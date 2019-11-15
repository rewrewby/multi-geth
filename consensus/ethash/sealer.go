// Copyright 2017 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package ethash

import (
	"bytes"
	crand "crypto/rand"
	"encoding/json"
	"errors"
	"math"
	"math/big"
	"math/rand"
	"net/http"
	"runtime"
	"sync"
	"time"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/rlp"
)

const (
	// staleThreshold is the maximum depth of the acceptable stale but valid ethash solution.
	staleThreshold = 7
)

var (
	errNoMiningWork      = errors.New("no mining work available yet")
	errInvalidSealResult = errors.New("invalid or stale proof-of-work solution")
)

// Seal implements consensus.Engine, attempting to find a nonce that satisfies
// the block's difficulty requirements.
func (ethash *Ethash) Seal(chain consensus.ChainReader, block *types.Block, results chan<- types.SealResult, stop <-chan struct{}) error {
	// If we're running a fake PoW, simply return a 0 nonce immediately
	if ethash.config.PowMode == ModeFake || ethash.config.PowMode == ModeFullFake {
		header := block.Header()
		header.Nonce, header.MixDigest = types.BlockNonce{}, common.Hash{}
		select {
		case results <- types.SealResult{Block: block.WithSeal(header)}:
		default:
			log.Warn("Sealing result is not read by miner", "mode", "fake", "sealhash", ethash.SealHash(block.Header()))
		}
		return nil
	}
	// If we're running a shared PoW, delegate sealing to it
	if ethash.shared != nil {
		return ethash.shared.Seal(chain, block, results, stop)
	}
	// Create a runner and the multiple search threads it directs
	abort := make(chan struct{})

	ethash.lock.Lock()
	threads := ethash.threads
	if ethash.rand == nil {
		seed, err := crand.Int(crand.Reader, big.NewInt(math.MaxInt64))
		if err != nil {
			ethash.lock.Unlock()
			return err
		}
		ethash.rand = rand.New(rand.NewSource(seed.Int64()))
	}
	ethash.lock.Unlock()
	if threads == 0 {
		threads = runtime.NumCPU()
	}
	if threads < 0 {
		threads = 0 // Allows disabling local mining without extra logic around local/remote
	}
	// Push new work to remote sealer
	if ethash.workCh != nil {
		ethash.workCh <- &sealTask{block: block, results: results}
	}
	var (
		pend   sync.WaitGroup
		locals = make(chan *types.Block)
	)
	for i := 0; i < threads; i++ {
		pend.Add(1)
		go func(id int, nonce uint64) {
			defer pend.Done()
			ethash.mine(block, id, nonce, abort, locals)
		}(i, uint64(ethash.rand.Int63()))
	}
	// Wait until sealing is terminated or a nonce is found
	go func() {
		var result *types.Block
		select {
		case <-stop:
			// Outside abort, stop all miner threads
			close(abort)
		case result = <-locals:
			// One of the threads found a block, abort all others
			select {
			case results <- types.SealResult{Block: result}:
			default:
				log.Warn("Sealing result is not read by miner", "mode", "local", "sealhash", ethash.SealHash(block.Header()))
			}
			close(abort)
		case <-ethash.update:
			// Thread count was changed on user request, restart
			close(abort)
			if err := ethash.Seal(chain, block, results, stop); err != nil {
				log.Error("Failed to restart sealing after update", "err", err)
			}
		}
		// Wait for all miners to terminate and return the block
		pend.Wait()
	}()
	return nil
}

// mine is the actual proof-of-work miner that searches for a nonce starting from
// seed that results in correct final block difficulty.
func (ethash *Ethash) mine(block *types.Block, id int, seed uint64, abort chan struct{}, found chan *types.Block) {
	// Extract some data from the header
	var (
		header  = block.Header()
		hash    = ethash.SealHash(header).Bytes()
		target  = new(big.Int).Div(two256, header.Difficulty)
		number  = header.Number.Uint64()
		dataset = ethash.dataset(number, false)
	)
	// Start generating random nonces until we abort or find a good one
	var (
		attempts = int64(0)
		nonce    = seed
	)
	logger := log.New("miner", id)
	logger.Trace("Started ethash search for new nonces", "seed", seed)
search:
	for {
		select {
		case <-abort:
			// Mining terminated, update stats and abort
			logger.Trace("Ethash nonce search aborted", "attempts", nonce-seed)
			ethash.hashrate.Mark(attempts)
			break search

		default:
			// We don't have to update hash rate on every nonce, so update after after 2^X nonces
			attempts++
			if (attempts % (1 << 15)) == 0 {
				ethash.hashrate.Mark(attempts)
				attempts = 0
			}
			// Compute the PoW value of this nonce
			digest, result := hashimotoFull(dataset.dataset, hash, nonce)
			if new(big.Int).SetBytes(result).Cmp(target) <= 0 {
				// Correct nonce found, create a new header with it
				header = types.CopyHeader(header)
				header.Nonce = types.EncodeNonce(nonce)
				header.MixDigest = common.BytesToHash(digest)

				// Seal and return a block (if still needed)
				select {
				case found <- block.WithSeal(header):
					logger.Trace("Ethash nonce found and reported", "attempts", nonce-seed, "nonce", nonce)
				case <-abort:
					logger.Trace("Ethash nonce found but discarded", "attempts", nonce-seed, "nonce", nonce)
				}
				break search
			}
			nonce++
		}
	}
	// Datasets are unmapped in a finalizer. Ensure that the dataset stays live
	// during sealing so it's not unmapped while being read.
	runtime.KeepAlive(dataset)
}

// remote is a standalone goroutine to handle remote mining related stuff.
func (ethash *Ethash) remote(notify []string, noverify bool) {
	var (
		works = make(map[common.Hash]*types.Block)
		rates = make(map[common.Hash]hashrate)

		results      chan<- types.SealResult
		currentBlock *types.Block
		currentWork  [10]string

		notifyTransport = &http.Transport{}
		notifyClient    = &http.Client{
			Transport: notifyTransport,
			Timeout:   time.Second,
		}
		notifyReqs = make([]*http.Request, len(notify))
	)
	// notifyWork notifies all the specified mining endpoints of the availability of
	// new work to be processed.
	notifyWork := func() {
		work := currentWork
		blob, _ := json.Marshal(work)

		for i, url := range notify {
			// Terminate any previously pending request and create the new work
			if notifyReqs[i] != nil {
				notifyTransport.CancelRequest(notifyReqs[i])
			}
			notifyReqs[i], _ = http.NewRequest("POST", url, bytes.NewReader(blob))
			notifyReqs[i].Header.Set("Content-Type", "application/json")

			// Push the new work concurrently to all the remote nodes
			go func(req *http.Request, url string) {
				res, err := notifyClient.Do(req)
				if err != nil {
					log.Warn("Failed to notify remote miner", "err", err)
				} else {
					log.Trace("Notified remote miner", "miner", url, "hash", log.Lazy{Fn: func() common.Hash { return common.HexToHash(work[0]) }}, "target", work[2])
					res.Body.Close()
				}
			}(notifyReqs[i], url)
		}
	}
	// makeWork creates a work package for external miner.
	//
	// The work package consists of 3 strings:
	//   result[0], 32 bytes hex encoded current block header pow-hash
	//   result[1], 32 bytes hex encoded seed hash used for DAG
	//   result[2], 32 bytes hex encoded boundary condition ("target"), 2^256/difficulty
	//   result[3], hex encoded block number
	//   result[4], 32 bytes hex encoded parent block header pow-hash
	//   result[5], hex encoded gas limit
	//   result[6], hex encoded gas used
	//   result[7], hex encoded transaction count
	//   result[8], hex encoded uncle count
	makeWork := func(block *types.Block) {
		header := block.Header()
		hash := ethash.SealHash(header)

		currentWork[0] = hash.Hex()
		currentWork[1] = common.BytesToHash(SeedHash(block.NumberU64())).Hex()
		currentWork[2] = common.BytesToHash(new(big.Int).Div(two256, block.Difficulty()).Bytes()).Hex()
		currentWork[3] = hexutil.EncodeBig(block.Number())
		currentWork[4] = block.ParentHash().Hex()
		currentWork[5] = hexutil.EncodeUint64(block.GasLimit())
		currentWork[6] = hexutil.EncodeUint64(block.GasUsed())
		currentWork[7] = hexutil.EncodeUint64(uint64(len(block.Transactions())))
		currentWork[8] = hexutil.EncodeUint64(uint64(len(block.Uncles())))

		extra := append(header.Extra, make([]byte, 4)...)
		encoded, err := rlp.EncodeToBytes([]interface{}{
			header.ParentHash,
			header.UncleHash,
			header.Coinbase,
			header.Root,
			header.TxHash,
			header.ReceiptHash,
			header.Bloom,
			header.Difficulty,
			header.Number,
			header.GasLimit,
			header.GasUsed,
			header.Time,
			extra,
		})
		if err == nil {
			currentWork[9] = hexutil.Encode(encoded)
		}

		// Trace the seal work fetched by remote sealer.
		currentBlock = block
		works[hash] = block
	}
	// submitWork verifies the submitted pow solution, returning
	// its block hash when success or an error when failed.
	submitWork := func(nonce types.BlockNonce, mixDigest common.Hash, sealhash common.Hash, extraNonce []byte) (blockHash common.Hash, err error) {
		if currentBlock == nil {
			err = errors.New("Pending work without block")
			log.Error(err.Error(), "sealhash", sealhash)
			return
		}
		// Make sure the work submitted is present
		block := works[sealhash]
		if block == nil {
			err = errors.New("Work submitted but none pending")
			log.Warn(err.Error(), "sealhash", sealhash, "curnumber", currentBlock.NumberU64())
			return
		}
		// Verify the correctness of submitted result.
		header := block.Header()
		header.Nonce = nonce
		header.MixDigest = mixDigest
		header.Extra = append(header.Extra, extraNonce...)

		start := time.Now()
		if !noverify {
			if ethashErr := ethash.verifySeal(nil, header, true); ethashErr != nil {
				err = errors.New("Invalid proof-of-work submitted")
				log.Warn(err.Error(), "sealhash", sealhash, "elapsed", common.PrettyDuration(time.Since(start)), "err", ethashErr)
				return
			}
		}
		// Make sure the result channel is assigned.
		if results == nil {
			err = errors.New("Ethash result channel is empty, submitted mining result is rejected")
			log.Warn(err.Error())
			return
		}
		log.Trace("Verified correct proof-of-work", "sealhash", sealhash, "elapsed", common.PrettyDuration(time.Since(start)))

		// Solutions seems to be valid, return to the miner and notify acceptance.
		solution := block.WithSeal(header)
		result := types.SealResult{
			Block:    solution,
			SealHash: &sealhash,
		}

		// The submitted solution is within the scope of acceptance.
		if solution.NumberU64()+staleThreshold > currentBlock.NumberU64() {
			select {
			case results <- result:
				blockHash = solution.Hash()
				log.Debug("Work submitted is acceptable", "number", solution.NumberU64(), "sealhash", sealhash, "hash", blockHash)
				return
			default:
				err = errors.New("Sealing result is not read by miner")
				log.Warn(err.Error(), "mode", "remote", "sealhash", sealhash)
				return
			}
		}
		// The submitted block is too old to accept, drop it.
		err = errors.New("Work submitted is too old")
		log.Warn(err.Error(), "number", solution.NumberU64(), "sealhash", sealhash, "hash", solution.Hash())
		return
	}

	ticker := time.NewTicker(5 * time.Second)
	defer ticker.Stop()

	for {
		select {
		case work := <-ethash.workCh:
			// Update current work with new received block.
			// Note same work can be past twice, happens when changing CPU threads.
			results = work.results

			makeWork(work.block)

			// Notify and requested URLs of the new work availability
			notifyWork()

		case work := <-ethash.fetchWorkCh:
			// Return current mining work to remote miner.
			if currentBlock == nil {
				work.errc <- errNoMiningWork
			} else {
				work.res <- currentWork
			}

		case result := <-ethash.submitWorkCh:
			// Verify submitted PoW solution based on maintained mining blocks.
			blockHash, err := submitWork(result.nonce, result.mixDigest, result.hash, result.extraNonce)
			if err == nil {
				result.blockHashCh <- blockHash
			} else {
				result.errorCh <- err
			}

		case result := <-ethash.submitRateCh:
			// Trace remote sealer's hash rate by submitted value.
			rates[result.id] = hashrate{rate: result.rate, ping: time.Now()}
			close(result.done)

		case req := <-ethash.fetchRateCh:
			// Gather all hash rate submitted by remote sealer.
			var total uint64
			for _, rate := range rates {
				// this could overflow
				total += rate.rate
			}
			req <- total

		case <-ticker.C:
			// Clear stale submitted hash rate.
			for id, rate := range rates {
				if time.Since(rate.ping) > 10*time.Second {
					delete(rates, id)
				}
			}
			// Clear stale pending blocks
			if currentBlock != nil {
				for hash, block := range works {
					if block.NumberU64()+staleThreshold <= currentBlock.NumberU64() {
						delete(works, hash)
					}
				}
			}

		case errc := <-ethash.exitCh:
			// Exit remote loop if ethash is closed and return relevant error.
			errc <- nil
			log.Trace("Ethash remote sealer is exiting")
			return
		}
	}
}
