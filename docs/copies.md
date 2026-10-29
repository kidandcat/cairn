# Copies and messages between shards

This is not a transaction across shards. There is no 2PC and no consensus.

A key has an owner shard: the one from `shardOf`. The write that counts is the one on that home, inside `transact`. The same batch leaves outbox notices, one per destination shard. The destination applies them later, in ticket order (home LSN and index inside the batch). If the process dies between the home commit and the propagator, the outbox is still in the home's file and the destination's progress mark has not advanced: on resume it is applied that once, and a second pass does not repeat it.

## What a reader sees

`ShardSet.get` reads the home. It is up to date for that shard.

`readCopy home dest key` reads the destination's file. It can lag. It returns the value, the applied ticket, and the home's `nextLsn` (`homeTip`). If `applied` lags the tickets the home has already written, the copy is stale. Two reads, one of the home and one of the copy, can disagree. Two copies can disagree with each other until both propagators reach the same ticket. There is no global snapshot.

The outbox and the progress mark are stored with `Tx.putLocal` in the file of the shard that runs the batch. `shardOf` does not route them. The propagator reads that file with `localPrefix` and `localGet`.

## Messages and sagas

`Tx.enqueue dest notice` puts a message in the outbox of the shard that holds the lock. The destination receives it in `propagate`, inside its own `transact`, once per ticket. It is at-least-once in the sense that a crash retries; the mark makes the effect apply once.

A transfer from account `a` (shard 0) to `z` (shard 1): `a` is debited and the credit is enqueued. If `z` is frozen, the handler does not credit and enqueues the compensation; the propagator on the way back returns the amount to `a`. If the credit does land, a second `propagate` does not add it again.

## `commitCross`

`commit` still rejects a batch that crosses shards. `commitCross` splits the batch: the home's ops are written there, and the rest goes out as notices. The result is `.local` or `.eventual home destinations`. `.eventual` is not atomic: the destination may not have applied anything yet. `commitCross ops true` is the strict mode and throws `cross-shard batch` without writing.

## Proved

- `applyTicket_idem`: the same ticket twice equals once.
- `numbered_fold`: tickets `start, start+1, …` reapply the ops in that order and the mark ends on the last one.
- `converge`: if the copy starts empty and applies those tickets, it matches `applyBatch` of the home log.

Not proved: the mutex, that two tasks do not step on each other outside the model, or that `readCopy` is within one ticket of home. The lag is a number the read returns, not a bound.

## Tested

`lake test`: `cairn tests ok`, fuzz detect 1591, torn 89, miss 0, forge 0, same 0. The process is closed after the home commit and before propagate, the file is reopened, the copy arrives, and a second pass applies 0. Four tasks propagate the same outbox and the copy ends at the home's value. The frozen saga compensates; the free saga credits once. `scripts/crash_demo.sh`: `recovered 156 keys, a prefix of the committed writes`. `cairn-backend`: `backend demo ok`.

`cairn-copy-bench`, memory, the fill of 1000 `commitCross` outside the clock, three repetitions of `propagate`, total nanoseconds, not averaged. 4 vCPU, Xeon 2400 MHz, ext4 `/dev/vdc`:

```
propagate n=1000  58276448ns  36116345ns  23830012ns
```
