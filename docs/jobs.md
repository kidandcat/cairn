# Jobs, TTL, and change feed

Phase 2 report. The queue is persistent. The outbox is a single batch. The feed is one shard's log.

## Constraint

`Queue.enqueueWith` puts the caller's ops and the job's `put` in the same batch. If `sameShard` is false, it throws `outbox crossed a shard` and publishes nothing. With a single shard it always fits. With bounds, the job key (prefix `03`) and the change key have to fall on the same id. There is no transaction across shards.

The TTL index is key order under the prefix `04` (expiry in big-endian, then the id). `Ttl.sweep` deletes those whose expiry is `≤ now` and stops at the first later one. `claim` and `sweep` ask the shard's `prefix` for pages of 32. From the tree's lower bound, each page is the cut of `prefixWalk`, not a filter of the whole queue. `Job.claim_spec` and `Job.claim_blocks` remain the pure model of the row, not of the tree.

`ShardSet.watch shard fromLsn prefix` reads that shard's log. The order is that shard's admission order. There is no order across shards.

`nack` retries with `Job.backoff` (a power of two, cap 65536) and, past the maximum number of attempts, marks the job dead. The cron in this phase is an interval: the caller enqueues again with `runAt = now + every`. It is not a calendar expression.

## Proved

- `Job.claim_spec`: given the state, the claim is the row `pick` chooses and the lease `now + leaseFor`.
- `Job.claim_blocks`: a second `pick` before that lease expires does not return the same id.
- `Job.enqueue_idem`: if the idempotency key is already present, another job is not added.
- `Job.ack_gone`: ack removes that id.
- `outbox_both`: after the batch of two `put`s, both keys are present.
- `Feed.visible_mem`, `visible_since`, `visible_prefix`: the feed is exactly the log ops with `lsn ≥ from` and the prefix.
- `Job.due_mem`: a TTL row is due exactly when `expiry ≤ now`.

Not proved: that two `Task`s do not claim the same job. The model is sequential. The runtime uses compare-and-set of the value. A bound on the sweep is not proved either.

## Tested

`lake test` covers the lease (it is not handed out again before time, and it is after), the outbox that crosses a bound and writes nothing, the feed from a later LSN, the sweep of one of two expiries, and four tasks claiming eight jobs without repetition. The fuzz is still detect 1591, torn 89, miss 0, forge 0, same 0.

`scripts/crash_demo.sh` printed `recovered 140 keys, a prefix of the committed writes`. `cairn-backend` printed `backend demo ok`.

`cairn-design-bench`, same machine (4 vCPU, Xeon 2400 MHz, ext4 `/dev/vdc`), three repetitions, not averaged. `mem-claim-100` enqueues 100 jobs outside the clock and then claims them:

```
mem-claim-100 ops=100  178963ns/op 5587ops/s  181739ns/op 5502ops/s  179097ns/op 5583ops/s
```

About 0.18 ms per claim: each one walks the prefix again. `mem-prefix-pages` on the same run: 1006, 883, and 917 ns/op.
