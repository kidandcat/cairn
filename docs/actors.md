# Actors, one per shard

This is not an actor runtime, and not one actor per entity. Each shard, if `Actor.spawn` is called, has a loop and a bounded mailbox (`Std.Channel`, capacity `cap`). The durable mailbox is the copy outbox: `propagate` applies a notice inside a `transact` and stores the progress mark in that same batch.

## Why there is no synchronous call

`ShardSet.send dst msg` returns when the notice is in the source log and, if the destination actor exists, when the in-memory mailbox accepts a wake-up. It does not wait for the effect. A reply is another `send` back. If the sender waited inside its turn, and the destination were waiting on the sender, the two loops would stall. That is why there is no synchronous request between actors.

## Reads

Reads do not enter the queue. `ShardSet.get` is still a `Ref.get` of an immutable snapshot.

## Failures

If the handler throws, the batch is not published and the mark does not advance. The loop records it, sleeps `attempts * 2` milliseconds, and reads the log again. After `maxAttempts` failures, the head notice is copied to a dead-letter key (`deadKey`) and the mark steps past it. A poison message does not stall the shard.

`Actor.spawn shard handler` starts that loop. The copy propagator and the saga are the same `propagate`: the actor's handler is the saga's handler.

## Proved

- `ActorModel.process_one`: processing one message is `applyOp`, a batch of one op.
- `ActorModel.process_fold`: the mailbox in order is the fold of those batches.
- `CopyModel.applyTicket_idem`, `numbered_fold`, `converge`: idempotence, order by source, and a copy that catches up to home, which this loop reuses.

Not proved: the `Channel`, the backoff, or that `kill -9` cuts only a prefix. That is the same file model as the rest of cairn.

## Tested

`lake test`: `cairn tests ok`, fuzz detect 1591, torn 89, miss 0, forge 0, same 0. The capacity-1 mailbox rejects the third `trySend`, and a blocked `send` continues when a slot frees. Three messages from one source stay in order `[0,1,2]`. A handler that throws twice and writes on the third try does write. A poison message goes to the dead-letter queue and the next message is applied. Four tasks send at once and the 20 keys appear once each. Closing the file and reopening it does not reapply. `Demo/Backend` sends a ping and reads the pong with `get`. `scripts/actor_crash.sh` printed `actor recovered 40 notices, applied once` after `kill -9`.

`cairn-actor-bench`, memory, 1000 notices written outside the clock, three drains, total nanoseconds, not averaged. 4 vCPU, Xeon 2400 MHz, ext4 `/dev/vdc`:

```
actor-drain n=1000  30174778ns  23558303ns  23487820ns
```
