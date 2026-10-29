# Transactions inside one shard

`ShardSet.transact` runs the function under the mutex of the anchor key's shard. Every read and write goes through `Tx`: `get`, `range`, `prefix`, `put`, `delete`. A read sees the pending writes of that same function. At the end there is a single batch, or nothing if the function throws or touches a key on another shard.

The function holds the lock. It has to be short. Do not do slow I/O inside it. If the stretch passes `txWarnNs` (50 ms) a warning is printed and the batch is published anyway.

`occCommit` is obsolete. The read set annotated by the caller can omit a read and admit write skew. `Sec.put`, the queue, and the outbox use `transact`.

## Proved

In `TxRun`, a body is a list of steps.

- `run_ok_apply`: if the body finishes, the map is `applyBatch` of its ops on the starting map.
- `run_abort` and `run_abort_after`: an `abort`, including after writes in the same body, returns no map.
- `read_own_write`: the put of a single step leaves that key inserted.
- `compose`: two bodies that finish, in that order, are the concatenation of their steps.

That is serializability of the model: one body, then the other, on a single map. It is not a theorem about the C++ mutex or about two interleaved `Task`s. The 50 ms warning is not proved either.

## Tested

`lake test`: `cairn tests ok`, fuzz detect 1591, torn 89, miss 0, forge 0, same 0. A transaction that writes and reads that key sees its own value. One that writes and throws leaves the key as it was. A key on another shard aborts and does not publish the home. Two and four tasks do the classic write skew (both read both accounts and each writes its own if both are still `ok`): the two never both end as `gone`. `counts.commits` goes up with `transact` and with `modifyKey`.
