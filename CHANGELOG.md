# Changelog

All notable changes to this project are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.0] - 2026-10-29

First numbered release. Nothing was tagged before this. The commits below
are the whole history of `main` through the actor work (28 October 2026),
plus the English docs and release metadata in this version.

`0.1.0` is a development version, not a 1.0. Lake treats `0.x.x` the same
way: a first official release has not been declared. The store builds and
`lake test` passes, and the README states which claims are theorems, which
are measurements, and which are out of scope. There is no network, no
election, and no proof that a pulled power cord matches the byte-prefix
model. That is why this is not `1.0.0`.

### Added

- Append-only record codec, crash-as-prefix recovery, range sharding, and a
  single-writer `DB` with file and memory backends. Tests, a `kill -9` demo,
  and CI (`lake build` and `lake test` on push).
- Power-loss barriers: `fdatasync` on Linux, `F_FULLFSYNC` then `fsync` on
  macOS, and a directory `fsync` after create or rename. Non-reflected
  CRC-32 (`sum32`) with a proved burst bound of 32 bits, and a proved
  odd-weight collision so not every corruption is detected.
- One writer per shard (`ShardSet`): no global mutex. `Directory`, `Locate`,
  and `Mailbox` are the seams a later network would fill. The model proves
  the routed id is `shardOf`, each shard keeps its own history, distinct
  shards commute, and the global iterate is the sorted merge of the snapshots.
- A written comparison of concurrent-writer designs A–F. The decision is B
  now and C only if one shard falls short. D and E are not implemented.
  See `docs/concurrency.md`.
- Tree index (`Std.TreeMap`) and a memory log that conses frames instead of
  copying the byte log on every append.
- Paginated ranges and collections: time-ordered `Ulid` ids and version
  compare-and-set. A prefix on `ShardSet` is the merge of per-shard snapshots.
- Per-shard job queue with lease, outbox in one batch, TTL sweep, and a
  change feed.
- Secondary indexes in the same batch as the document, and an annotated OCC
  validator inside one shard. That validator is obsolete; see below.
- Copy up to an LSN, compaction on a task, a schema-version key, and get /
  commit counters.
- Range and prefix walks from the tree's lower bound. The page is proved
  equal to the filtered page, and a merged page only needs that many rows
  from each local shard.
- Serializable transactions inside one shard (`ShardSet.transact` / `Tx`).
  The pure `TxRun` model is `applyBatch` on success and no map on abort.
- Copies and messages between shards, without a distributed transaction.
  `commitCross` writes the home shard and an outbox notice per destination.
  `propagate` applies each ticket once. `commit` stays strict.
- One actor per shard on the durable inbox. `spawn` drains the outbox inside
  `transact`, with a bounded wake channel. `send` is asynchronous. A handler
  that keeps failing lands on the dead-letter key.
- `Cairn.version` (`"0.1.0"`), this changelog, and `scripts/check_version.sh`.
  CI checks that the lakefile version, the top changelog entry, and
  `Cairn.version` are the same string.

### Changed

- Design notes that were in Spanish are in English, and the Spanish filenames
  were renamed (`docs/indice.md` to `docs/index.md`, `docs/copias.md` to
  `docs/copies.md`, and the same for actors, collections, concurrency,
  durability, and transactions). Technical claims and recorded numbers are
  unchanged.
- The MIT copyright line names Jairo Caro-Accino Viciana. Source files do
  not carry per-file license headers.
