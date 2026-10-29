# Annotated OCC

Obsolete. The read set the caller annotates can forget a key and admit write skew. The current path is `ShardSet.transact` with `Tx`. It is in [transactions.md](transactions.md).

The lemmas `readsMatch_iff`, `readsMatch_miss`, and `occ_conflict` remain in `Cairn/Occ.lean`: they describe the old validator, not the mutex.
