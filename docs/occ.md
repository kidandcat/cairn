# OCC anotado

Obsoleto. El read set que anota el llamador puede olvidar una clave y admitir write skew. El camino actual es `ShardSet.transact` con `Tx`. Está en [transacciones.md](transacciones.md).

Los lemas `readsMatch_iff`, `readsMatch_miss` y `occ_conflict` siguen en `Cairn/Occ.lean`: describen el validador viejo, no el mutex.
