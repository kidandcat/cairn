# Índices secundarios y OCC dentro de un shard

Fase 3. El índice se escribe en el mismo lote que el documento. El commit optimista valida el read set. No es snapshot isolation.

## Restricción

`Sec.put` arma `put` del documento y un `put` por clave de índice. Si `sameShard` es falso, lanza `index crossed a shard` y no escribe nada. La clave de índice empieza por `05`, el nombre, el campo y el `Ulid`. El valor del índice es la clave del documento.

`occCommit` corre bajo el mutex de un shard. Si alguna lectura grabada ya no está, el lote no se publica. Si las escrituras cruzan de shard, lanza y tampoco publica. El read set lo pone el llamador. Una decisión que no anota una clave que leyó puede commitear un write skew. El validador no inventa lecturas.

## Demostrado

- `readsMatch_iff`: el read set coincide con el mapa exactamente cuando cada valor anotado sigue ahí.
- `readsMatch_miss`, `occ_conflict`: si la clave anotada cambió, el read set no coincide.

El lote que sí pasa usa el mismo `commit` que el resto: un registro, o el prefijo de un corte. No hay un teorema nuevo de serializabilidad del entrelazado de dos `Task`. Eso está solo en el test.

## Probado con tests

`lake test` terminó con `cairn tests ok` y el fuzz de siempre (detect 1591, torn 89, miss 0, forge 0, same 0). El caso nuevo: un commit que leyó `k1=a` escribe `k2`; después de cambiar `k1`, el mismo read set no escribe. El índice `by-name/ada` apunta a la clave del documento. Un bound que separa el documento del índice rechaza el lote y deja la clave ausente.
