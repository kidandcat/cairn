# Transacciones dentro de un shard

`ShardSet.transact` corre la función bajo el mutex del shard de la clave ancla. Toda lectura y escritura pasa por `Tx`: `get`, `range`, `prefix`, `put`, `delete`. Una lectura ve las escrituras pendientes de esa misma función. Al terminar hay un solo lote, o nada si la función lanza o toca una clave de otro shard.

La función mantiene el lock. Tiene que ser corta. No hagas E/S lenta dentro. Si el tramo pasa de `txWarnNs` (50 ms) se imprime un aviso y el lote se publica igual.

`occCommit` queda obsoleto. El read set anotado por el llamador puede omitir una lectura y admitir write skew. `Sec.put`, la cola y el outbox usan `transact`.

## Demostrado

En `TxRun`, un cuerpo es una lista de pasos.

- `run_ok_apply`: si el cuerpo termina, el mapa es `applyBatch` de sus ops sobre el mapa de partida.
- `run_abort` y `run_abort_after`: un `abort`, también después de escrituras del mismo cuerpo, no devuelve mapa.
- `read_own_write`: el put de un solo paso deja esa clave insertada.
- `compose`: dos cuerpos que terminan, en ese orden, son la concatenación de sus pasos.

Eso es la serializabilidad del modelo: un cuerpo, luego el otro, sobre un solo mapa. No es un teorema del mutex de C++ ni de dos `Task` entrelazadas. El aviso de los 50 ms tampoco está demostrado.

## Probado con tests

`lake test`: `cairn tests ok`, fuzz detect 1591, torn 89, miss 0, forge 0, same 0. Una transacción que escribe y lee esa clave ve su propio valor. Una que escribe y lanza deja la clave como estaba. Una clave de otro shard aborta y no publica el home. Dos y cuatro tareas hacen el write skew clásico (las dos leen las dos cuentas y cada una escribe la suya si ambas siguen en `ok`): nunca quedan las dos en `gone`. `counts.commits` sube con `transact` y con `modifyKey`.
