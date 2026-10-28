# Copia, compactación, esquema y métricas

Fase 4. La copia de un shard es el prefijo del log hasta un LSN. La compactación corre en una tarea. La versión de esquema es una clave. Los contadores viven en el `ShardSet`.

## Qué hace

`upTo n` recorre el log cronológico y se detiene en el primer registro con `lsn > n`. `upTo_is_prefix` dice que eso es `take k` para algún `k`. Los LSN de cairn crecen de uno en uno, así que ese corte es el estado hasta `n`. `DB.backupFile` lo escribe con `writeDurable` (el mismo `fdatasync` y el fsync del directorio que una compactación). Restaurar es `openFile` de esa imagen.

`DB.compactAsync` lanza `DB.compact` en una tarea. Sigue siendo el mismo escritor: el mutex del shard serializa la compactación con los commits.

`migrate` lee la clave `schemaKey` (`[0]`) y, si la versión guardada es menor, escribe el paso y la versión nueva en un lote. Si ese lote cruza de shard, lanza y no publica. `schema_visible` es `get_after_put` de esa clave.

`ShardSet.counts` devuelve lecturas, commits locales y los nanos del último commit. No es un histograma. `ShardSet.commit`, `ShardSet.transact` y `ShardSet.modifyKey` incrementan `commits` y graban `lastCommitNs` al volver. Un `transact` que no escribe también cuenta: sostuvo el mutex. Un commit remoto no pasa por ese contador.

## Demostrado

`upTo_is_prefix` y `schema_visible`. El resto de la durabilidad sigue siendo `recovery_prefix` y `recovery_keeps_synced` sobre la imagen escrita.

## Probado con tests

`lake test`: `cairn tests ok`, fuzz detect 1591, torn 89, miss 0, forge 0, same 0. El caso nuevo abre un fichero, copia hasta el segundo registro, reabre la copia (están `a` y `b`, no `c`), compacta en una tarea y `b` sigue, migra a la versión 2 y los contadores de un `put` y un `get` suben. `scripts/crash_demo.sh`: `recovered 144 keys, a prefix of the committed writes`.

`cairn-design-bench` con los contadores puestos, misma máquina, tres repeticiones. Memoria de un shard: 49271, 38709 y 36317 ns/op. Fichero de un shard: 182679, 151965 y 159001 ns/op. Sigue en la banda del `fdatasync` y del árbol; el contador no se ve al lado de eso.
