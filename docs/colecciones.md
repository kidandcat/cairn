# Rangos y colecciones

Informe de la fase 1. Un `range` o un `prefix` es una página ordenada. Una colección es un prefijo de claves, con id ordenable en el tiempo y compare-and-set de versión.

## Cómo está hecho

`rangeHits` y `prefixHits` filtran `entries`. `lo` es inclusivo, `hi` es exclusivo, `after` es un cursor estricto. La página es el `take` de esa lista. `pageCursor` es la última clave si la página llenó el límite.

En un `DB` eso es una foto. En `ShardSet` cada shard aporta su foto, se mezclan con `mergeAll` y entonces se corta la página. Un prefijo puede cruzar shards. No hay foto global: un commit puede caer entre la lectura de un shard y la del siguiente.

El recorrido filtra la lista de entradas. No es un descenso al primer clave del árbol. Con 1000 claves salió a cerca de 1 µs por clave.

La clave de un documento es `01`, la longitud `UInt32` del nombre, el nombre, `02`, y 16 bytes de `Ulid`. El orden de bytes del id es el orden del tiempo. `IdGen` usa un `Clock` inyectable. El valor es versión `UInt64` más un `Val` (`bytes`, `str` o `nat`). `collUpdate` y `collDelete` leen y escriben bajo el mutex del shard de esa clave. Si la versión no coincide, no hay escritura. La versión no da la vuelta. Un documento es una clave, así que cae en un solo shard. Escribir una colección en un shard remoto lanza `remote shard`.

## Qué está demostrado

Sin `sorry`. Los axiomas siguen siendo los del núcleo (`propext`, `Quot.sound`, y `Classical.choice` donde entra `omega`).

- `rangeHits_mem`, `prefixHits_mem`: la entrada está en el resultado exactamente si está en el mapa y cae en el intervalo.
- `rangeHits_sorted`, `prefixHits_sorted`, `rangeHits_nodup`, `prefixHits_nodup`, y lo mismo para la página: ordenadas y sin claves repetidas.
- `resume_hits`, `resume_prefix`: la página siguiente, con el cursor, es la cola de esa lista.
- `mergedHits_mem`: en la mezcla, una entrada está si algún shard la tenía y cumplía el predicado.
- `Ulid.encode_lt_of_lt`: si el tiempo o el azar es menor, los bytes lo son.
- `Ulid.fresh_increases`, `Ulid.bump_lt`: el paso puro no repite un id anterior.
- `resolve_insert_fresh`, `resolve_insert_taken`, `resolve_update_ok`, `resolve_update_conflict`, `resolve_update_missing`, `resolve_delete_ok`, `resolve_delete_conflict`, `resolve_delete_missing`.
- `decodeDoc_encode`, `decode_encode_bytes`, `decode_encode_nat`.

No está demostrado que el `IO.Ref` publique el `View` de forma atómica, ni una cota del recorrido.

## Qué solo está probado con tests

`lake test` terminó con `cairn tests ok` y el fuzz de siempre:

```
fuzz [(detect, 1591), (torn, 89), (miss, 0), (forge, 0), (same, 0)]
```

Ahí entran el rango (`b` inclusivo, `d` exclusivo, página de 2 y el resto, prefijo `a`), la colección cruzando dos shards (tiempos 1 y 5000, orden de lista, conflicto de versión, borrado), y el reloj contador. `scripts/crash_demo.sh` imprimió `recovered 135 keys, a prefix of the committed writes`. `cairn-backend` imprimió `backend demo ok`.

## Números

Misma máquina: 4 vCPU, Intel Xeon a 2400 MHz, ext4 en `/dev/vdc`. `cairn-design-bench`, tres repeticiones, sin promediar. Las filas de shards siguen en la banda de después del árbol (fichero de un shard unas 0.16–0.18 ms/op, memoria de un shard unas 42–50 µs/op). La fila nueva es el recorrido:

```
mem-prefix-pages ops=1000  1131ns/op 884173ops/s  1012ns/op 988142ops/s  931ns/op 1074113ops/s
```

Mil claves, páginas de 40, el `put` fuera del reloj. Cerca de 1 µs por clave. Es el filtro de la lista, no un lower bound del árbol.
