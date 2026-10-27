# Un escritor por shard

Informe de la rama `cursor/shard-writer-35e9`. Es la fase 1 de la comparación de concurrencia: el diseño B. Cada shard es un `DB` con su mutex, su fichero y su `Hist`. No hay mutex global. C (OCC dentro de un shard) queda para cuando un solo shard no dé abasto.

## Qué hace la capa

`ShardSet` posee un `DB` opcional por id. `get`, `put`, `delete`, `commit` y `commitMany` calculan `shardOf` y entran solo en el mutex de ese `DB`. Un lote con claves de dos shards se rechaza. `iterate` lee una foto por shard y las mezcla en orden de clave (`mergeAll`). Esa mezcla no es una foto global: un commit puede caer en el shard 1 entre la lectura del 0 y la del 1. No hay un orden serial entre shards.

La costura de clúster, sin red:

- `HostId` es el proceso. `ShardHost` es la lista de shards que aloja (`Directory.hostView`).
- `Directory` es el mapa versionado shard → dueño (`ShardOwner`: host líder, `NodeId` del líder, seguidores). `publish` / `reassign` sube la generación y no mueve bytes.
- `Locate` dice `here`, `remote` o `missing`. Lo remoto llama a `ShardSet.remote`. Por defecto lanza `remote shard`. `serve` es lo que un handler de socket llamaría.
- `Mailbox` es `send`/`drain`. `InProc.mailbox` es el buzón que ya había. `planCatchup` elige `appendEntries` o `installSnapshot` igual que `catchUp`, y `pushLog` lo manda. El seguidor aplica con `DB.follow`. La longitud del seguidor la pasa el llamador: un latido futuro la traería.

Los ficheros son `dir/shard-<id>.cairn`. Un corte de un fichero no reescribe los demás.

## Qué está demostrado

Reutilizado: `key_one_shard`, `state_eq_serial`, `decodeFile_prefix` / `recovery_prefix`.

Añadido, en Lean, sin `sorry` ni `axiom` declarado:

- `route_is_shardOf`: el id de un lote de un solo shard es `shardOf` de su clave.
- `step_home`, `step_other`, `shard_hist_serial`: el paso escribe el `Hist` de ese shard y ningún otro, y el estado es el pliegue serial de sus propios commits.
- `steps_commute`: dos escrituras en shards distintos conmutan. No hay un orden global que recuperar.
- `clusterEntries_sorted`, `clusterEntries_mem`, `cluster_partition`: el merge ordenado contiene exactamente las entradas de las partes, y partir un mapa con `inShard` y volver a mezclarlo devuelve esas entradas. El teorema habla de las fotos que se le pasan, no de un instante común.
- `crash_shard_independent` y `crash_others`: el prefijo de bytes de un shard es un prefijo de sus registros; el resto de ids no cambia.
- `reassign_gen`, `reassign_owner`, `locate_here`, `locate_remote`, `plan_agrees`.

No está demostrado que dos `Task` avancen a la vez, ni que el mutex de C++ no deje entrar a dos secciones, ni nada de un socket.

## Qué solo está probado con tests

`lake test` terminó con `cairn tests ok` (el fuzz de siempre: detect 1591, torn 89, miss 0, forge 0). Además:

- El id que elige `ShardSet` coincide con `shardOf`. El lote cruzado y el vacío fallan. El log de cada shard, al rehacerlo, no contiene las claves del otro.
- `iterate` es igual a `mergeAll` de las fotos por shard, y sale ordenado.
- Dos hosts en memoria: el put de una clave del otro host pasa por `remote`/`serve` y aparece en los dos lados. `iterate` mezcla las dos fotos.
- `pushLog` de un shard vacío de seguidor manda un mensaje; `DB.follow` deja la clave. Un epoch distinto no manda nada.
- Cuatro tareas de escritura (una por shard, lotes de dos claves) y dos lectoras. Cada foto de un shard tiene el par entero o no lo tiene. Al final, 40 entradas por shard e `iterate` igual al merge.
- Ficheros: dos tareas, un shard cada una. Tras cerrar, se corta `shard-0.cairn` al header de 4096 bytes. Al reabrir, las claves del shard 0 no están y las del shard 1 siguen.

## Números

Una pasada de `cairn-design-bench`, tres repeticiones, 4 vCPU, `Intel(R) Xeon(R) Processor` a 2400 MHz, ext4 en `/dev/vdc`. El reloj no incluye el `open`. Cada put de fichero hace un `fdatasync`.

```
file-shards-1 ops=100  224989ns/op 4444ops/s  156568ns/op 6387ops/s  163593ns/op 6112ops/s
file-shards-2 ops=200  127894ns/op 7818ops/s  103404ns/op 9670ops/s  93035ns/op 10748ops/s
file-shards-4 ops=400  56760ns/op 17618ops/s  53457ns/op 18706ops/s  61310ns/op 16310ops/s
mem-shards-1 ops=100  5482020ns/op 182ops/s  5406456ns/op 184ops/s  5383518ns/op 185ops/s
mem-shards-2 ops=200  2725123ns/op 366ops/s  2713650ns/op 368ops/s  2726411ns/op 366ops/s
mem-shards-4 ops=400  1428210ns/op 700ops/s  1440656ns/op 694ops/s  1428952ns/op 699ops/s
file-group-32-shards-4 ops=512  6425ns/op 155642ops/s  5400ns/op 185185ops/s  5601ns/op 178539ops/s
file-contended-1-tasks-4 ops=400  209802ns/op 4766ops/s  181693ns/op 5503ops/s  208523ns/op 4795ops/s
```

En fichero, 4 shards hicieron unas tres veces el ritmo de 1 shard (unos 16–19k ops/s frente a unos 4.4–6.4k). 2 shards queda en medio. Cuatro tareas sobre un solo shard se quedan en el ritmo de un shard: el mutex no paraleliza dentro. El group commit de 32, con 4 shards, baja a unos 5–6 µs por put porque la barrera se paga una vez por segmento.

Las filas de memoria escalan igual (el doble, luego el cuádruple) pero el absoluto es el backend de memoria copiando la trama de 4096 bytes en cada append. No miden el router a solas y no son un disco.

## Qué falta para el clúster

Red (codec de `ShardReq` y `Rpc`, y un transporte detrás de `Mailbox` y `remote`), un protocolo de membresía que llame a `publish` después de `adopt`, y consenso o quórum si un shard tiene que sobrevivir a la caída del líder. Esta fase es copia primario/secundario: el líder gana. Varios escritores del mismo shard siguen fuera.
