# Índice en árbol y log que no se copia

Informe del cambio de un solo shard. El índice deja de ser una lista asociativa. El backend de memoria deja de copiar el log de bytes en cada `append`, y el `View` deja de hacer `v.log ++ [record]`. Sigue habiendo un escritor por shard. El `View` se publica con `IO.Ref.set` y se lee con `IO.Ref.get`.

## Qué cambió

El mapa es `Std.TreeMap` con el comparador de los bytes de la clave. La biblioteca mantiene un árbol balanceado por tamaño (delta 3, ratio 2). `get` es `TreeMap.get?`. `insert` y `erase` devuelven otra raíz y comparten las ramas que no tocan. Un lector que ya hizo `Ref.get` se queda con el árbol anterior.

`entries` es el inorden: orden lexicográfico de la clave, cada clave una vez. La compactación emite un `put` por clave viva y, al rehacerlo, recupera esas entradas. Dos árboles con las mismas entradas no tienen por qué tener la misma forma, así que `compact_eq`, `compact_roundtrip`, `move_replays` y `moved_state` equatan `entries`, no las raíces. `state_eq_serial` y `snapshot_stable` siguen siendo igualdad estructural: los dos lados pliegan la misma secuencia de `insert`.

El log del `View` guarda el registro más nuevo en la cabeza. Un `commit` hace `record :: revLog`. `commitMany` copia solo el grupo nuevo (`built ++ revLog`) y comparte la cola. `readLog`, `follow` y el fichero ven el orden cronológico, que es el reverso.

`Store.mem` guarda una lista de tramas, la nueva delante. `append` es un cons. `readAll` invierte y aplana. `replaceAll` sustituye por una sola trama. El almacén de fallos (`FaultState`) sigue concatenando bytes planos: es el inyector de cortes, no el backend de memoria.

## Qué está demostrado

Sin `sorry` y sin `axiom` declarado. `#print axioms` de `get_insert`, `get_insert_ne`, `get_remove`, `nodup_replay`, `compact_eq`, `compact_roundtrip`, `entries_sorted`, `entries_nodup`, `entries_rebuilt`, `move_replays`, `moved_state`, `state_eq_serial`, `snapshot_stable`, `cluster_partition` y `catchUp_state` da `propext`, `Classical.choice` y `Quot.sound`. `steps_commute` no arrastra `Classical.choice`.

- `get_insert`, `get_insert_ne`, `get_remove`, `get_remove_ne`: las ecuaciones del índice de lista, sobre el árbol.
- `entries_sorted`, `entries_nodup`, `entries_of_get`: la iteración está ordenada, no repite claves, y coincide con `get`.
- `nodup_replay` y los `nodup_*` de insertar, borrar y filtrar por shard. El árbol no admite claves duplicadas; los lemas lo dicen.
- `compact_eq` y `compact_roundtrip`: rehacer el log compactado, también tras el codec, devuelve las mismas `entries`.
- `move_replays` y `moved_state`: el log de un shard, rehecho, tiene las `entries` de `inShard`.
- `mem_inShard`, `rebalance_partition`, `cluster_partition`, `state_eq_serial`, `snapshot_stable`, `catchUp_state`, `steps_commute`: siguen. El filtro de shard es `TreeMap.filter`.

No está demostrada una cota O(log n). El balance es el invariante interno de `Std.TreeMap`, no un teorema de cairn. Tampoco está demostrado que `IO.Ref.set` sea atómico ni que el mutex excluya a dos escritores.

## Qué solo está probado con tests

`lake test` terminó con `cairn tests ok`. El fuzz, semilla `0xC0FFEE`, imprimió:

```
fuzz [(detect, 1591), (torn, 89), (miss, 0), (forge, 0), (same, 0)]
```

Los mismos cinco contadores que antes. Los cortes de un log de 12 registros, el fichero (incluido el group commit de 8192 bytes y la cola rota), el router, las tareas, el almacén de fallos y `ShardSet` van en ese mismo `lake test`.

`scripts/crash_demo.sh` (`kill -9` a los 0.3 s, no es un corte de luz) imprimió `recovered 144 keys, a prefix of the committed writes`. Una pasada anterior, con el índice de lista, había impreso 147. Las dos son un prefijo; el número depende de cuándo llega la señal.

## Números

Una pasada de `cairn-design-bench` antes y otra después, en la misma máquina: 4 vCPU, `Intel(R) Xeon(R) Processor` a 2400 MHz, ext4 en `/dev/vdc`. Tres repeticiones, sin promediar. El `open` queda fuera del reloj. `file-*` hace `fdatasync`. `mem-*` es el mismo router en memoria.

Antes (lista asociativa, `++` del log de bytes y del log de registros):

```
file-shards-1 ops=100  206093ns/op 4852ops/s  276915ns/op 3611ops/s  195993ns/op 5102ops/s
file-shards-2 ops=200  120833ns/op 8275ops/s  86026ns/op 11624ops/s  109377ns/op 9142ops/s
file-shards-4 ops=400  61085ns/op 16370ops/s  57966ns/op 17251ops/s  58748ns/op 17021ops/s
mem-shards-1 ops=100  5478466ns/op 182ops/s  5409442ns/op 184ops/s  5391236ns/op 185ops/s
mem-shards-2 ops=200  2803036ns/op 356ops/s  2784675ns/op 359ops/s  2722233ns/op 367ops/s
mem-shards-4 ops=400  1406929ns/op 710ops/s  1394600ns/op 717ops/s  1380735ns/op 724ops/s
file-group-32-shards-4 ops=512  11336ns/op 88214ops/s  5189ns/op 192715ops/s  5644ns/op 177179ops/s
file-contended-1-tasks-4 ops=400  195137ns/op 5124ops/s  213681ns/op 4679ops/s  233684ns/op 4279ops/s
```

Después:

```
file-shards-1 ops=100  190454ns/op 5250ops/s  168778ns/op 5924ops/s  208253ns/op 4801ops/s
file-shards-2 ops=200  78123ns/op 12800ops/s  92477ns/op 10813ops/s  115542ns/op 8654ops/s
file-shards-4 ops=400  53649ns/op 18639ops/s  70828ns/op 14118ops/s  53762ns/op 18600ops/s
mem-shards-1 ops=100  59268ns/op 16872ops/s  38080ns/op 26260ops/s  33897ns/op 29501ops/s
mem-shards-2 ops=200  35357ns/op 28282ops/s  18389ns/op 54380ops/s  17948ns/op 55716ops/s
mem-shards-4 ops=400  19539ns/op 51179ops/s  18866ns/op 53005ops/s  9567ns/op 104525ops/s
file-group-32-shards-4 ops=512  9212ns/op 108554ops/s  8485ns/op 117855ops/s  8311ns/op 120322ops/s
file-contended-1-tasks-4 ops=400  153274ns/op 6524ops/s  154198ns/op 6485ops/s  153646ns/op 6508ops/s
```

En fichero, un shard sigue en el coste del `fdatasync` (unas 0.17–0.28 ms/op en las dos pasadas). Cuatro shards siguen por encima de uno. Cuatro tareas en un solo shard siguen en el mutex de ese shard. El group commit de 32 sigue en unos 5–12 µs/op. La fila de memoria de un shard pasa de unas 5.4–5.5 ms/op a unas 34–59 µs/op. Con 100 claves esa bajada es la de dejar de copiar las tramas de 4096 bytes, no una medida del salto asintótico del árbol frente al escaneo lineal.
