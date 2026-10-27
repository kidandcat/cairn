# Escritores concurrentes en cairn: comparación de diseños

## Decisión

El owner implementa **B ahora**: un escritor por shard, sin mutex global. Cada shard sigue siendo el diseño A (un mutex, un log, un `sync`). **C** (OCC serializable dentro del shard, con conjuntos de lectura y de escritura) solo si un shard se queda corto. No se implementan D, E ni varios escritores del mismo shard.

Esa fase está en el PR del `ShardSet` (`cursor/shard-writer-35e9`), con el informe en `docs/shards.md`. Este PR no se mergea como código: `Bench/Design.lean` de esta rama es el arnés anterior, el de `Handle.flush`, y no debe sustituir al `cairn-design-bench` de `main`, que mide el router con `fdatasync`. El texto de abajo sigue siendo la comparación que llevó a la decisión.

Las cifras de las tablas son de antes del `fdatasync` (PR #2). Miden `flush`, no una barrera de disco. Los números con `sync` real están en el README de `main` y en `docs/shards.md`. No se rehacen aquí y no se promedian con aquellas.

## Qué era este documento

Documento de decisión. No implementa escritores concurrentes. Cuando se escribió, `main` tenía un escritor por `DB` (`Std.Mutex` por base, lecturas de una `View` inmutable). Esta rama añade este texto y el microbenchmark que lo alimentó (`Bench/Design.lean`). Ese ejecutable no entra en `lake test`.

Cada cifra de abajo es una de dos cosas:

- **Medido:** salió de un programa de este repo, en la máquina y con el método que se indican. Las tres repeticiones se copian, no se sustituyen por una media inventada.
- **Estimado:** no hay implementación que medir. La estimación se apoya en el coste medido de la sección crítica actual y en las primitivas que Lean 4.35 tiene o no tiene. Va marcada.

## Lectura para decidir

1. En este disco, un `put` de fichero cuesta decenas de microsegundos de camino Lean. Un `write` de un record de 31 bytes más un `flush` de `Handle`, medido aparte, está por debajo del microsegundo. Juntar varios `flush` (el “group commit” de A) **no subió** el throughput de `DB.commit` en las tres repeticiones.
2. Cuatro tareas sobre **el mismo** `DB` de fichero, claves disjuntas, bajaron el agregado respecto del hilo único. El mutex no paraleliza un shard.
3. Cuatro `DB` de fichero distintos (cuatro mutex, cuatro logs), 500 `put` cada uno, mantuvieron la latencia por operación cerca de la de un solo shard y subieron el agregado. Eso ya es el diseño B, y hoy se obtiene abriendo N bases. Falta un dueño que las despache; no falta un protocolo de locks nuevo.
4. OCC (C), 2PL (D) y un log por tarea (E) no están implementados. Con las primitivas de Lean 4.35 la validación y el secuenciador caen otra vez en un mutex: no hay compare-and-swap ni fetch-add en `Std` ni en `Init`. D y E empeoran recuperación, pruebas o las lecturas sin lock. No son el camino.
5. Recomendación: dejar A como el escritor de cada shard; exponer B (un `DB` por shard, sin mutex global) si se quieren escritores de verdad en claves de shards distintos; dejar C para más adelante, y solo como OCC **serializable** (conjuntos de lectura y de escritura), al lado de `commit`, no en su lugar. F es esa secuencia, no un tercer sistema. El detalle y la tabla están al final.

## Qué hay hoy

Un `DB` es un log, un índice en memoria y un `Std.Mutex Unit`. `DB.commit` entra en el mutex, rechaza el lote vacío y el lote entre shards, escribe **un** record, hace `Store.sync` y solo entonces publica la `View` con `IO.Ref.set`. `set` descarta el valor de `ST.Ref.swap`. El comentario de `swap` en Lean 4.35 dice que el intercambio es atómico (`Init/System/ST.lean`). Los lectores (`snapshot`, `get`, `iterate`, `readLog`, `readEpoch`) solo hacen `view.get`.

El orden de admisión del mutex es el orden serial del modelo `Cairn.Hist` (`Cairn/Snapshot.lean`): `state_eq_serial` y `snapshot_stable`. Ese fichero no formaliza el modelo de memoria de C++. El README lo dice. Esta comparación no lo cambia.

`Store.sync` en el código que midió este documento era `Handle.flush`. En memoria es `pure ()`. Lean 4.35 no tiene `fsync` en el runtime: el PR #2 lo añadió con un shim C, y esa barrera no está en las tablas de abajo. Un `flush` sobrevivió a `kill -9` en el demo ya publicado (una ejecución: 268 claves, un prefijo). Un corte de alimentación no está cubierto. El `kill -9` de después del shim recuperó 147 claves en otra ejecución; tampoco es un corte de luz.

El índice es una lista asociativa (`Cairn/Map.lean`): `insert` recorre la lista. El log en memoria del `DB` es `v.log ++ [record]` en cada commit (copia la espina). El backend de memoria, además, hace `buf.modify (· ++ b)` y copia **todos** los bytes del log en cada append (`Cairn/Store.lean`). `Ref.modify` está `implemented_by` un `take`/`put` unsafe; el backend de memoria usa eso. El de fichero escribe el `ByteArray` en el descriptor.

Cada `DB` tiene su propio mutex. Abrir N ficheros ya son N escritores que no comparten lock. El no-objetivo del README (“several writers at once”) habla de varios escritores del **mismo** `DB`. Entre shards, el paralelismo de B no exige un lock nuevo: exige un sitio que posea el array de `DB` y despache con `shardOf`.

Un lote de `DB.commit` ya es un record y un `flush`. Varias claves, un shard, una atomicidad de record. Eso es group commit de **un** record. No es “varios records, un flush”.

## Primitivas de Lean 4.35

Inventario leído en el toolchain `leanprover/lean4:v4.35.0` (el pin del repo). No es una estimación.

Hay, en `Std.Sync`: `Mutex`, `RecursiveMutex`, `SharedMutex` (un lock de lectores/escritor, no una tabla por clave), `Semaphore`, `Channel`, `Barrier`, `Notify`, `Broadcast`, `CancellationToken`, `StreamMap`. `BaseMutex.lock` documenta que reentrar es comportamiento indefinido, heredado de C++. `SharedMutex` igual.

Hay `IO.asTask`, `IO.wait` (en tareas `IO` devuelve `Except IO.Error`), `Task.Priority.dedicated` (prioridad 9). La documentación de `Task.Priority` dice que por encima de `Priority.max` (8) la tarea va a un hilo dedicado, y que el pool normal no pasa del número de núcleos. En un solo hilo del sistema, una tarea sigue siendo una computación: el diseño tiene que ser correcto si esas tareas no avanzan a la vez.

Hay `IO.Ref` / `ST.Ref`: `get`, `swap` (documentado atómico), `set` = descartar `swap`, `modify` lógico como get+set pero compilado con `take`/`put`. Hay `IO.monoNanosNow` y `IO.monoMsNow`.

Hay en el handle de fichero: `read`, `write`, `flush`, `rewind`, `truncate`, `lock` / `tryLock` / `unlock`. Ese `lock` es el del sistema sobre el descriptor (un fichero entero), no un lock por clave.

No hay, buscado en `Std` e `Init` como primitiva de concurrencia: compare-and-swap, fetch-add, ni una palabra atómica de usuario. Sin FFI no se puede construir un secuenciador lock-free ni una validación OCC lock-free. El núcleo de cairn no usa FFI. Cualquier commit concurrente de esta lista acaba serializando el momento de “este record entra en el log” con un mutex, un canal o un solo hilo.

No hay `fsync` ni `fdatasync` en `IO.FS.Handle`.

`IO.sleep` existe. No sustituye una barrera de disco.

## Cómo se midió

Máquina de esta ejecución, leída antes del banco:

- 4 CPU en línea, 1 hilo por núcleo, Intel Xeon modelo 207, hypervisor KVM, x86_64.
- `/`, `/tmp` y el workspace en `/dev/vdc`, ext4. El temporal de `IO.FS.createTempDir` cae en ese volumen. No es un disco de producción ni un corte de corriente.

Comando: `.lake/build/bin/cairn-design-bench`, tres pasadas seguidas (`rep` 1, 2 y 3) en el mismo proceso, después de 100 `put` de calentamiento. Reloj: `IO.monoNanosNow`. Throughput: `ops * 1000000000 / wall_ns`, división entera. Percentil: se ordena la lista de latencias y se toma el índice `(n - 1) * numer / denom`. Con 1000 muestras, p50 es el índice 499 y p99 el 989. Con 8 muestras, p99 no describe una cola: se publica igual y no se usa para decidir. El cronómetro **por operación** (dos lecturas de reloj) está dentro de la media y del percentil. En un `put` de ~30 µs es una fracción pequeña. En un `write` de cientos de nanosegundos es una fracción grande: esas medias son un techo.

Qué hace cada fila:

| Fila | Qué cronometra |
| --- | --- |
| `file_seq_put` / `mem_seq_put` | 1000 `DB.putStr` de claves distintas, en el hilo llamador. El reloj por operación incluye construir la clave. |
| `file_batch_K` | 1024 operaciones repartidas en lotes de K. El lote se construye **antes** del reloj. El reloj es un `DB.commit` (un record, un `flush`). La latencia es por commit, no por clave. El `ops_s` sí es por clave. |
| `raw_records_then_one_flush` | 1024 `Handle.write` del mismo record de 31 bytes y **un** `flush` al final. Un solo reloj para todo el bucle. |
| `raw_record_group_K` | Grupos de K copias de ese record, cada grupo un `write` y un `flush`. |
| `file_parallel_shards_T` | T ficheros, T `DB`, T tareas `Priority.dedicated`, 500 `putStr` disjuntos cada una. Los `open` van antes del reloj. |
| `contended_file_*_4` / `contended_mem_*_4` | 4 tareas, **un** `DB`, 250 `put` cada una. `disjoint`: claves distintas. `overlap`: las cuatro escriben `ov0`…`ov249`. `hotkey`: las cuatro escriben la clave `"hot"`. |

El banco no implementa C, D, E ni F. No llama a `fsync`. No mide WASM, Android ni ESP32. No mide un corte de alimentación. El `kill -9` citado más abajo es el demo ya existente, una ejecución, no este banco.

Tamaño medido: `record_bytes=31` para la clave `"k"` y el valor `"v"`. Tras 1000 `putStr` secuenciales el fichero mide 33898 bytes en las tres repeticiones.

### Resultados (las tres repeticiones)

`ops_s` es operaciones de clave por segundo, entero. `mean_ns`, `p50_ns` y `p99_ns` son de la muestra por operación, salvo en los lotes (por commit) y en `raw_records_then_one_flush` (una sola muestra: el muro; el percentil no aporta).

**Fichero, un hilo, claves distintas**

| rep | ops | wall_ns | ops_s | mean_ns | p50_ns | p99_ns |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 1000 | 30327189 | 32973 | 30281 | 29730 | 61018 |
| 2 | 1000 | 29642816 | 33734 | 29599 | 28855 | 59704 |
| 3 | 1000 | 30073536 | 33251 | 30029 | 30115 | 61481 |

**Memoria, un hilo, claves distintas**

| rep | ops | wall_ns | ops_s | mean_ns | p50_ns | p99_ns |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 1000 | 134083599 | 7458 | 134035 | 128133 | 302851 |
| 2 | 1000 | 132259971 | 7560 | 132212 | 126908 | 282331 |
| 3 | 1000 | 133708409 | 7478 | 133660 | 127202 | 294245 |

**`DB.commit` en fichero, 1024 claves, lotes de K (latencia = un commit)**

| K | rep | commits en la muestra | ops_s | mean_ns del commit | p50_ns | p99_ns |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 1 | 1024 | 16584 | 59844 | 67724 | 117647 |
| 1 | 2 | 1024 | 20162 | 49242 | 50311 | 97765 |
| 1 | 3 | 1024 | 19836 | 50041 | 50150 | 98964 |
| 8 | 1 | 128 | 24278 | 327543 | 322777 | 708151 |
| 8 | 2 | 128 | 24927 | 319070 | 326325 | 654509 |
| 8 | 3 | 128 | 24500 | 324617 | 321285 | 669822 |
| 32 | 1 | 32 | 21743 | 1464644 | 1468048 | 2694297 |
| 32 | 2 | 32 | 22117 | 1439966 | 1445510 | 2674061 |
| 32 | 3 | 32 | 21818 | 1459746 | 1448231 | 2723044 |
| 128 | 1 | 8 | 19935 | 6392529 | 5799160 | 10058328 |
| 128 | 2 | 8 | 20351 | 6261311 | 5571880 | 10244928 |
| 128 | 3 | 8 | 20438 | 6235317 | 5546633 | 10069056 |

p99 con 8 o 32 muestras no se usa para decidir.

**Handle crudo, record de 31 bytes, 1024 records**

| serie | rep | wall_ns | ops_s | nota |
| --- | ---: | ---: | ---: | --- |
| 1024 `write`, un `flush` | 1 | 51019 | 20070953 | un reloj para el bucle |
| 1024 `write`, un `flush` | 2 | 35236 | 29061187 | |
| 1024 `write`, un `flush` | 3 | 39755 | 25757766 | |
| `write`+`flush` de 1 record | 1 | 426033 | 2403569 | media por grupo 385 ns; incluye dos relojes |
| `write`+`flush` de 1 record | 2 | 398992 | 2566467 | media 359 ns |
| `write`+`flush` de 1 record | 3 | 417547 | 2452418 | media 377 ns |
| grupo 8 | 1 | 64407 | 15898892 | media por grupo 471 ns |
| grupo 8 | 2 | 62677 | 16337731 | media 458 ns |
| grupo 8 | 3 | 66644 | 15365224 | media 489 ns |
| grupo 32 | 1 | 25894 | 39545840 | media 774 ns |
| grupo 32 | 2 | 24615 | 41600650 | media 733 ns |
| grupo 32 | 3 | 31357 | 32656185 | media 935 ns |
| grupo 128 | 1 | 18370 | 55743059 | 8 grupos; media 2247 ns |
| grupo 128 | 2 | 16383 | 62503814 | media 2000 ns |
| grupo 128 | 3 | 20836 | 49145709 | media 2546 ns |

**Shards paralelos (ficheros distintos)**

| tareas | rep | ops | wall_ns | ops_s | mean_ns | p50_ns | p99_ns |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 1 | 500 | 21465036 | 23293 | 41871 | 41142 | 82692 |
| 1 | 2 | 500 | 21465646 | 23293 | 41956 | 41208 | 81566 |
| 1 | 3 | 500 | 21694253 | 23047 | 42171 | 41511 | 88691 |
| 2 | 1 | 1000 | 21909382 | 45642 | 42747 | 41673 | 87635 |
| 2 | 2 | 1000 | 21929511 | 45600 | 42777 | 41984 | 96426 |
| 2 | 3 | 1000 | 22062723 | 45325 | 42885 | 41766 | 89411 |
| 4 | 1 | 2000 | 22041037 | 90739 | 42820 | 42177 | 83238 |
| 4 | 2 | 2000 | 35770199 | 55912 | 56445 | 54307 | 134512 |
| 4 | 3 | 2000 | 26788890 | 74657 | 45959 | 44063 | 88509 |

**Cuatro tareas, un solo `DB`**

| serie | rep | ops_s | mean_ns | p50_ns | p99_ns |
| --- | ---: | ---: | ---: | ---: | ---: |
| file disjoint | 1 | 13563 | 152125 | 73699 | 149284 |
| file disjoint | 2 | 12829 | 152500 | 83550 | 143432 |
| file disjoint | 3 | 13599 | 148896 | 74030 | 152469 |
| file overlap | 1 | 23712 | 106468 | 48676 | 76936 |
| file overlap | 2 | 20905 | 104212 | 48403 | 80611 |
| file overlap | 3 | 22551 | 93892 | 48362 | 71362 |
| file hotkey | 1 | 49098 | 40026 | 20210 | 37206 |
| file hotkey | 2 | 48085 | 42690 | 20172 | 37589 |
| file hotkey | 3 | 48984 | 39530 | 19960 | 39162 |
| mem disjoint | 1 | 1788 | 1050493 | 552890 | 1135407 |
| mem disjoint | 2 | 1773 | 1054985 | 554654 | 1148339 |
| mem disjoint | 3 | 1777 | 1058169 | 556095 | 1172176 |
| mem overlap | 1 | 1946 | 969363 | 508179 | 1092374 |
| mem overlap | 2 | 1938 | 1001232 | 514643 | 1071759 |
| mem overlap | 3 | 1884 | 987175 | 510487 | 1310214 |
| mem hotkey | 1 | 2270 | 838787 | 439628 | 885268 |
| mem hotkey | 2 | 2170 | 890297 | 447402 | 980083 |
| mem hotkey | 3 | 2247 | 853707 | 439758 | 890955 |

Mediciones anteriores, **una** ejecución, reloj de milisegundos (`IO.monoMsNow` en `cairn-bench`), copiadas del README. No son comparables 1:1 con la tabla de nanosegundos: 20 ms tiene granularidad de 1 ms, y aquel bucle no toma un reloj por operación.

```
file put: 1000 ops in 20 ms (50000 ops/s)
file get: 1000 ops in 9 ms (111111 ops/s)
concurrent get (4 tasks x 2000): 8000 ops in 409 ms (19559 ops/s)
```

Demo `kill -9`, una ejecución ya publicada: `recovered 268 keys, a prefix of the committed writes`.

### Qué se puede leer de esos números

El `flush` de este ext4, con el page cache del kernel, no explica el `put`. La cifra de I/O más limpia es 1024 `write` y un `flush`: 35236, 39755 y 51019 ns (entre unos 20 y 29 millones de records/s). Un `write`+`flush` por record, con reloj dentro del bucle, da medias de 359, 377 y 385 ns. Un `file_seq_put` está en medias de 29599, 30029 y 30281 ns. El camino de `DB.putStr` es del orden de ochenta veces ese `write`+`flush` con reloj incluido, y del orden de mil veces el bucle con un solo `flush`. **Estimado a partir de esa resta:** quitar `flush` del camino, o agruparlos, mueve menos de un microsegundo de un `put` de ~30 µs. **Medido, coherente con eso:** los lotes de 8, 32 y 128 claves hicieron 19935–24927 ops/s, por debajo de los 32973–33734 del `put` secuencial. Agrandar el record no pagó. El lote de 1 clave (16584–20162 ops/s) también quedó por debajo del `putStr` secuencial: las claves del lote son más largas y el proceso ya había corrido el barrido de memoria. Esa diferencia no queda aislada.

La memoria secuencial (7458–7560 ops/s, media ~132–134 µs) es más lenta que el fichero en el mismo índice creciente. El código copia la lista de bytes entera en cada append. Eso es un defecto del backend de memoria para este banco, no un modelo de “CPU pura”.

Cuatro tareas en un fichero, claves disjuntas: 12829–13599 ops/s, por debajo del hilo único. La media por operación (~149–153 µs) incluye la espera del mutex; el muro también empeora (unos 74–78 ms frente a unos 30 ms). Solapar 250 claves queda en medio (20905–23712). La clave `"hot"` sube a 48085–49098 ops/s con p50 ~20 µs, **con cuatro tareas en el mismo mutex**. El mapa se queda en una entrada. La dirección encaja con el coste de `insert` sobre una lista que crece, pero este banco no separa índice, codificación, copia de `log ++ [record]` y mutex con un perfilador. No atribuyo los 30 µs enteros a la lista. Lo que sí queda medido: en el diseño actual, “más contención de clave” no es el término que domina; el término gordo entre estas series es el tamaño del mapa y el hecho de compartir un mutex y un log.

Shards distintos: 1 tarea dedicada, 500 puts, 23047–23293 ops/s, p50 ~41 µs (el salto de hilo ya cuesta respecto del hilo llamador a ~33k). 2 tareas, 1000 puts: el muro sigue en ~22 ms y el agregado sube a 45325–45642 ops/s; el p50 sigue ~42 µs. 4 tareas, 2000 puts: muros 22041037, 26788890 y 35770199 ns; agregados 90739, 74657 y 55912 ops/s. Dos repeticiones escalan cerca del muro de un shard; la segunda no. La latencia por operación se mantiene en la banda de un shard en la primera y la tercera (p50 42177 y 44063 ns) y sube en la segunda (p50 54307). **Medido:** hay paralelismo real entre ficheros en 4 vCPU, con dispersión, y no es un 4× limpio. **Medido:** no aparece dentro de un fichero.

Las lecturas concurrentes no se volvieron a medir aquí. La cifra vieja (4 tareas leyendo, 19559 ops/s, un reloj de milisegundos) sigue siendo una sola ejecución. El diseño de lectura (un `Ref.get` de una `View` inmutable) es el que A–F pueden conservar. C y D lo pierden si una lectura toma un lock exclusivo.

## Los diseños

En todos, un record sigue siendo el lote atómico de un shard. Un lote con claves de dos shards se rechaza. No hay commit de dos fases. Las lecturas que no toman el mutex siguen viendo una `View` vieja o una nueva, no una a medias, en la medida en que `swap` sea el intercambio que el runtime documenta. Eso no está probado en el kernel de Lean.

### A. Un escritor, mutex, group commit

Es el `DB` de hoy, con la opción de juntar varios commits en menos `flush`.

**Aislamiento.** El modelo actual es serializable por orden de admisión: `Hist` es una secuencia de lotes, `state_eq_serial` dice que el estado es el pliegue de esa secuencia, `snapshot_stable` dice que una foto no cambia cuando la historia crece. No es snapshot isolation. No hay write skew: quien escribe, escribe solo dentro del mutex, viendo el mapa del commit anterior.

**Conflictos.** No hay abortos por clave. Dos `put` de la misma clave se ordenan. El segundo gana. Un lote vacío o entre shards falla y no se appendea (código de `commitNow`, cubierto por tests).

**Rendimiento, claves disjuntas.** **Medido** en un `DB`: 32973–33734 ops/s, p50 ~29–30 µs, p99 ~60–61 µs, 1000 claves. **Medido:** agrupar 8, 32 o 128 operaciones en un record y un `flush` no superó esa cifra (19935–24927 ops/s). **Estimado:** en un backend futuro con una barrera de disco real (no existe en Lean 4.35; no se midió `fsync`), agrupar bajaría el número de barreras. Hoy el ahorro de `flush` cabe en la fracción de microsegundo que el handle ya midió, al lado de un `put` de ~30 µs.

**Rendimiento, contención.** **Medido:** 4 tareas, un fichero, claves disjuntas, 12829–13599 ops/s. La cola del mutex alarga la latencia (p50 ~74–84 µs, p99 ~143–152 µs). La clave única fue más rápida por el mapa chico, no porque el mutex escale.

**Complejidad en Lean.** La menor. `commitNow` ya existe. Un group commit de varios **records** sería un bucle de append y un `sync`, todavía bajo el mismo mutex. No hace falta CAS. Cabe en 32 bits: no toca el codec.

**Pruebas.** Lo que ya hay: el modelo `Hist`, el prefijo de crash (`recovery_prefix`, `decodeFile_prefix`), la foto estable. Un group commit que escribe varios records y hace un `flush` **no** es un solo paso atómico frente a un corte: `recovery_prefix` dice que sobrevive un prefijo de records. Habría que enunciarlo, no rehacerlo. Lo que no se puede demostrar: que el mutex de C++ no admite dos secciones, que `swap` es atómico, que `flush` es durable, que el CRC caza todo.

**Crash, compactación, shards, réplicas.** Un log, un prefijo, una compactación que reasigna LSN y obliga a `installSnapshot`. Cada shard que sea un `DB` sigue igual. El follower que diverge pierde el sufijo (el líder gana). A no cambia eso.

**WASM / ESP32.** Correcto en un hilo. El mutex es una cola; si no hay hilos, la cola tiene un cliente. No se gana paralelismo. No se midió ese runtime.

**Se pierde.** Paralelismo dentro del shard y, si el llamador usa un solo `DB` para todas las claves, también entre shards. No se pierde aislamiento ni el teorema de prefijo.

### B. Un escritor por shard

Paralelo entre shards, serializado dentro. Cada shard es un cairn con su log, su mutex y su punto de commit. No hay mutex global.

**Aislamiento.** Serializable **dentro** del shard, por el mismo `Hist`. No hay un orden serial global. Dos commits en shards distintos no están ordenados entre sí. Eso ya es la regla del proyecto: un lote no cruza de shard. Una lectura que junta varios shards ve una mezcla de fotos; no es un snapshot transversal. Hay que decirlo en la API del router.

**Conflictos.** Igual que A dentro del shard. Cero abortos por carrera entre shards: las claves no se pisan, por `key_one_shard` (una clave, un id, en una época).

**Rendimiento, claves disjuntas.** **Medido** con N `DB` de fichero, sin router todavía (el despacho sería una llamada a `shardOf` más un array; **estimado** despreciable al lado de 30 µs):

- 1 shard en tarea dedicada: 23047–23293 ops/s, p50 ~41 µs.
- 2 shards: 45325–45642 ops/s, p50 ~42 µs, muro ~22 ms igual que el de 500 puts.
- 4 shards: 55912, 74657 y 90739 ops/s. El mejor muro (22041037 ns para 2000 puts) iguala al de un shard de 500; el peor (35770199 ns) no. Dispersión real en 4 vCPU compartidos.

**Estimado:** en un hilo (WASM sin pthreads, ESP32) el agregado vuelve al de un escritor, porque las tareas no avanzan a la vez. La corrección no depende de eso.

**Rendimiento, contención.** Una clave caliente vive en un shard. Ese shard es A. **Medido** el caso de un `DB`: no escala. **Estimado:** repartir el rango para partir la clave caliente no se puede si es una sola clave; haría falta C o partir el valor, y partir el valor es otro producto.

**Complejidad.** Pequeña y aditiva. Un módulo que posee `Array DB` (o una lista), abre un fichero por id, y enruta `put`/`get`/`commit`. `sameShard` ya rechaza el lote cruzado. No se reescribe `commitNow`. El mutex por `DB` ya está. Cabe en los targets de 32 bits: el router es aritmética de bytes y un array de bases.

**Pruebas.** Ya: `shardOf` total y determinista, `key_one_shard`, `rebalance_partition`, `move_replays`. Se puede añadir: el id que elige el router es el índice del array (función, fácil). Cada shard conserva su `Hist`; no hace falta un `Hist` global, y un `Hist` global sería falso. No se puede probar el solape temporal de los hilos. El test de estrés (dos shards, tareas) es la evidencia de paralelismo, no un teorema.

**Crash, compactación, shards, réplicas.** Cada log recupera por su cuenta, con el prefijo de hoy. Una compactación reescribe el LSN de **ese** shard; el follower de ese shard hace `installSnapshot`. Los demás shards no se enteran. `adopt` sigue siendo el movimiento local. No aparece un corte a medias entre dos shards, porque no hay un commit que los cubra: o bien cada uno commiteó, o bien no. Un crash puede dejar el shard 0 actualizado y el shard 1 no. Eso es lo que “sin transacción entre shards” significa en disco.

**WASM / ESP32.** El mismo código corre en un hilo. Varios ficheros implican varios descriptores; en un microcontrolador el límite es el número de ficheros abiertos y la RAM del índice por shard, no el lock. **Estimado**, sin medida en ESP32.

**Se pierde.** Un orden serial de todo el proceso. Una foto que corte todos los shards a la vez. Nada del aislamiento intra-shard.

### C. MVCC optimista dentro del shard

`transact`: se toma una `View`, se lee y se escribe en privado, y en el commit se valida contra lo que entró después de la foto. Si falla, no se appendea y se reintenta. El append sigue siendo una sección corta.

Dos variantes, y no dan el mismo aislamiento:

- **Solo write-write** (el conjunto de escritura choca con un commit posterior): snapshot isolation. Las lecturas son la foto. Dos transacciones pueden leer los mismos dos valores y escribir cada una una clave distinta; las dos commitean. Eso es write skew. El estado no es el de ningún orden serial. El `Hist` de hoy **rechaza** ese interleaving porque el segundo escritor habría visto el write del primero.
- **Write-write y read-write** (el conjunto de lectura choca con el conjunto de escritura de un commit posterior), validados en el mismo paso que el append: OCC serializable, equivalente al orden de commit. Es el que conserva la frase “el orden de commit es un orden serial”.

Recomiendo no implementar la variante débil. Bajar a SI sin decirlo rompería la garantía que `state_eq_serial` enuncia para el escritor único.

**Conflictos.** Aborto si la validación falla. El aborto no escribe. Bajo claves disjuntas y transacciones que no leen lo que otro escribe, **estimado:** casi ningún aborto. Bajo una clave caliente, **estimado:** reintentos en cadena; puede haber livelock si todos reintentan sin espera. No hay medida: no hay `transact`. Una espera aleatoria usa `IO.sleep` (granularidad de milisegundos) o un bucle; las dos son incómodas, y ninguna está medida aquí.

La validación tiene que ocurrir en la misma sección que decide el LSN y el append. Sin CAS, esa sección es el mutex del shard (o un actor único). OCC no saca el commit del mutex. Saca del mutex el trabajo de **antes**: lecturas y cómputo del usuario.

**Rendimiento, claves disjuntas.** El `put` de una clave ya preparada es casi todo sección crítica (encode, append, índice, publicar). **Medido** ese bloque: ~30 µs de media en fichero, de los cuales el `flush` es una fracción de 1 µs. **Estimado:** OCC no multiplica el throughput de `put`/`commit` de hoy, porque no hay trabajo que mover fuera del lock. Puede ayudar a una transacción que lee varias claves, calcula y escribe: los lectores de la foto no toman el mutex (igual que ahora) y solo el commit lo toma. El techo de commits por segundo de un shard sigue siendo el de A.

**Rendimiento, contención.** **Estimado:** peor que A en una clave caliente, por el reintento. A hace cola y cada intento escribe una vez. C hace cola igual en la validación y, además, tira el trabajo si choca. El conjunto de lectura cuesta RAM; en un ESP32 eso importa antes que el CPU.

**Complejidad.** Grande. Tipos de transacción, conjuntos, reintento, y un protocolo de “la compactación y el cambio de época invalidan las fotos en vuelo”. Si no se invalidan, una transacción valida contra un log que ya no es el del índice. `follow` / `installSnapshot` también cambian el log bajo el mutex: una foto tomada antes queda vieja de época, no solo de LSN.

Lean alcanza para escribirlo: `IO.Ref`, mutex, `Task`. No alcanza para validar sin lock.

**Pruebas.** En un modelo nuevo (no en el C++):

- Un commit que pasa la validación WW+RW es una extensión de `Hist` en orden de commit, y el estado es el pliegue serial. Esto es demostrable si la validación se escribe como función pura sobre la historia.
- Un aborto no aparece en `Hist.commits`.
- La variante WW-only **no** cumple `state_eq_serial` para todo interleaving de lecturas. Se puede dar el contraejemplo del write skew como teorema negativo (existe una historia aceptada por la validación débil cuyo mapa no es ningún pliegue serial de esas transacciones leídas). Conviene demostrarlo para que SI no se cuele en el README.

No se puede demostrar: ausencia de livelock, que el bucle de reintento implementa el modelo, el modelo de memoria, ni que una foto leída por `Ref.get` es la que la validación cree.

**Crash.** El record de un commit validado es el de siempre: o entra entero o el corte lo tira (`recovery_prefix`). Un aborto no tiene bytes. Un group commit de varios commits validados en un `flush` vuelve al prefijo: el crash puede guardar los primeros records del grupo. Cada record sigue siendo atómico por el encuadre de longitudes. La validación no sobrevive al proceso; al reabrir no hay transacciones a medio hacer. Eso es una ventaja frente a locks guardados en el log.

**Compactación, réplicas, shards.** La compactación cambia los LSN. Una transacción en vuelo tiene que abortar si el epoch o la identidad del log cambian (`compact`, `adopt`, `installSnapshot`). La réplica sigue recibiendo records ya comprometidos, no conjuntos de lectura. B+C (véase F) deja la réplica como está.

**WASM / ESP32.** El reintento es correcto en un hilo si el commit no reentra el mutex. Un `Task` que tome el mutex y espere a otro `Task` en el mismo hilo se bloquea. El código de C no debe esperar dentro del lock. Los conjuntos de lectura son el coste de RAM.

**Se pierde**, si se elige SI: serializabilidad, y el enunciado actual del README. Si se elige OCC serializable: nada del aislamiento, y sí se gana una clase nueva de fallos (abortos) que A no tiene. El `put` de una clave no debería pagarlos: puede seguir siendo A.

### D. 2PL, locks por clave o por rango

Two-phase locking: locks compartidos para leer, exclusivos para escribir, soltarlos todos tras el commit. Bien hecho, el orden de los locks es serializable (conflicto-serializable). No es SI. No hace falta conjunto de lectura si los locks se tienen hasta el final.

**Conflictos.** Espera, no aborto, salvo deadlock. El deadlock es el fallo de este diseño en Lean: el mutex no es reentrante, el pool de tareas es finito (del orden de los núcleos, documentación de `Task.Priority`), y un orden de locks que no sea total se bloquea. Un lock por clave con `Std.Mutex` sería una tabla enorme y cada lock es un objeto de runtime. `SharedMutex` es **un** lock, no una tabla. El `Handle.lock` bloquea el fichero entero: sirve como candado entre procesos, no como 2PL de claves.

Para no perder la lectura sin lock haría falta MV2PL (locks de escritura más versiones de lectura). Eso es más maquinaria que C, y las versiones ya las da la `View`.

**Rendimiento.** **Estimado**, anclado a la medida: cada `put` de A ya entra en un mutex. Añadir locks por clave **dentro** de ese mutex no paraleliza. Sacarlos **fuera** exige o bien muchos mutex (memoria, deadlock) o bien un lock manager. Claves disjuntas podrían avanzar a la vez solo en la sección que no toca el log. El log sigue siendo uno, así que el append se serializa igual que en C. El techo de commits es el de A, con más instrucciones por operación. Contención: colas por clave y riesgo de deadlock; **estimado** peor latencia que A, sin números.

**Complejidad.** La más alta de la lista junto con E, y la peor de encajar en el estilo del repo. Hay que definir un orden total de claves para evitar deadlocks (el orden de bytes ya existe: `keyLe`) y demostrar que todo el código lo respeta, incluidos `compact` y `follow`, que hoy toman el mutex del `DB` y no pueden tomar un lock de clave sin una jerarquía. `compact` bajo 2PL es una transacción de todas las claves.

**Pruebas.** Un modelo de schedules, un grafo de espera y “orden total de locks ⇒ sin ciclo” es demostrable y largo. Conectarlo con `Hist` también. No cubre el runtime ni el UB de reentrar. Es más superficie que el OCC puro, donde la validación es una función sobre listas.

**Crash.** Un lock no es durable. Un crash suelta los locks al morir el proceso; el log recupera como hoy si el append sigue siendo el punto de commit. Quien hubiera querido locks en el log (para transacciones que sobreviven al proceso) sale del modelo de cairn. No hace falta.

**Compactación, réplicas, targets.** La compactación tiene que tomar todos los locks o abortar a los poseedores: fácil de equivocar. La réplica no ve locks, ve records: bien. En un solo hilo, esperar un lock que tiene la misma tarea es deadlock seguro. En ESP32 la tabla de locks compite con el índice por la RAM. 32 bits: el codec no cambia; la tabla sí puede no caber.

**Se pierde.** La lectura de un `Ref.get` si las lecturas toman locks compartidos. Se pierde simplicidad del modelo. No se gana un techo de commits por encima de A.

### E. Log por escritor, fusión por LSN

Cada tarea appendea a su propio log. Un LSN global ordena la fusión. Parece el patrón de logs estructurados por núcleo.

**Aislamiento.** Depende de la fusión.

- Fusión por LSN de solo escrituras, último LSN gana: se pierden updates. Ni siquiera es SI. Dos `put` de la misma clave en dos logs no se ven entre sí hasta fundir, y el perdedor desaparece.
- Fusión que aplica OCC (conjuntos de lectura incluidos): es C más N logs. El aislamiento es el de C. La recuperación es peor que la de C.

**Conflictos.** Sin conjuntos de lectura, el conflicto se resuelve tirando un valor (lost update), no abortando. Con conjuntos, abortos como en C, y además hay que fundir antes de validar o validar en la fusión.

**El LSN.** Asignar un LSN único y creciente sin huecos durables exige un secuenciador. No hay fetch-add. Las opciones reales son: un mutex (entonces el secuenciador es A, y los logs partidos solo paralelizan el `write`), o LSN por log más un reloj que **no** da un orden total reproducible tras un crash. Un crash puede dejar los ficheros en longitudes que no determinan qué record “iba antes” si el LSN no se persistió en un solo sitio antes del ack. **Estimado** el fallo; la ausencia de la primitiva es un hecho del toolchain.

**Rendimiento, claves disjuntas.** El `write` paralelo es lo que el banco de shards ya midió (varios ficheros). El cuello de un `put` no es el `write`. **Estimado:** N logs no acercan el `put` a los 20–29 millones de records/s del handle crudo, porque el índice, la codificación y la publicación de la `View` siguen en algún sitio serial si se quiere una foto coherente. Si cada log tiene su índice, eso es B con otro nombre y sin el router determinista: peor, porque una clave podría caer en dos logs.

**Rendimiento, contención.** **Estimado:** la fusión de una clave caliente es un solo hilo, más el coste de leer N logs. Peor que A.

**Complejidad.** Alta. N manejadores de fichero, un formato de fusión, un criterio de “ya es durable”. Choca con el codec actual, que asume un byte stream y un prefijo.

**Pruebas.** `decodeFile_prefix` es por stream. Habría un teorema nuevo: si existe un orden total durable (una lista de LSN escrita en un sitio antes de responder al cliente), la fusión es una función y el replay coincide con ese orden. Sin ese sitio, el enunciado es falso y no se debe fingir. La compactación de N logs a un snapshot es `moved` a lo grande; demostrable, y obliga a los followers a instalar, no a appendear cruzando la frontera (igual que hoy, por cada log).

**Crash, réplicas.** El follower de hoy aplica **un** log (`appendEntries` con `prev` = longitud). N logs son N unidades de réplica o una fusión antes de replicar. Fundir antes de replicar devuelve el cuello a un log. Replicar N logs empuja el consenso fuera de alcance (el proyecto no tiene quorum ni término). Un corte a mitad de la fusión tiene que caer en el prefijo de **cada** stream y en un orden acordado. Es el punto donde E pierde lo que cairn ya demostró.

**WASM / ESP32.** N ficheros y N buffers en un aparato sin hilos: se paga la complejidad y no el paralelismo. Pocos descriptores.

**Se pierde.** El teorema de un prefijo, la unidad de réplica, la compactación de un log, el orden determinista tras un corte si el secuenciador no es durable. No es un buen intercambio: el paralelismo de I/O que buscaría E ya se midió en B, y el I/O no es el cuello.

### F. Híbrido B+C

Un escritor lógico por shard para el append (el mutex de B) y, dentro del shard, transacciones optimistas serializables (C) cuyo trabajo previo al commit corre sin el lock.

No es B+D ni B+E. Meter 2PL o logs partidos dentro del shard arrastra los problemas de D y E a cada rango.

**Aislamiento.** Entre shards, el de B (ningún orden global). Dentro, el de C serializable si la validación es WW+RW. La composición es: cada clave un shard (`key_one_shard`), y dentro de ese shard el orden de commits es un `Hist`. Una transacción no toca dos shards. Write skew **entre** shards puede existir aunque cada shard sea serializable: es la misma limitación que ya tiene el proyecto, no una nueva. Dentro del shard no debe existir.

**Conflictos.** Abortos solo intra-shard. Una clave en otro shard no aborta.

**Rendimiento.** El de B en claves de shards distintos (**medido** el caso N ficheros). El de C dentro del shard caliente (**estimado**: no mejora el `put` corto; sí deja correr cómputo fuera del lock). Group commit dentro del commit del shard: **medido** que un record grande no sube ops/s con `flush`. Sigue sirviendo como atomicidad de lote, que ya es `DB.commit`.

**Complejidad.** La suma, en ese orden. Implementar C antes de tener el router de N `DB` optimiza el shard caliente y deja el caso disjunto, que es el que el banco sí acelera, en manos del llamador.

**Pruebas.** Las de B más las de C. No hace falta una prueba de producto si la transacción no cruza el shard: se demuestra que `transact` solo mira el `Hist` de su `DB`.

**Crash, compactación, réplicas, targets.** Igual que B para el disco y la réplica (un log por shard, records ya validados). Igual que C para fotos en vuelo frente a `compact` y `adopt`. En un hilo, B+C es A más un reintento que no debe reentrar el mutex.

**Se pierde.** Lo que se pierde en C (abortos, RAM de conjuntos) en cada shard que active `transact`. Los shards que solo hacen `put` no tienen por qué perderlo.

### Algo que el banco sugiere y no es un escritor

El hueco entre el handle crudo y `DB.put`, y el hueco entre la clave única y las 1000 claves distintas, no se cierran con locks. Dos costes están en el código y se ven en las cifras, sin que este banco los aísle con un perfilador:

- El backend de memoria copia todos los bytes en cada append. **Medido** el efecto de conjunto: 7458–7560 ops/s frente a 32973–33734 del fichero, mismo patrón de claves.
- El índice recorre una lista, y `v.log ++ [record]` copia la espina en ambos backends. La serie `hotkey` (p50 ~20 µs, mapa de una clave, aun con cuatro tareas) frente a `file_seq_put` (p50 ~29–30 µs, mapa que crece, un hilo) va en esa dirección. No es un experimento controlado: cambian a la vez los hilos y el tamaño del mapa.

**Estimado:** un índice de coste más plano y un buffer que no sea `List UInt8` suben el `put` de un shard más de lo que lo sube agrupar `flush`. No hay cifra de un índice alternativo. Tocar `Map` reabre los teoremas de `get`/`insert`/`replay`. No cambia el formato del log. Es independiente de A–F y anterior, en rendimiento, a C y a E. No sustituye a B: B multiplica shards; el índice acelera cada uno.

## Tabla

“Disjunto” y “contención” son throughput de clave. Donde dice medido, el rango es el mínimo y el máximo de las tres repeticiones de esta máquina. Donde dice estimado, no hay código.

| | Aislamiento | Abortos | Claves disjuntas | Contención en un shard | Lean 4.35 | Qué se puede probar | Crash y réplica | Un hilo / RAM pequeña | Qué se pierde |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| **A** mutex ± group commit | Serializable por admisión (`Hist`) | No por clave | **Medido** 33.0–33.7k ops/s un hilo. Lotes 8–128: 19.9–24.9k, no mejoran | **Medido** 4 tareas, un fichero, disjuntas: 12.8–13.6k ops/s | Mutex y `Ref`. Sin CAS. Sin `fsync` | Ya: `state_eq_serial`, `snapshot_stable`, prefijo. No: C++, `flush`, CRC | Un log, prefijo. Varios records en un `flush` siguen siendo un prefijo, no un grupo atómico | Correcto. Sin speedup | Paralelismo |
| **B** un escritor por shard | Serializable en el shard. Sin orden global | No | **Medido** 4 ficheros: 55.9–90.7k ops/s; p50 ~42–54 µs | Igual que A en el shard caliente | Igual. N `DB` ya tienen N mutex | `key_one_shard` + un `Hist` por `DB`. No el solape de hilos | N logs, cada uno con el prefijo de hoy. Réplica por shard | Correcto en serie. N ficheros, N índices | Foto global y orden global |
| **C** OCC en el shard | Serializable si WW+RW. SI si solo WW (write skew) | Sí, y reintento. Livelock posible | **Estimado:** el `put` corto no pasa del techo de A (~30 µs). Ayuda si hay cómputo fuera del lock | **Estimado:** peor que A (reintentos). Sin medida | Validación bajo el mutex. No hay CAS para evitarlo | Modelo puro: commit = extensión de `Hist`; aborto fuera del log; teorema negativo de SI | El record validado usa el prefijo actual. Fotos mueren en compactación y en cambio de época | Correcto si no se espera dentro del lock. Los read sets gastan RAM | Abortos. SI perdería la serializabilidad actual |
| **D** 2PL | Conflicto-serializable si no hay deadlock | Espera; deadlock si el orden no es total | **Estimado:** techo de commits = A, con más trabajo. El log sigue siendo uno | **Estimado:** colas y deadlocks. `SharedMutex` no es una tabla | Mutex no reentrante + pool finito. `Handle.lock` es el fichero entero | Schedule y orden de locks, largo. No el runtime | Locks no durables. El log, si el append es el commit, recupera como A | Deadlock fácil en un hilo. Tabla de locks en RAM | Lectura sin lock, si la lectura bloquea |
| **E** log por tarea + LSN | Lost update, o C si la fusión valida | Según la fusión | **Estimado:** el I/O paralelo ya se vio en B y no es el cuello del `put` | **Estimado:** la fusión de la clave caliente es un hilo | Sin fetch-add el LSN durable es un mutex | Prefijo **por stream**. Orden total solo si el secuenciador es durable y único | Rompe la unidad de réplica o la rehace al fundir. El crash no determina el orden si el LSN no se guardó antes del ack | N ficheros, cero paralelismo real | El teorema de un log, la réplica simple, el orden tras el corte |
| **F** B luego C | B entre shards, C serializable dentro | Solo dentro del shard | El de B, **medido** | El de C, **estimado** | Suma de B y C | Composición: `transact` no mira el `Hist` de otro shard | Un log por shard de records ya validados | Igual que B y C | Lo de C, solo en los shards que usen `transact` |

## Recomendación

Dejar el escritor de cada `DB` como está (A). No invertir en agrupar `flush` para ganar ops/s: en este ext4, con `Handle.flush` y sin `fsync`, las tres repeticiones dicen que no. Conservar `DB.commit` como el group commit que ya es: un record, un `flush`, varias claves de un shard.

Si el objetivo es “escritores de verdad”, el paso que las medidas apoyan es B: un valor que posea un `DB` por shard y despache con `shardOf`, sin mutex global. El paralelismo entre ficheros ya se ha visto (agregado 55.9k–90.7k ops/s en 4 shards frente a 23.0k–23.3k de un shard en tarea dedicada, con una repetición claramente peor). Dentro del shard el contrato no cambia, así que las pruebas de `Hist` y de recuperación se quedan. Hay que escribir en la API que no existe un orden serial entre shards ni una foto que los corte a la vez.

No hacer D. No hacer E. Los dos cuestan más de lo que el banco dice que se puede ganar, y E suelta el prefijo único que ya está demostrado.

No hacer C todavía. Cuando haya transacciones que leen, calculan y escriben dentro de un shard caliente, hacerla serializable (WW y RW), bajo el mutex de ese shard, con aborto que no appendea, y dejar `put` / `commit` en el camino de A. Declarar SI sería bajar la garantía del modelo actual. F es exactamente “primero B, y C solo si un shard se queda corto”: no hace falta un diseño con otro nombre.

Antes de esperar más ops/s de un solo shard, medir un índice que no recorra una lista y un backend de memoria que no copie el log entero. Es una estimación de dónde está el tiempo; la única cifra firme es el hueco ya medido entre `put` (~30 µs) y el handle (el bucle de 1024 `write` y un `flush`, 35–51 µs **en total**).

## Plan por fases

Sin plazos. El tamaño es el de los módulos y el de la superficie de prueba.

**Fase 0. Esta nota.** Rama `docs/concurrencia`. No entra en `main` hasta que se mergee a mano. No cambia el runtime.

**Fase 1. Dueño de N bases (B).** Módulo nuevo al lado de `Cairn/Router.lean` y `Cairn/DB.lean`. Abre un fichero (o un `Store`) por id de shard, guarda el array, enruta get/put/commit/iterate. No añade un mutex por encima. `commit` de un lote que cruce el rango sigue fallando. Pruebas nuevas: el id del array es `shardOf`; un test con tareas en dos ficheros, del estilo del estrés que ya existe. Pruebas que se reutilizan: `key_one_shard`, `Hist` por cada `DB`, `recovery_prefix` por cada fichero. No se toca el codec. Correcto si el runtime ejecuta las tareas en un solo hilo; el speedup es solo nativo. El banco de esta rama sirve otra vez, apuntando al router en vez de al bucle que abre los `DB` a mano.

**Fase 2. No hacer, salvo que aparezca una barrera de disco.** Juntar varios records en un `flush` dentro de `commitNow`. Código corto. Hay que decir en el README que un corte puede conservar un prefijo del grupo (`recovery_prefix` ya lo da). Throughput: no es el objetivo, con las cifras de arriba. Bloqueado de verdad si se quiere durabilidad ante corte de corriente: `IO.FS.Handle` no tiene `fsync`, y el núcleo no usa FFI. Un backend externo que sí sincronice sería un `Store` nuevo, fuera de esta fase.

**Fase 3. OCC serializable en un shard (la mitad C de F).** Solo con un uso real de transacciones largas. Módulo nuevo (`transact`, conjuntos, reintento con tope). El commit valida y appendea bajo el mutex ya existente. `compact`, `adopt`, `installSnapshot` y `setEpoch` marcan inválidas las fotos vivas. `put` de una clave no pasa por ahí. Modelo nuevo al lado de `Snapshot.lean`: validación pura, extensión de `Hist`, aborto ausente del log, y un teorema de que la validación WW-only admite un write skew. Tests de estrés contra un modelo secuencial, disjunto y en conflicto, más un corte a mitad de commit (el record a medias ya lo cubre el prefijo). Superficie grande, localizada: no reescribe el router ni el codec. Sigue sin ser una prueba del mutex de C++.

**Explícitamente fuera:** D, E, commit entre shards, quorum, y cualquier secuenciador lock-free.

**Transversal, cuando se quiera bajar los ~30 µs:** experimento de índice y de buffer, con el mismo banco, antes de dar por hecho que hace falta C. Si se cambia `Map`, se rehacen los lemas que despliegan `insert` y `remove`. El fichero de log no cambia de formato.
