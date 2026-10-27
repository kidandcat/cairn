# Durabilidad ante corte de luz y CRC

Informe de la rama `cursor/durability-crc-35e9`. No está mergeada. El owner decide cuándo entra en `main`. La comparación de concurrencia sigue en su propio PR. Varios escritores a la vez sigue siendo un non-goal.

El núcleo de Lean no llama a FFI. El único C es `native/cairn_sync.c`, y solo lo usa el backend de fichero (`Cairn.Posix`, importado por `Cairn.Store`). Longitudes `UInt32`, LSN `UInt64`, sin `USize` en el codec. No hay `sorry`, ni `axiom` declarado, ni `partial`, ni `bv_decide`, ni `native_decide`.

## Contrato de `sync`

Después de que `sync` vuelve, cada `append` y cada `replaceAll` desde el `sync` anterior sobrevive un corte. Lo que no ha pasado por un `sync` completado puede perderse, quedar torn, reordenarse o escribirse solo en parte, a granularidad de sector.

El modelo formal es una imagen estable (lo ya sincronizado, alineado a bloque) más una cola pendiente. `Tail.lost` no conserva nada de esa cola. `Tail.take n` conserva un prefijo de bytes. El caso de sector es `n` múltiplo de `blockSize` (4096). Un destino de sector que falta se queda en ceros en su sitio: el disco no desplaza los sectores posteriores. Eso está ejercitado por el `Storage` simulado de `Cairn.Crash`. El teorema `recovery_keeps_synced` cubre el prefijo de bytes, que incluye el prefijo por sector: si `n` cubre la codificación de los grupos ya sincronizados, `decodeFile` de ese prefijo devuelve esos grupos (y, si el corte cayó más adelante, un prefijo de lo que iba en vuelo). El resultado es un prefijo de lo enviado. Hace falta `GroupsFit` / `RecordsFit`: sin esa hipótesis `UInt32.ofNat` da la vuelta y el enunciado es falso.

El orden de un commit es escribir, `sync`, y solo entonces publicar la vista. La compactación es fichero nuevo, `fdatasync`, `rename` atómico, `fsync` del directorio. Nunca se renombra antes del `fdatasync`. Un corte después del `rename` y antes del `fsync` del directorio puede mostrar el nombre viejo o el nuevo; los dos ficheros ya estaban sincronizados en datos.

El backend de memoria hace `sync` y vuelve. No es un disco.

## Qué está demostrado

Sobre la recuperación, en Lean:

- `decodeFile_prefix` y `recovery_prefix`: un prefijo de bytes de una codificación bien formada es un prefijo de los registros, y el replay de eso es el mapa recuperado. Hace falta `RecordsFit`.
- `recovery_keeps_synced`: si el prefijo incluye todo lo que ya se sincronizó, esas operaciones están en el resultado, y el resultado sigue siendo un prefijo de lo enviado (sincronizado más en vuelo). Hace falta `GroupsFit`.

Eso no dice que cualquier basura pegada detrás de un fichero válido sea un prefijo. Una colisión del checksum podría añadir una trama. Tampoco cubre un sector físico mayor de 4096 bytes: ese corte puede partir datos que `sync` ya dio por buenos.

Sobre CRC-32 no reflejado (`sum32`, polinomio `0x04C11DB7`, init 0, sin xor final), que es el checksum de la cabecera y de cada trama:

- `sum32_burst`: si los bits a uno caben en una ventana de 32 posiciones consecutivas (`polyOf = B * 2^t` con `0 < B < 2^32`), el checksum no es cero. El límite es la anchura de la ventana, no la longitud del mensaje. Vale para cualquier longitud.
- `sum32_one_bit` y `sum32_weight_one`: un solo bit, o peso de Hamming 1, es esa ventana.
- `sum32_two_close`: dos bits a distancia `d` con `1 ≤ d ≤ 31`.
- `sum32_xor` y `sum32_detects_burst`: en dos cadenas de la misma longitud, el checksum del xor es el xor de los checksums, así que una ráfaga de ese tipo cambia el checksum del mensaje.
- `not_all_odd_weight`: `sum32 [1, 4, 0xC1, 0x1D, 0xB7] = 0` y el peso es impar (15). El polinomio no detecta todos los errores de peso impar. `(x+1)` no divide a este polinomio; el contraejemplo es la prueba, no una conjetura.

No está demostrado: dos bits a distancia mayor de 31 (haría falta el orden de `x` módulo el polinomio). No se promete que un checksum de anchura fija detecte toda corrupción.

El CRC reflejado de cada registro (`crc32`) se mantiene. No es `sum32`. La prueba de ráfaga es de `sum32`.

`#print axioms` de `sum32_burst`, `sum32_detects_burst`, `recovery_keeps_synced`, `decodeFile_prefix` y `recovery_prefix` da solo `propext`, `Quot.sound` y `Classical.choice` (de `omega`).

## Política de corrupción

`scan` separa cuatro casos:

- `clean`: todo byte pertenece a una trama válida. Abrir no reescribe el fichero.
- `torn`: falta un sufijo. Se trunca a lo consumido. Un prefijo de una codificación válida es `torn` o `clean`, nunca `corrupt`.
- `corrupt`: una trama completa falla y más adelante hay otra trama `SEG1` válida. `openFile` lanza `corrupt log`. No devuelve un mapa a medias.
- `reject`: no es un fichero cairn (`"HI"`, `NOTACAIR`). No se trunca ni se pisa. Un prefijo real de tres bytes de la cabecera sí abre como log vacío.

`openFileRepair` trunca a propósito una cola rota y una corrupción en medio. Un `reject` sigue fallando.

Dos huecos que parecen una cola rota y por tanto se truncan, no se señalan como corrupción en medio: un bit dañado solo en el último segmento, y un campo de longitud tan dañado que la trama ya no cabe en el fichero. Están documentados. No son un silencio: el resultado es un prefijo, o un error si más adelante hay una trama válida.

## Qué solo está probado con tests

- El `Storage` simulado (`Cairn.Crash`): dos puts sincronizados y una trama no sincronizada en modo `.torn` de 10 bytes conservan el prefijo de longitud 2; `.keep` da prefijo 2 o 3; dos tramas pendientes `[.zero, .keep]` lanzan `corrupt log`. `lake test` lo comprueba.
- Cortes de un log de 12 registros. El test recorre `sampleCuts` (los primeros 80 bytes, los bordes de cada trama de 4096, y los desplazamientos 17 y 40). La prueba cubre todos los índices.
- Fuzz de un log válido de tres registros, semilla `0xC0FFEE`, multiplicador `6364136223846793005`. 512 bits de la cabecera, 768 bits al principio del primer segmento, 200 bits al azar y 200 máscaras de byte distintas de cero. Total 1680. Resultado de esta ejecución:

```
fuzz [(detect, 1591), (torn, 89), (miss, 0), (forge, 0), (same, 0)]
cairn tests ok
```

`miss` habría aceptado los bytes alterados como los registros originales. `forge` habría producido una lista que no es un prefijo. Los dos quedaron en cero en este conjunto. Los 89 `torn` son prefijos y se truncan. Es una medición de las clases cubiertas, no una prueba de toda corrupción. Una ráfaga de 4096 bytes no es una ráfaga de ≤ 32 bits.

- `strace` en esta máquina Linux. Dos puts (`cairn-crash-writer`): `open` con `O_TRUNC`, `write` de 4096, `fdatasync`, `open` del directorio con `O_DIRECTORY`, `fsync`, y un `fdatasync` después de cada put. Compactación (`cairn-sync-trace`): `fdatasync` del temporal `path.cairn-tmp`, `rename` sobre el fichero vivo, `fsync` del directorio. La ruta macOS no se ejecutó.
- `kill -9` (`scripts/crash_demo.sh`, espera 0.3 s, 2000 claves pedidas): `recovered 147 keys, a prefix of the committed writes`. Eso mata el proceso. No corta la luz.

## Qué sigue fuera

- Un apagón físico. No se puede provocar en esta VM.
- `dm-flakey`. Hay `sudo` y dispositivos `loop`, pero no hay `dmsetup` ni `modprobe`, así que el módulo no se cargó.
- Un disco que responde al `fsync` sin haber escrito.
- Un sector físico mayor de 4096 bytes.
- Colisiones del CRC fuera de las clases demostradas, y dos bits a distancia mayor de 31.
- Varios escritores concurrentes.
- La rama `F_FULLFSYNC` de macOS, compilada solo con `__APPLE__`.

## Decisión del checksum

Se midió CRC-32 reflejado (`crc32`, el de los registros), `sum32` (el de las tramas), CRC-64-ECMA (`sum64`, polinomio `0x42F0E1EBA9EA3693`, init 0, sin xor final) y `mix128` (mezcla de multiplicar y xor en Lean puro: no es xxHash, no es BLAKE, no es un hash criptográfico). `sum64` y `mix128` no se escriben en el disco. La prueba de ráfaga es de `sum32`. Pasar el disco a un checksum sin esa prueba no compensa: en esta build los tres CRC salen al mismo coste, y `mix128` es más lento.

## Cómo se verificó, y los números

Máquina: 4 vCPU, `Intel(R) Xeon(R) Processor`, 2400 MHz según `/proc/cpuinfo`, ext4 en `/dev/vdc`.

`lake test` terminó en unos 1,1 s con `cairn tests ok` y el fuzz de arriba.

`cairn-durable-bench` no forma parte de `lake test`. Una ejecución, tres repeticiones. `sync-per-commit` son 100 `putStr`, cada uno con su `fdatasync`. Los grupos son 256 puts en segmentos de 8, 32 o 128 registros, un `fdatasync` por segmento. El checksum pliega 4096 bytes, 401 veces, y conserva el digest.

```
sync-per-commit n=100  282891ns/op 3534ops/s  166494ns/op 6006ops/s  322710ns/op 3098ops/s
group-8 n=256  33787ns/op 29597ops/s  35793ns/op 27938ops/s  48203ns/op 20745ops/s
group-32 n=256  25519ns/op 39186ops/s  20269ns/op 49336ops/s  17335ns/op 57686ops/s
group-128 n=256  6133ns/op 163052ops/s  10651ns/op 93887ops/s  11090ns/op 90171ops/s
checksum crc32 bytes=4096 reps=401  8ns/byte sink=3563452679
checksum sum32 bytes=4096 reps=401  8ns/byte sink=1106225055
checksum sum64 bytes=4096 reps=401  8ns/byte sink=169702108233435973
checksum mix128 bytes=4096 reps=401  12ns/byte sink=16824937962598406005
```

Las tres repeticiones de cada checksum imprimieron los mismos nanos y el mismo sink; aquí queda una línea. En esta pasada un put con `fdatasync` costó entre 166 µs y 323 µs. Un `sum32` de 4096 bytes sale a unos 33 µs. El group commit baja el coste por put porque la barrera se paga una vez por segmento. La latencia de `fdatasync` en esta VM se mueve de una pasada a otra; no es un disco que espere a medio estable, y no vale para otra máquina.

No hay número de un corte de luz real, porque no se hizo.
