# Copias y mensajes entre shards

No es una transacción entre shards. No hay 2PC ni consenso.

Una clave tiene un shard dueño: el de `shardOf`. La escritura que manda es la de ese home, dentro de `transact`. En el mismo lote se dejan avisos de outbox, uno por shard destino. El destino los aplica después, en el orden del ticket (LSN del home e índice dentro del lote). Si el proceso muere entre el commit del home y el propagador, el outbox sigue en el fichero del home y la marca de progreso del destino no ha avanzado: al reanudar se aplica esa vez, y una segunda pasada no lo repite.

## Qué ve un lector

`ShardSet.get` lee el home. Está al día de ese shard.

`readCopy home dest key` lee el fichero del destino. Puede ir detrás. Devuelve el valor, el ticket aplicado y el `nextLsn` del home (`homeTip`). Si `applied` va por detrás de los tickets que el home ya escribió, la copia está vieja. Dos lecturas, una al home y otra a la copia, pueden discrepar. Dos copias pueden discrepar entre sí hasta que ambos propagadores alcanzan el mismo ticket. No hay un snapshot global.

El outbox y la marca de progreso se guardan con `Tx.putLocal` en el fichero del shard que ejecuta el lote. `shardOf` no los enruta. El propagador lee ese fichero con `localPrefix` y `localGet`.

## Mensajes y sagas

`Tx.enqueue dest notice` mete un mensaje en el outbox del shard que tiene el lock. El destino lo recibe en `propagate`, dentro de su propio `transact`, una vez por ticket. Es at-least-once en el sentido de que un crash reintenta; la marca hace que el efecto se aplique una vez.

Una transferencia de la cuenta `a` (shard 0) a `z` (shard 1): se debita `a` y se encola el crédito. Si `z` está congelada, el manejador no acredita y encola la compensación; el propagador de vuelta devuelve el importe a `a`. Si el crédito sí entra, un segundo `propagate` no lo suma otra vez.

## `commitCross`

`commit` sigue rechazando un lote que cruza shards. `commitCross` parte el lote: las ops del home se escriben ahí, el resto sale como avisos. El resultado es `.local` o `.eventual home destinos`. `.eventual` no es atómico: el destino puede no haber aplicado nada todavía. `commitCross ops true` es el modo estricto y lanza `cross-shard batch` sin escribir.

## Demostrado

- `applyTicket_idem`: el mismo ticket dos veces es igual que una.
- `numbered_fold`: los tickets `start, start+1, …` reaplican las ops en ese orden y la marca queda en el último.
- `converge`: si la copia empieza vacía y aplica esos tickets, coincide con `applyBatch` del log del home.

No está demostrado el mutex, ni que dos tareas no se pisen fuera del modelo, ni que `readCopy` esté a menos de un ticket del home. El retraso es un número que devuelve la lectura, no una cota.

## Probado con tests

`lake test`: `cairn tests ok`, fuzz detect 1591, torn 89, miss 0, forge 0, same 0. Se cierra el proceso después del commit del home y antes de propagar, se reabre el fichero, la copia llega, y una segunda pasada aplica 0. Cuatro tareas propagan el mismo outbox y la copia queda en el valor del home. La saga congelada compensa; la saga libre acredita una vez. `scripts/crash_demo.sh`: `recovered 156 keys, a prefix of the committed writes`. `cairn-backend`: `backend demo ok`.

`cairn-copy-bench`, memoria, el relleno de 1000 `commitCross` fuera del reloj, tres repeticiones del `propagate`, nanosegundos totales, sin promediar. 4 vCPU, Xeon 2400 MHz, ext4 `/dev/vdc`:

```
propagate n=1000  58276448ns  36116345ns  23830012ns
```
