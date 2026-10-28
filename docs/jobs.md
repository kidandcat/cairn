# Jobs, TTL y change feed

Informe de la fase 2. La cola es persistente. El outbox es un solo lote. El feed es el log de un shard.

## Restricción

`Queue.enqueueWith` mete las ops del llamador y el `put` del job en un mismo lote. Si `sameShard` es falso, lanza `outbox crossed a shard` y no publica nada. Con un solo shard siempre cabe. Con bounds, la clave del job (prefijo `03`) y la clave del cambio tienen que caer en el mismo id. No hay transacción entre shards.

El índice de TTL es el orden de la clave bajo el prefijo `04` (caducidad en big-endian, luego el id). `Ttl.sweep` borra las que tienen caducidad `≤ now` y se detiene en la primera posterior.

`ShardSet.watch shard fromLsn prefix` lee el log de ese shard. El orden es el de admisión de ese shard. No hay un orden entre shards.

`nack` reintenta con `Job.backoff` (potencia de dos, tope 65536) y, pasado el máximo de intentos, marca el job como muerto. El cron de esta fase es un intervalo: el llamador vuelve a encolar con `runAt = now + every`. No es una expresión de calendario.

## Demostrado

- `Job.claim_spec`: dado el estado, el claim es la fila que `pick` elige y el lease `now + leaseFor`.
- `Job.claim_blocks`: un segundo `pick` antes de que venza ese lease no devuelve el mismo id.
- `Job.enqueue_idem`: si la clave de idempotencia ya está, no se añade otro job.
- `Job.ack_gone`: el ack quita ese id.
- `outbox_both`: tras el lote de dos `put`, las dos claves están.
- `Feed.visible_mem`, `visible_since`, `visible_prefix`: el feed es exactamente las ops del log con `lsn ≥ from` y el prefijo.
- `Job.due_mem`: la fila de TTL vence exactamente cuando `expiry ≤ now`.

No está demostrado que dos `Task` no reclamen el mismo job: el modelo es secuencial. El runtime usa compare-and-set del valor. Tampoco está demostrada una cota del barrido.

## Probado con tests

`lake test` incluye el lease (no se entrega otra vez antes de tiempo, sí después), el outbox que cruza un bound y no escribe nada, el feed desde un LSN posterior, el barrido de una de dos caducidades, y cuatro tareas reclamando ocho jobs sin repetir. El fuzz sigue en detect 1591, torn 89, miss 0, forge 0, same 0.

`scripts/crash_demo.sh` imprimió `recovered 140 keys, a prefix of the committed writes`. `cairn-backend` imprimió `backend demo ok`.

`cairn-design-bench`, misma máquina (4 vCPU, Xeon 2400 MHz, ext4 `/dev/vdc`), tres repeticiones, sin promediar. `mem-claim-100` encola 100 jobs fuera del reloj y luego los reclama:

```
mem-claim-100 ops=100  178963ns/op 5587ops/s  181739ns/op 5502ops/s  179097ns/op 5583ops/s
```

Cerca de 0.18 ms por claim: cada uno vuelve a recorrer el prefijo. `mem-prefix-pages` en la misma pasada: 1006, 883 y 917 ns/op.
