# Actores, uno por shard

No es un runtime de actores ni un actor por entidad. Cada shard, si se llama a `Actor.spawn`, tiene un bucle y un buzón acotado (`Std.Channel`, capacidad `cap`). El buzón durable es el outbox de las copias: `propagate` aplica un aviso dentro de un `transact` y guarda la marca de progreso en ese mismo lote.

## Por qué no hay llamada síncrona

`ShardSet.send dst msg` vuelve cuando el aviso está en el log del origen y, si el actor destino existe, cuando el buzón en memoria acepta un despertar. No espera el efecto. Una respuesta es otro `send` de vuelta. Si el emisor esperara dentro de su turno, y el destino estuviera esperando al emisor, los dos bucles se quedarían parados. Por eso no hay petición síncrona entre actores.

## Lecturas

No entran en la cola. `ShardSet.get` sigue siendo un `Ref.get` de una foto inmutable.

## Fallos

Si el manejador lanza, el lote no se publica y la marca no avanza. El bucle lo anota, duerme `intentos * 2` milisegundos y vuelve a leer el log. A los `maxAttempts` fallos, el aviso de cabeza se copia a una clave de fallidos (`deadKey`) y la marca lo salta. Un mensaje venenoso no atasca el shard.

`Actor.spawn shard handler` arranca ese bucle. El propagador de copias y la saga son el mismo `propagate`: el handler del actor es el de la saga.

## Demostrado

- `ActorModel.process_one`: procesar un mensaje es `applyOp`, un lote de una op.
- `ActorModel.process_fold`: el buzón en orden es el pliegue de esos lotes.
- `CopyModel.applyTicket_idem`, `numbered_fold`, `converge`: la idempotencia, el orden por origen y la copia que alcanza al home, que este bucle reutiliza.

No está demostrado el `Channel`, el backoff, ni que `kill -9` corte solo un prefijo. Eso es el mismo modelo de fichero que el resto de cairn.

## Probado

`lake test`: `cairn tests ok`, fuzz detect 1591, torn 89, miss 0, forge 0, same 0. El buzón de capacidad 1 rechaza el tercer `trySend` y un `send` bloqueado sigue cuando se libera un hueco. Tres mensajes de un origen quedan en orden `[0,1,2]`. Un manejador que lanza dos veces y a la tercera escribe, termina escribiendo. Un veneno pasa a la cola de fallidos y el mensaje siguiente se aplica. Cuatro tareas envían a la vez y las 20 claves aparecen una vez. Cerrar el fichero y reabrirlo no reaplica. `Demo/Backend` manda un ping y lee el pong con `get`. `scripts/actor_crash.sh` imprimió `actor recovered 40 notices, applied once` después de `kill -9`.

`cairn-actor-bench`, memoria, 1000 avisos escritos fuera del reloj, tres drenados, nanosegundos totales, sin promediar. 4 vCPU, Xeon 2400 MHz, ext4 `/dev/vdc`:

```
actor-drain n=1000  30174778ns  23558303ns  23487820ns
```
