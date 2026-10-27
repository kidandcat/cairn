import Cairn

open Cairn System

def rate (label : String) (ops ms : Nat) : String :=
  if ms = 0 then
    s!"{label}: {ops} ops in 0 ms"
  else
    s!"{label}: {ops} ops in {ms} ms ({ops * 1000 / ms} ops/s)"

def main : IO UInt32 := do
  let dir ← IO.FS.createTempDir
  try
    let path := FilePath.mk (dir.toString ++ "/bench")
    let db ← DB.openFile path
    let t0 ← IO.monoMsNow
    for i in [0:1000] do
      db.putStr (toString i) "v"
    let t1 ← IO.monoMsNow
    for i in [0:1000] do
      let _ ← db.getStr (toString i)
    let t2 ← IO.monoMsNow
    IO.println (rate "file put" 1000 (t1 - t0))
    IO.println (rate "file get" 1000 (t2 - t1))
    let mut tasks : List (Task (Except IO.Error Unit)) := []
    for _ in [0:4] do
      let t ← IO.asTask (prio := .dedicated) do
        for _ in [0:2000] do
          let _ ← db.getStr "0"
      tasks := t :: tasks
    let t3 ← IO.monoMsNow
    for t in tasks do
      match ← IO.wait t with
      | .ok () => pure ()
      | .error e => throw e
    let t4 ← IO.monoMsNow
    IO.println (rate "concurrent get (4 tasks x 2000)" 8000 (t4 - t3))
    db.close
  finally
    IO.FS.removeDirAll dir
  return 0
