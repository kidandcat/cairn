/-
One writer per shard, through `ShardSet`. Not part of `lake test`.

Each row is three fresh runs. `file-*` calls `sync` (`fdatasync` on Linux)
once per put, or once per group. `mem-*` is the same router on the memory
backend, whose `sync` returns immediately. Opens happen before the clock.
-/

import Cairn

open Cairn System

def boundsOf (n : Nat) : List Bytes :=
  (List.range (n - 1)).map fun i => [UInt8.ofNat (i + 1)]

def fitKey (shard i : Nat) : FitBytes where
  bytes := [UInt8.ofNat shard, UInt8.ofNat (i % 251), UInt8.ofNat ((i / 251) % 251), 0]
  hlen := by
    rw [List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
    decide

def showRow (name : String) (ops : Nat) (run : IO Nat) : IO Unit := do
  let mut line := s!"{name} ops={ops}"
  for _ in [0:3] do
    let dt ← run
    let per := if ops == 0 then 0 else dt / ops
    let rate := if per == 0 then 0 else 1000000000 / per
    line := line ++ s!"  {per}ns/op {rate}ops/s"
  IO.println line

def runShards (file : Bool) (nShards puts : Nat) : IO Nat := do
  let dir ← IO.FS.createTempDir
  try
    let epoch : Epoch := { gen := 0, bounds := boundsOf nShards }
    let s ← if file then ShardSet.openFiles dir epoch else ShardSet.openMem epoch
    let t0 ← IO.monoNanosNow
    let mut tasks : List (Task (Except IO.Error Unit)) := []
    for shard in [0:nShards] do
      let t ← IO.asTask (prio := .dedicated) do
        for i in [0:puts] do
          s.put (fitKey shard i) (fitKey shard i)
      tasks := t :: tasks
    for t in tasks do
      match ← IO.wait t with
      | .ok () => pure ()
      | .error e => throw e
    let t1 ← IO.monoNanosNow
    s.close
    return t1 - t0
  finally
    IO.FS.removeDirAll dir

def runGroup (nShards puts group : Nat) : IO Nat := do
  let dir ← IO.FS.createTempDir
  try
    let epoch : Epoch := { gen := 0, bounds := boundsOf nShards }
    let s ← ShardSet.openFiles dir epoch
    let t0 ← IO.monoNanosNow
    let mut tasks : List (Task (Except IO.Error Unit)) := []
    for shard in [0:nShards] do
      let t ← IO.asTask (prio := .dedicated) do
        let mut i := 0
        while i < puts do
          let mut batches : List (List Op) := []
          let mut j := 0
          while j < group && i + j < puts do
            batches := batches ++ [[.put (fitKey shard (i + j)) (fitKey shard (i + j))]]
            j := j + 1
          s.commitMany batches
          i := i + group
      tasks := t :: tasks
    for t in tasks do
      match ← IO.wait t with
      | .ok () => pure ()
      | .error e => throw e
    let t1 ← IO.monoNanosNow
    s.close
    return t1 - t0
  finally
    IO.FS.removeDirAll dir

/-- Four tasks, one shard, one mutex. Keys stay on shard 0. -/
def runContended (tasksN puts : Nat) : IO Nat := do
  let dir ← IO.FS.createTempDir
  try
    let s ← ShardSet.openFiles dir Epoch.single
    let t0 ← IO.monoNanosNow
    let mut tasks : List (Task (Except IO.Error Unit)) := []
    for w in [0:tasksN] do
      let t ← IO.asTask (prio := .dedicated) do
        for i in [0:puts] do
          s.put (fitKey 0 (w * puts + i)) (fitKey 0 (w * puts + i))
      tasks := t :: tasks
    for t in tasks do
      match ← IO.wait t with
      | .ok () => pure ()
      | .error e => throw e
    let t1 ← IO.monoNanosNow
    s.close
    return t1 - t0
  finally
    IO.FS.removeDirAll dir

/-- Page a thousand memory keys. Puts are outside the clock. -/
def runPrefixPages : IO Nat := do
  let s ← ShardSet.openMem Epoch.single
  for i in [0:1000] do
    s.put (fitKey 0 i) (fitKey 0 i)
  let t0 ← IO.monoNanosNow
  let mut after : Option FitBytes := none
  let mut seen := 0
  for _ in [0:25] do
    let (rows, cur) ← s.prefix [0] after 40
    seen := seen + rows.length
    after := cur
  let t1 ← IO.monoNanosNow
  s.close
  if seen != 1000 then
    throw (IO.userError s!"prefix saw {seen}")
  return t1 - t0

def runClaims : IO Nat := do
  let s ← ShardSet.openMem Epoch.single
  for i in [0:100] do
    let t := 1000 + i
    if ht : t < 2 ^ 48 then
      Queue.enqueue s 1 0 ⟨t, 1, ht, by decide⟩ [UInt8.ofNat (i % 200)]
  let t0 ← IO.monoNanosNow
  let mut n := 0
  for _ in [0:100] do
    match ← Queue.claim s 0 1000000 with
    | some _ => n := n + 1
    | none => pure ()
  let t1 ← IO.monoNanosNow
  s.close
  if n != 100 then
    throw (IO.userError s!"claimed {n}")
  return t1 - t0

def main : IO UInt32 := do
  let cpu ← IO.FS.readFile "/proc/cpuinfo"
  let model := (cpu.splitOn "\n").find? (·.startsWith "model name") |>.getD "model name: unknown"
  IO.println model
  let puts := 100
  for n in [1, 2, 4] do
    showRow s!"file-shards-{n}" (n * puts) (runShards true n puts)
  for n in [1, 2, 4] do
    showRow s!"mem-shards-{n}" (n * puts) (runShards false n puts)
  let gputs := 128
  showRow "file-group-32-shards-4" (4 * gputs) (runGroup 4 gputs 32)
  showRow "file-contended-1-tasks-4" (4 * puts) (runContended 4 puts)
  showRow "mem-prefix-pages" 1000 runPrefixPages
  showRow "mem-claim-100" 100 runClaims
  return 0
