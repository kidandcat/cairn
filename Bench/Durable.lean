/-
Sync and checksum cost. Not part of `lake test`.

One process, this machine, `IO.monoNanosNow`. A rep is a fresh file.
`sync` here is `fdatasync` (Linux) or `F_FULLFSYNC` (macOS), once per commit
or once per group.
-/

import Cairn
import Cairn.WideSum

open Cairn

def nanos (k : IO Unit) : IO Nat := do
  let t0 ← IO.monoNanosNow
  k
  let t1 ← IO.monoNanosNow
  return t1 - t0

def repPuts (n : Nat) : IO Nat := do
  let dir ← IO.FS.createTempDir
  try
    let db ← DB.openFile (dir.toString ++ "/db")
    let dt ← nanos do
      for i in [0:n] do
        db.putStr (toString i) "v"
    db.close
    return dt
  finally
    IO.FS.removeDirAll dir

def repGroup (n group : Nat) : IO Nat := do
  let dir ← IO.FS.createTempDir
  try
    let db ← DB.openFile (dir.toString ++ "/db")
    let dt ← nanos do
      let mut i := 0
      while i < n do
        let mut batches : List (List Op) := []
        let mut j := 0
        while j < group && i + j < n do
          match FitBytes.ofString? (toString (i + j)), FitBytes.ofString? "v" with
          | some k, some v => batches := batches ++ [[.put k v]]
          | _, _ => pure ()
          j := j + 1
        db.commitMany batches
        i := i + group
    db.close
    return dt
  finally
    IO.FS.removeDirAll dir

def mb (n : Nat) : Nat :=
  if n == 0 then 0 else 1000000000 / n

def showRep (name : String) (n : Nat) (run : IO Nat) : IO Unit := do
  let mut line := s!"{name} n={n}"
  for _ in [0:3] do
    let dt ← run
    let per := if n == 0 then 0 else dt / n
    line := line ++ s!"  {per}ns/op {mb per}ops/s"
  IO.println line

def checksumBytes (n : Nat) : Bytes :=
  (List.range n).map fun i => UInt8.ofNat (i % 251)

def timeSum (n : Nat) (f : Bytes → Unit) : IO Unit := do
  let bs := checksumBytes n
  let mut line := s!"checksum bytes={n}"
  for _ in [0:3] do
    let dt ← nanos (pure (f bs))
    let per := if n == 0 then 0 else dt / n
    line := line ++ s!"  {per}ns/byte"
  IO.println line

def main : IO Unit := do
  let cpu ← IO.FS.readFile "/proc/cpuinfo"
  let model := (cpu.splitOn "model name").getD 1 ""
  IO.println (model.take 80)
  showRep "sync-per-commit" 100 (repPuts 100)
  showRep "group-8" 256 (repGroup 256 8)
  showRep "group-32" 256 (repGroup 256 32)
  showRep "group-128" 256 (repGroup 256 128)
  let n := 4096
  timeSum n fun bs => let _ := crc32 bs; ()
  timeSum n fun bs => let _ := sum32 bs; ()
  timeSum n fun bs => let _ := sum64 bs; ()
  timeSum n fun bs => let _ := mix128 bs; ()
