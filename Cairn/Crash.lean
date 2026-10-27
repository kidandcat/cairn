/-
Power-loss images of an unsynced tail.

`stable` is the bytes covered by completed `sync`s. `pending` is what the
process has written since then. A crash may keep any sector-prefix of
`stable ++ pending` (the file ends early). That case is `Tail.take`, and
`recovery_keeps_synced` says the recovered records contain every synced
group and are a prefix of what was submitted.

A crash may also keep a subset of the unsynced sectors in place: a missing
sector stays zero, it is not shifted. `crashImage` builds that image.
`laterFrame` turns a zero hole with a valid frame after it into `.corrupt`,
so open fails instead of silently dropping the hole. A zero tail after the
last complete frame is a torn tail and is truncated.
-/

import Cairn.FileFmt
import Cairn.Store

namespace Cairn

inductive SectorFate where
  | keep
  | zero
  | torn (n : Nat)
  deriving Repr, BEq

def chunkBy : Nat → Bytes → List Bytes
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, bs =>
      if bs.length ≤ blockSize then
        [bs]
      else
        bs.take blockSize :: chunkBy fuel (bs.drop blockSize)

def chunks (bs : Bytes) : List Bytes :=
  chunkBy (bs.length + 1) bs

def applyFate (chunk : Bytes) : SectorFate → Bytes
  | .keep => chunk
  | .zero => List.replicate chunk.length 0
  | .torn n =>
      let k := min n chunk.length
      chunk.take k ++ List.replicate (chunk.length - k) 0

def applyFates (bs : Bytes) (fates : List SectorFate) : Bytes :=
  let cs := chunks bs
  let paired := cs.zip fates
  let kept := paired.foldl (fun acc p => acc ++ applyFate p.1 p.2) []
  let missing := cs.drop fates.length
  missing.foldl (fun acc c => acc ++ List.replicate c.length 0) kept

/-- Synced bytes, then whatever subset of the unsynced sectors landed. -/
def crashImage (stable pending : Bytes) (fates : List SectorFate) : Bytes :=
  stable ++ applyFates pending fates

inductive Tail where
  | lost
  | take (n : Nat)

def tailImage (stable pending : Bytes) : Tail → Bytes
  | .lost => stable
  | .take n => (stable ++ pending).take n

structure FaultState where
  stable : IO.Ref Bytes
  pending : IO.Ref Bytes

def FaultState.new : IO FaultState := do
  let stable ← IO.mkRef ([] : Bytes)
  let pending ← IO.mkRef ([] : Bytes)
  return { stable, pending }

def FaultState.store (s : FaultState) : Store where
  readAll := do
    return (← s.stable.get) ++ (← s.pending.get)
  append b := s.pending.modify (· ++ b)
  sync := do
    let p ← s.pending.get
    s.stable.modify (· ++ p)
    s.pending.set []
  replaceAll b := do
    s.stable.set b
    s.pending.set []

def FaultState.crash (s : FaultState) (fates : List SectorFate) : IO Bytes := do
  return crashImage (← s.stable.get) (← s.pending.get) fates

end Cairn
