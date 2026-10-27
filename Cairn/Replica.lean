/-
Primary/secondary catch-up on the record log.

A follower whose log is a prefix appends the missing suffix. Any other
follower with the same epoch installs the leader log wholesale: the leader
wins, and the follower's extra suffix is dropped. That is not a merge and not
Raft. Epoch mismatch leaves the follower untouched.

Compaction on a leader rewrites LSNs, so a follower cannot append across a
compaction boundary. It installs the compacted log (`installSnapshot`).
-/

import Cairn.Log
import Cairn.Transport

namespace Cairn

structure Replica where
  epochGen : Nat
  log : List Record

def Replica.state (r : Replica) : Map :=
  replay r.log

def Replica.truncate (r : Replica) (n : Nat) : Replica :=
  { r with log := r.log.take n }

/-- Byte-level crash: keep `n` bytes of the encoded log and decode. -/
def Replica.crashBytes (r : Replica) (n : Nat) : Except String Replica :=
  Except.map (fun log => { r with log := log }) (decodeFile ((encodeFile r.log).take n))

theorem crash_is_prefix (r : Replica) (n : Nat) (h : RecordsFit r.log) :
    ∃ k, Except.map Replica.state (r.crashBytes n) = .ok (replay (r.log.take k)) := by
  obtain ⟨k, hk⟩ := recovery_prefix r.log n h
  refine ⟨k, ?_⟩
  simp only [Replica.crashBytes]
  have hmap :
      Except.map Replica.state
          (Except.map (fun log => { epochGen := r.epochGen, log := log })
            (decodeFile ((encodeFile r.log).take n))) =
        Except.map replay (decodeFile ((encodeFile r.log).take n)) := by
    cases decodeFile ((encodeFile r.log).take n) with
    | ok rs => simp [Except.map, Replica.state]
    | error e => simp [Except.map]
  rw [hmap, hk]

def catchUp (f leader : Replica) : Replica :=
  if f.epochGen != leader.epochGen then
    f
  else if f.log.isPrefixOf leader.log then
    let suffix := leader.log.drop f.log.length
    let applied := applyRpc f.epochGen f.log
      (.appendEntries leader.epochGen f.log.length suffix)
    { f with log := applied.2 }
  else
    let applied := applyRpc f.epochGen f.log (.installSnapshot leader.epochGen leader.log)
    { f with log := applied.2 }

theorem catchUp_state (f leader : Replica) (h : f.epochGen = leader.epochGen) :
    (catchUp f leader).state = leader.state := by
  unfold catchUp
  have hne : (f.epochGen != leader.epochGen) = false := by simp [h, bne]
  rw [hne, ite_eq_right (by decide)]
  by_cases hp : f.log.isPrefixOf leader.log = true
  · rw [ite_eq_left hp]
    have hpre : f.log <+: leader.log := List.isPrefixOf_iff_prefix.mp hp
    obtain ⟨suf, hsuf⟩ := hpre
    have hdrop : leader.log.drop f.log.length = suf := by
      rw [← hsuf, List.drop_left]
    simp [applyRpc, h, hdrop, Replica.state, hsuf]
  · rw [ite_eq_right hp]
    simp [applyRpc, h, Replica.state]

theorem prefix_log_catchup (leader : Replica) (k : Nat) :
    (catchUp { leader with log := leader.log.take k } leader).state = leader.state :=
  catchUp_state _ _ rfl

theorem truncate_catchup (leader : Replica) (n : Nat) :
    (catchUp (leader.truncate n) leader).state = leader.state :=
  catchUp_state _ _ rfl

/-- Same epoch, then the follower log replays to the leader map. -/
theorem catchUp_replay (f leader : Replica) (h : f.epochGen = leader.epochGen) :
    replay (catchUp f leader).log = replay leader.log := by
  simpa [Replica.state] using catchUp_state f leader h

end Cairn
