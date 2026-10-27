/-
In-process cluster shape.

One shard is one log. `resync` points every follower at the head replica.
`moved` builds the log a shard should carry after a split: the compaction of
that shard's entries. Replaying it is the projection (`move_replays`).

The running cluster is `ShardSet`: one `DB` per shard, no global mutex.
`Directory` says which host owns a shard. `planCatchup` is the per-shard log
route a transport would send. This file stays the pure catch-up of a replica
list.

Cross-shard batches are rejected by `sameShard` at commit time. There is no
two-phase commit and no cross-shard transaction.
-/

import Cairn.Replica
import Cairn.Router

namespace Cairn

def resync (rs : List Replica) : List Replica :=
  match rs with
  | [] => []
  | leader :: rest => leader :: rest.map (fun f => catchUp f leader)

theorem resync_nil : resync [] = [] := rfl

theorem resync_states (leader : Replica) (rest : List Replica)
    (h : ∀ f, f ∈ rest → f.epochGen = leader.epochGen) :
    ∀ f, f ∈ resync (leader :: rest) → f.state = leader.state := by
  intro f hf
  simp only [resync, List.mem_cons] at hf
  cases hf with
  | inl heq =>
      cases heq
      rfl
  | inr hf =>
      simp only [List.mem_map] at hf
      obtain ⟨g, hg, rfl⟩ := hf
      exact catchUp_state g leader (h g hg)

/-- Records that should live on shard `s` after a split, as their own log. -/
def moved (m : Map) (bounds : List Bytes) (s : Nat) (gen : Nat) : Replica where
  epochGen := gen
  log := compactRecords (inShard bounds s m) 0

theorem moved_state (m : Map) (h : NodupKeys m) (bounds : List Bytes) (s : Nat) (gen : Nat) :
    entries (moved m bounds s gen).state = entries (inShard bounds s m) :=
  move_replays bounds s m h 0

end Cairn
