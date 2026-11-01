import MultiSplay.RichJoinPlacements
import MultiSplay.RichJoinTopDown

/-!
# A stable, fully realized common join

The constructed output satisfies the exact `State.Represents` interface used
by the existing chronological splay analysis. Its strict operation trace starts
from the disjoint sum of the two current interface states and retains every
old block. The new boundary costs two insertions and four value increases.
-/

namespace MultiSplay.RichJoin

open Splay.Tree (BST)
open Splay.Rank (Snapshot)
open Splay.Lazy (State Block Element Side)
open Splay.Lazy.Canonical
open JoinIntervals (leftEmbedding rightEmbedding)

variable {l r : Nat}

theorem growingTopmost {params : Splay.Interface.Parameters}
    (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r) (a : State l) (b : State r)
    (aRep : a.Represents params (Snapshot.ofTree left).withTruePriority sl)
    (bRep : b.Represents params (Snapshot.ofTree right).withTruePriority sr) :
    (state left right sl sr a b).GrowingTopmost := by
  intro id
  dsimp only
  intro growing
  have member := List.get_mem (state left right sl sr a b).blocks id
  generalize blockEq : (state left right sl sr a b).blocks.get id = block at *
  change block ∈ _ ++ _ ++ _ at member
  rcases List.mem_append.mp member with old | fresh
  · rcases List.mem_append.mp old with oldLeft | oldRight
    · obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp oldLeft
      obtain ⟨originalId, originalEq⟩ := List.mem_iff_get.mp originalMem
      have oldGrowing : (a.blocks.get originalId).mode = .growing := by simpa only [originalEq, BlockEmbedding.block] using growing
      obtain ⟨suffix, oldTop⟩ := aRep.growingTopmost originalId oldGrowing
      rw [originalEq] at oldTop
      refine ⟨suffix.map (leftEmbedding l r), ?_⟩
      change (state left right sl sr a b).view.topDown (leftEmbedding l r original.owner) original.side = _
      rw [left_topDown left right sl sr a b aRep bRep, oldTop, List.map_append]
      rfl
    · obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp oldRight
      obtain ⟨originalId, originalEq⟩ := List.mem_iff_get.mp originalMem
      have oldGrowing : (b.blocks.get originalId).mode = .growing := by simpa only [originalEq, BlockEmbedding.block] using growing
      obtain ⟨suffix, oldTop⟩ := bRep.growingTopmost originalId oldGrowing
      rw [originalEq] at oldTop
      refine ⟨suffix.map (rightEmbedding l r), ?_⟩
      change (state left right sl sr a b).view.topDown (rightEmbedding l r original.owner) original.side = _
      rw [right_topDown left right sl sr a b aRep bRep, oldTop, List.map_append]
      rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl | rfl
    · exact ⟨[], by simpa only [rootBlock, List.append_nil] using pivot_topDown left right sl sr a b aRep bRep .left⟩
    · exact ⟨[], by simpa only [rootBlock, List.append_nil] using pivot_topDown left right sl sr a b aRep bRep .right⟩

theorem stable {params : Splay.Interface.Parameters}
    (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r) (a : State l) (b : State r)
    (aRep : a.Represents params (Snapshot.ofTree left).withTruePriority sl)
    (bRep : b.Represents params (Snapshot.ofTree right).withTruePriority sr)
    (growingLimit : 2 ≤ params.growingLimit) (valueCap : 3 ≤ params.valueBound) :
    (state left right sl sr a b).Stable params :=
  ⟨valid left right sl sr a b aRep bRep growingLimit valueCap,
   complete left right sl sr a b aRep bRep, canonicalHeapView_heapOrdered _ _,
   oneGrowingPerSide left right sl sr a b aRep.oneGrowingPerSide bRep.oneGrowingPerSide,
   growingTopmost left right sl sr a b aRep bRep, valuesRealizeGaps left right sl sr a b aRep bRep⟩

/-- This output can be passed directly to the existing request and comparison
rotation realizations. The premise is the two current representations, not a
new canonical initialization of either component. -/
theorem represents {params : Splay.Interface.Parameters}
    (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r) (a : State l) (b : State r)
    (aRep : a.Represents params (Snapshot.ofTree left).withTruePriority sl)
    (bRep : b.Represents params (Snapshot.ofTree right).withTruePriority sr)
    (growingLimit : 2 ≤ params.growingLimit) (valueCap : 3 ≤ params.valueBound) :
    (state left right sl sr a b).Represents params
      (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr) :=
  ⟨stable left right sl sr a b aRep bRep growingLimit valueCap, rfl⟩

end MultiSplay.RichJoin
