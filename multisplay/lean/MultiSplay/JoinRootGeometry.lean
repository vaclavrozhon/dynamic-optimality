import MultiSplay.JoinPriority

/-!
# The two root intervals at a common split boundary

These facts concern the two tree shapes alone and apply to every current lazy
history representing them. In particular, they do not require that history to
have been produced by the most recent common join.
-/

namespace MultiSplay.JoinRootGeometry

open Splay.Tree (BST)
open Splay.Rank (Snapshot External)
open Splay.Lazy (HeapView Side)
open Splay.Lazy.Canonical
open JoinIntervals (leftEmbedding rightEmbedding)

variable {l r : Nat}

theorem parent_pivot_iff (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (element : External (0 + l + 1 + r)) :
    canonicalParent (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree sl sr) element = some (JoinRanks.pivot l r) ↔
      element = leftEmbedding l r (canonicalRoot (Snapshot.ofTree left) sl) ∨
      element = rightEmbedding l r (canonicalRoot (Snapshot.ofTree right) sr) := by
  constructor
  · intro parent
    simp only [canonicalParent, Option.map_eq_some_iff] at parent
    obtain ⟨edge, found, ownerEq⟩ := parent
    obtain ⟨member, childEq⟩ := incomingEdge?_some_mem _ _ found
    rw [JoinRanks.full_edges] at member
    rcases List.mem_append.mp member with earlier | rightMem
    · rcases List.mem_append.mp earlier with roots | leftMem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at roots
        rcases roots with rfl | rfl
        · exact Or.inl (childEq.symm.trans (JoinRanks.root_left_child left right sl sr))
        · exact Or.inr (childEq.symm.trans (JoinRanks.root_right_child left right sl sr))
      · obtain ⟨old, _, rfl⟩ := List.mem_map.mp leftMem
        exact False.elim (JoinIntervals.left_ne_pivot l r old.owner ownerEq)
    · obtain ⟨old, _, rfl⟩ := List.mem_map.mp rightMem
      exact False.elim (JoinIntervals.right_ne_pivot l r old.owner ownerEq)
  · rintro (rfl | rfl)
    · exact JoinHeap.left_root_parent left right sl sr
    · exact JoinHeap.right_root_parent left right sl sr

theorem priority_parent_pivot_iff (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (element : External (0 + l + 1 + r)) :
    canonicalParent (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr) element = some (JoinRanks.pivot l r) ↔
      element = leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl) ∨
      element = rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr) := by
  rw [(JoinPriority.structure_eq _ (JoinRanks.tree sl sr)).2.1,
    (JoinPriority.structure_eq (Snapshot.ofTree left) sl).1,
    (JoinPriority.structure_eq (Snapshot.ofTree right) sr).1]
  exact parent_pivot_iff left right sl sr element

theorem priority_topDown (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r) (side : Side) :
    (canonicalHeapView (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)).topDown (JoinRanks.pivot l r) side =
      [match side with
       | .left => leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl)
       | .right => rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr)] := by
  have leftSide : canonicalSide (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)
      (leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl)) = .left := by
    rw [(JoinPriority.structure_eq _ (JoinRanks.tree sl sr)).2.2, (JoinPriority.structure_eq (Snapshot.ofTree left) sl).1]
    exact JoinIntervals.left_root_side left right sl sr
  have rightSide : canonicalSide (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)
      (rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr)) = .right := by
    rw [(JoinPriority.structure_eq _ (JoinRanks.tree sl sr)).2.2, (JoinPriority.structure_eq (Snapshot.ofTree right) sr).1]
    exact JoinIntervals.right_root_side left right sl sr
  have membership : ∀ element,
      element ∈ (canonicalHeapView (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)).topDown (JoinRanks.pivot l r) side ↔
      element ∈ [match side with
       | .left => leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl)
       | .right => rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr)] := by
    intro element
    rw [HeapView.mem_topDown_iff]
    change (canonicalParent _ _ element = _ ∧ canonicalSide _ _ element = side) ↔ _
    rw [priority_parent_pivot_iff]
    simp only [List.mem_singleton]
    cases side <;> constructor
    · rintro ⟨rfl | rfl, sideEq⟩
      · rfl
      · rw [rightSide] at sideEq
        cases sideEq
    · rintro rfl
      exact ⟨Or.inl rfl, leftSide⟩
    · rintro ⟨rfl | rfl, sideEq⟩
      · rw [leftSide] at sideEq
        cases sideEq
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, rightSide⟩
  cases side with
  | left => exact List.Pairwise.eq_of_mem_iff ((canonicalHeapView _ _).topDown_ordered _).1 (by simp) membership
  | right => exact List.Pairwise.eq_of_mem_iff ((canonicalHeapView _ _).topDown_ordered _).2 (by simp) membership

end MultiSplay.JoinRootGeometry
