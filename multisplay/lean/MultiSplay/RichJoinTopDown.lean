import MultiSplay.RichJoin

/-! # Existing top-down orders survive the common join -/

namespace MultiSplay.RichJoin

open Splay.Tree (BST)
open Splay.Rank (Snapshot)
open Splay.Lazy (State HeapView Element Side)
open Splay.Lazy.Canonical
open JoinIntervals (leftEmbedding rightEmbedding)

variable {l r : Nat}

theorem complete_attached {n : Nat} (state : State n) (complete : state.Complete)
    (owner : Element n) (side : Side) :
    state.view.attachedTopDown state.allElements owner side = state.view.topDown owner side := by
  unfold HeapView.attachedTopDown
  apply List.filter_eq_self.mpr
  intro element member
  apply decide_eq_true
  apply (complete element).mpr
  obtain ⟨parent, _⟩ := state.view.mem_topDown_iff.mp member
  rw [parent]
  exact Option.some_ne_none _

theorem left_topDown {params : Splay.Interface.Parameters}
    (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r) (a : State l) (b : State r)
    (aRep : a.Represents params (Snapshot.ofTree left).withTruePriority sl)
    (bRep : b.Represents params (Snapshot.ofTree right).withTruePriority sr)
    (owner : Element l) (side : Side) :
    (state left right sl sr a b).view.topDown (leftEmbedding l r owner) side =
      (a.view.topDown owner side).map (leftEmbedding l r) := by
  rw [← complete_attached _ (complete left right sl sr a b aRep bRep), attached_assignment]
  change (canonicalHeapView _ _).attachedTopDown _ _ _ = _
  rw [JoinPriority.attached_eq]
  have aRoot : canonicalRoot (Snapshot.ofTree left) sl ∉ a.allElements := by
    simpa only [aRep.view_eq, canonicalHeapView, (JoinPriority.structure_eq (Snapshot.ofTree left) sl).1] using aRep.stable.root_not_mem
  have bRoot : canonicalRoot (Snapshot.ofTree right) sr ∉ b.allElements := by
    simpa only [bRep.view_eq, canonicalHeapView, (JoinPriority.structure_eq (Snapshot.ofTree right) sr).1] using bRep.stable.root_not_mem
  change (JoinIntervals.view left right sl sr).attachedTopDown _ _ _ = _
  rw [JoinIntervals.left_children left right sl sr a.allElements b.allElements aRoot bRoot]
  rw [← JoinPriority.attached_eq, ← aRep.view_eq, complete_attached a aRep.complete]

theorem right_topDown {params : Splay.Interface.Parameters}
    (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r) (a : State l) (b : State r)
    (aRep : a.Represents params (Snapshot.ofTree left).withTruePriority sl)
    (bRep : b.Represents params (Snapshot.ofTree right).withTruePriority sr)
    (owner : Element r) (side : Side) :
    (state left right sl sr a b).view.topDown (rightEmbedding l r owner) side =
      (b.view.topDown owner side).map (rightEmbedding l r) := by
  rw [← complete_attached _ (complete left right sl sr a b aRep bRep), attached_assignment]
  change (canonicalHeapView _ _).attachedTopDown _ _ _ = _
  rw [JoinPriority.attached_eq]
  have aRoot : canonicalRoot (Snapshot.ofTree left) sl ∉ a.allElements := by
    simpa only [aRep.view_eq, canonicalHeapView, (JoinPriority.structure_eq (Snapshot.ofTree left) sl).1] using aRep.stable.root_not_mem
  have bRoot : canonicalRoot (Snapshot.ofTree right) sr ∉ b.allElements := by
    simpa only [bRep.view_eq, canonicalHeapView, (JoinPriority.structure_eq (Snapshot.ofTree right) sr).1] using bRep.stable.root_not_mem
  change (JoinIntervals.view left right sl sr).attachedTopDown _ _ _ = _
  rw [JoinIntervals.right_children left right sl sr a.allElements b.allElements aRoot bRoot]
  rw [← JoinPriority.attached_eq, ← bRep.view_eq, complete_attached b bRep.complete]

theorem root_links (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (a : State l) (b : State r) :
    let view := (state left right sl sr a b).view
    let x := leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl)
    let y := rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr)
    view.parent x = some (JoinRanks.pivot l r) ∧ view.side x = .left ∧
      view.parent y = some (JoinRanks.pivot l r) ∧ view.side y = .right := by
  dsimp only
  have doubled := JoinPriority.structure_eq (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree sl sr)
  change canonicalParent _ _ _ = _ ∧ canonicalSide _ _ _ = _ ∧ canonicalParent _ _ _ = _ ∧ canonicalSide _ _ _ = _
  rw [doubled.2.1, doubled.2.2, (JoinPriority.structure_eq (Snapshot.ofTree left) sl).1,
    (JoinPriority.structure_eq (Snapshot.ofTree right) sr).1]
  exact ⟨JoinHeap.left_root_parent left right sl sr, JoinIntervals.left_root_side left right sl sr,
    JoinHeap.right_root_parent left right sl sr, JoinIntervals.right_root_side left right sl sr⟩

theorem parent_pivot_iff {params : Splay.Interface.Parameters}
    (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r) (a : State l) (b : State r)
    (aRep : a.Represents params (Snapshot.ofTree left).withTruePriority sl)
    (bRep : b.Represents params (Snapshot.ofTree right).withTruePriority sr)
    (element : Element (0 + l + 1 + r)) :
    (state left right sl sr a b).view.parent element = some (JoinRanks.pivot l r) ↔
      element = leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl) ∨
      element = rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr) := by
  have doubled := JoinPriority.structure_eq (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree sl sr)
  constructor
  · intro parent
    have member := (complete left right sl sr a b aRep bRep element).mpr (by rw [parent]; exact Option.some_ne_none _)
    rw [allElements] at member
    rcases List.mem_append.mp member with old | fresh
    · rcases List.mem_append.mp old with oldLeft | oldRight
      · obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp oldLeft
        obtain ⟨block, blockMem, elementMem⟩ := State.mem_allElements_iff.mp originalMem
        have oldParent := (aRep.valid.2 block blockMem).parent_eq elementMem
        rw [aRep.view_eq] at oldParent
        change canonicalParent _ _ original = some block.owner at oldParent
        rw [(JoinPriority.structure_eq (Snapshot.ofTree left) sl).2.1] at oldParent
        have newParent := JoinHeap.left_parent left right sl sr oldParent
        change canonicalParent _ _ _ = _ at parent
        rw [doubled.2.1, newParent] at parent
        exact False.elim (JoinIntervals.left_ne_pivot l r block.owner (Option.some.inj parent))
      · obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp oldRight
        obtain ⟨block, blockMem, elementMem⟩ := State.mem_allElements_iff.mp originalMem
        have oldParent := (bRep.valid.2 block blockMem).parent_eq elementMem
        rw [bRep.view_eq] at oldParent
        change canonicalParent _ _ original = some block.owner at oldParent
        rw [(JoinPriority.structure_eq (Snapshot.ofTree right) sr).2.1] at oldParent
        have newParent := JoinHeap.right_parent left right sl sr oldParent
        change canonicalParent _ _ _ = _ at parent
        rw [doubled.2.1, newParent] at parent
        exact False.elim (JoinIntervals.right_ne_pivot l r block.owner (Option.some.inj parent))
    · simpa only [List.mem_cons, List.not_mem_nil, or_false] using fresh
  · intro roots
    rcases roots with rfl | rfl
    · exact (root_links left right sl sr a b).1
    · exact (root_links left right sl sr a b).2.2.1

theorem pivot_topDown {params : Splay.Interface.Parameters}
    (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r) (a : State l) (b : State r)
    (aRep : a.Represents params (Snapshot.ofTree left).withTruePriority sl)
    (bRep : b.Represents params (Snapshot.ofTree right).withTruePriority sr) (side : Side) :
    (state left right sl sr a b).view.topDown (JoinRanks.pivot l r) side =
      [match side with
       | .left => leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl)
       | .right => rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr)] := by
  have links := root_links left right sl sr a b
  have membership : ∀ element,
      element ∈ (state left right sl sr a b).view.topDown (JoinRanks.pivot l r) side ↔
      element ∈ [match side with
       | .left => leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl)
       | .right => rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr)] := by
    intro element
    rw [HeapView.mem_topDown_iff, parent_pivot_iff left right sl sr a b aRep bRep]
    simp only [List.mem_singleton]
    cases side <;> constructor
    · rintro ⟨rfl | rfl, sideEq⟩
      · rfl
      · rw [links.2.2.2] at sideEq
        cases sideEq
    · rintro rfl
      exact ⟨Or.inl rfl, links.2.1⟩
    · rintro ⟨rfl | rfl, sideEq⟩
      · rw [links.2.1] at sideEq
        cases sideEq
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, links.2.2.2⟩
  cases side with
  | left => exact List.Pairwise.eq_of_mem_iff ((state left right sl sr a b).view.topDown_ordered _).1 (by simp) membership
  | right => exact List.Pairwise.eq_of_mem_iff ((state left right sl sr a b).view.topDown_ordered _).2 (by simp) membership

end MultiSplay.RichJoin
