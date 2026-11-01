import Splay.Accounting.ArticlePairingPassRealizer
import Splay.Lazy.SideTransferGeometry

namespace Splay.Accounting.ArticleBatchDestinationAllocation.BatchReparentedView

open Splay.Lazy Splay.Lazy.Canonical

variable {n : ℕ} {before : HeapView n} {matching : List (Interface.Pairing n)}
  (after : BatchReparentedView before matching)
  (parents : ∀ pairing ∈ matching,
    before.parent pairing.winner = some before.root ∧ before.parent pairing.loser = some before.root)

private theorem outside_of_not_loser {element : Element n}
    (outside : element ∉ Interface.pairingLosers matching) :
    ∀ pairing ∈ matching, element ≠ pairing.loser := by
  intro pairing member equal
  exact outside (List.mem_map.mpr ⟨pairing, member, equal.symm⟩)

include after parents in
theorem root_topDown (side : Side) :
    after.view.topDown before.root side =
      (before.topDown before.root side).filter (fun element => decide (element ∉ Interface.pairingLosers matching)) := by
  have winnerNeRoot : ∀ pairing ∈ matching, pairing.winner ≠ before.root := by
    intro pairing member equal
    have strict := before.parent_level_lt (parents pairing member).1
    rw [equal] at strict
    exact Nat.lt_irrefl _ strict
  have membership : ∀ element, element ∈ after.view.topDown before.root side ↔
      element ∈ (before.topDown before.root side).filter (fun element => decide (element ∉ Interface.pairingLosers matching)) := by
    intro element
    by_cases moved : element ∈ Interface.pairingLosers matching
    · obtain ⟨pairing, member, equal⟩ := List.mem_map.mp moved
      subst element
      simp [HeapView.mem_topDown_iff, after.paired_parent pairing member, winnerNeRoot pairing member, moved]
    · simp only [HeapView.mem_topDown_iff, after.unpaired_parent _ (outside_of_not_loser moved),
        after.unpaired_side _ (outside_of_not_loser moved), List.mem_filter, decide_eq_true_eq]
      simp [moved, HeapView.mem_topDown_iff]
  cases side with
  | left =>
      exact List.Pairwise.eq_of_mem_iff (after.view.topDown_ordered before.root).1
        ((before.topDown_ordered before.root).1.filter _) membership
  | right =>
      exact List.Pairwise.eq_of_mem_iff (after.view.topDown_ordered before.root).2
        ((before.topDown_ordered before.root).2.filter _) membership

include after parents in
/-- A non-root owner which never wins a pair keeps its exact child order. -/
theorem other_topDown (owner : Element n) (side : Side) (notRoot : owner ≠ before.root)
    (notWinner : ∀ pairing ∈ matching, pairing.winner ≠ owner) :
    after.view.topDown owner side = before.topDown owner side := by
  have membership : ∀ element, element ∈ after.view.topDown owner side ↔ element ∈ before.topDown owner side := by
    intro element
    by_cases moved : element ∈ Interface.pairingLosers matching
    · obtain ⟨pairing, member, equal⟩ := List.mem_map.mp moved
      subst element
      simp [HeapView.mem_topDown_iff, after.paired_parent pairing member, (parents pairing member).2,
        notWinner pairing member, notRoot.symm]
    · simp only [HeapView.mem_topDown_iff, after.unpaired_parent _ (outside_of_not_loser moved),
        after.unpaired_side _ (outside_of_not_loser moved)]
  cases side with
  | left =>
      exact List.Pairwise.eq_of_mem_iff (after.view.topDown_ordered owner).1
        (before.topDown_ordered owner).1 membership
  | right =>
      exact List.Pairwise.eq_of_mem_iff (after.view.topDown_ordered owner).2
        (before.topDown_ordered owner).2 membership

include after parents in
/-- Removing paired losers from the root order leaves a transferable prefix
above an untouched bottommost boundary. Its old children remain below it. -/
theorem exists_sideTransferGeometry (boundary : Element n) (side : Side)
    (front : List (Element n)) (decomposition : before.topDown before.root side = front ++ [boundary])
    (untouched : ∀ pairing ∈ matching, pairing.winner ≠ boundary ∧ pairing.loser ≠ boundary)
    (ranks : ∀ element ∈ front, before.rank boundary < before.rank element)
    (nested : before.NestedChildOrder) :
    Nonempty (SideTransferGeometry after.view before.root boundary side) := by
  have boundaryMember : boundary ∈ before.topDown before.root side := by rw [decomposition]; simp
  have boundaryPlacement := before.mem_topDown_iff.mp boundaryMember
  have boundaryNotRoot : boundary ≠ before.root := by
    intro equal
    have strict := before.parent_level_lt boundaryPlacement.1
    rw [equal] at strict
    exact Nat.lt_irrefl _ strict
  have boundaryNotLoser : boundary ∉ Interface.pairingLosers matching := by
    rintro member
    obtain ⟨pairing, member, equal⟩ := List.mem_map.mp member
    exact (untouched pairing member).2 equal
  have frontFresh : boundary ∉ front := by
    have distinct := before.topDown_nodup before.root side
    rw [decomposition] at distinct
    intro member
    exact (List.nodup_append.mp distinct).2.2 boundary member boundary (by simp) rfl
  refine ⟨{
    moved := front.filter (fun element => decide (element ∉ Interface.pairingLosers matching))
    decomposition := ?_
    ranks := ?_
    outermost := ?_
  }⟩
  · rw [after.root_topDown parents side, decomposition]
    simp [List.filter_append, boundaryNotLoser]
  · intro element member
    rw [after.rank_eq]
    exact ranks element (List.mem_filter.mp member).1
  · intro element member child childMember
    have inFront := (List.mem_filter.mp member).1
    have elementMember : element ∈ before.topDown before.root side := by
      rw [decomposition]
      exact List.mem_append_left _ inFront
    have elementPlacement := before.mem_topDown_iff.mp elementMember
    rw [after.other_topDown parents boundary side boundaryNotRoot (fun pairing member => (untouched pairing member).1)] at childMember
    have childPlacement := before.mem_topDown_iff.mp childMember
    have different : boundary ≠ element := by intro equal; exact frontFresh (equal ▸ inFront)
    have relative : (if element.val < boundary.val then Side.left else Side.right) = side := by
      cases side with
      | left =>
          have order := (before.topDown_ordered before.root).1
          rw [decomposition] at order
          have strict := (List.pairwise_append.mp order).2.2 element inFront boundary (by simp)
          simp [strict]
      | right =>
          have order := (before.topDown_ordered before.root).2
          rw [decomposition] at order
          have strict := (List.pairwise_append.mp order).2.2 element inFront boundary (by simp)
          simp [show ¬ element.val < boundary.val by omega]
    have inequality := nested boundaryPlacement.1 elementPlacement.1 different childPlacement.1
      (childPlacement.2.trans relative.symm)
    rw [relative] at inequality
    cases side <;> simpa using inequality

end Splay.Accounting.ArticleBatchDestinationAllocation.BatchReparentedView
