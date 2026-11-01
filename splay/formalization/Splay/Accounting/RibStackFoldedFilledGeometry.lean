import Splay.Accounting.RibStackFoldedFilledMaximum
import Splay.Accounting.RibStackExactPop

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree OfflineConnectedSupport

namespace FoldedMinimumStack

def empty (capacity boundary : ℕ) : FoldedMinimumStack capacity (.last (.empty boundary)) :=
  ⟨capacity, .empty capacity, [], .empty 0 capacity, .empty boundary, .leaf capacity (.empty boundary), rfl⟩

theorem ribs {capacity lower upper boundary slack : ℕ} {frontier : SupportFrontier lower upper}
    (stack : FoldedMinimumStack capacity frontier)
    (bounds : frontier.AllPayloads (fun payload => leftBoundaryDepth payload ≤ boundary ∧ rightBoundaryDepth payload ≤ boundary))
    (ribs : frontier.AllPayloads (fun payload => HasBoundedMinorRibs payload slack)) (room : 7 + boundary ≤ slack) :
    HasBoundedMinorRibs stack.tree slack := by
  apply stack.filling.ribs stack.shaped.geometry.1 ?_ ?_ room
  · rw [Substitution.allPayloads_iff_frontier, stack.frontier_eq]; exact bounds
  · rw [Substitution.allPayloads_iff_frontier, stack.frontier_eq]; exact ribs

theorem boundaries {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : FoldedMinimumStack capacity frontier) :
    leftBoundaryDepth stack.tree ≤ 6 + frontier.firstLeftBoundary ∧
      rightBoundaryDepth stack.tree ≤ 6 + frontier.lastRightBoundary := by
  have geometry := stack.shaped.geometry
  have exactBounds := stack.filling.boundary_exact
  rw [stack.frontier_eq] at exactBounds
  omega

theorem exists_pop_next {capacity lower root upper : ℕ}
    (payload : BST lower root) (rest : SupportFrontier (root + 1) upper)
    (stack : FoldedMinimumStack capacity (.next payload rest)) :
    ∃ result : FoldedMinimumStack capacity rest,
      HasSupportedPath stack.tree (.node payload result.tree)
        (64 * Digits.popCost 0 stack.digits) (64 * Digits.popCost 0 stack.digits) ∧
      64 * Digits.popCost 0 stack.digits + result.potential ≤ stack.potential + 448 := by
  obtain ⟨key, payload', rest', result, same, _, path, amortized⟩ :=
    stack.exists_pop (by simp [SupportFrontier.card])
  cases same
  exact ⟨result, path, amortized⟩

end FoldedMinimumStack

namespace FoldedMaximumStack

def empty (capacity boundary : ℕ) : FoldedMaximumStack capacity (.last (.empty boundary)) :=
  ⟨capacity, .empty capacity, [], .empty 0 capacity, 0, .empty 0, .leaf capacity 0,
    .empty boundary, .leaf 0 (.empty boundary), rfl⟩

theorem ribs {capacity lower upper boundary slack : ℕ} {frontier : SupportFrontier lower upper}
    (stack : FoldedMaximumStack capacity frontier)
    (bounds : frontier.AllPayloads (fun payload => leftBoundaryDepth payload ≤ boundary ∧ rightBoundaryDepth payload ≤ boundary))
    (ribs : frontier.AllPayloads (fun payload => HasBoundedMinorRibs payload slack)) (room : 7 + boundary ≤ slack) :
    HasBoundedMinorRibs stack.tree slack := by
  apply stack.filling.ribs (stack.reflection.ribs_iff.mpr stack.shaped.geometry.1) ?_ ?_ room
  · rw [Substitution.allPayloads_iff_frontier, stack.frontier_eq]; exact bounds
  · rw [Substitution.allPayloads_iff_frontier, stack.frontier_eq]; exact ribs

theorem boundaries {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : FoldedMaximumStack capacity frontier) :
    leftBoundaryDepth stack.tree ≤ 6 + frontier.firstLeftBoundary ∧
      rightBoundaryDepth stack.tree ≤ 6 + frontier.lastRightBoundary := by
  have geometry := stack.shaped.geometry
  have reflected := stack.reflection.boundary_eq
  have exactBounds := stack.filling.boundary_exact
  rw [stack.frontier_eq] at exactBounds
  omega

theorem exists_pop_last {capacity lower root upper : ℕ}
    (rest : SupportFrontier lower root) (payload : BST (root + 1) upper)
    (stack : FoldedMaximumStack capacity (rest.append (.last payload))) :
    ∃ result : FoldedMaximumStack capacity rest,
      HasSupportedPath stack.tree (.node result.tree payload)
        (64 * Digits.popCost 0 stack.digits) (64 * Digits.popCost 0 stack.digits) ∧
      64 * Digits.popCost 0 stack.digits + result.potential ≤ stack.potential + 448 := by
  obtain ⟨key, rest', payload', result, same, _, path, amortized⟩ :=
    stack.exists_pop (by rw [SupportFrontier.card_append]; simp [SupportFrontier.card])
  obtain ⟨keyEq, restEq, payloadEq⟩ := rest.append_last_injective rest' payload payload' same
  subst keyEq
  cases restEq
  cases payloadEq
  exact ⟨result, path, amortized⟩

end FoldedMaximumStack

end Splay.Accounting.OfflineNormalForm.RibStack
