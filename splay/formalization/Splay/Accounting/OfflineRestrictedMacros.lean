import Splay.Accounting.OfflineBoundedTrace
import Splay.Accounting.OfflineRestrictedTrace
import Splay.Accounting.OfflineSupportedComposition

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree OfflineNormalForm

theorem ribs_of_height {lower upper slack : ℕ} {tree : BST lower upper}
    (bound : tree.height ≤ slack) : HasBoundedMinorRibs tree slack := by
  apply (hasBoundedMinorRibs_iff_localNeighborDepth tree).mpr
  intro key lo hi
  exact ⟨by have := tree.externalDepth_le_height (2 * key); omega,
    by have := tree.externalDepth_le_height (2 * key + 2); omega⟩

theorem SupportedPath.eq_of_card_zero {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b)
    (zero : a.card = 0) : before = after := by
  cases path with
  | nil => rfl
  | cons rotation supported tail =>
      cases supported <;> simp [RootPrefix.card] at zero

/-- Normalize an actual supported macro. No rib hypothesis is needed for
this height-only stage; the support controls its intermediate height. -/
theorem HasSupportedPath.exists_boundedTrace {n support rotations height : ℕ}
    {before after : BST 0 n} (execution : HasSupportedPath before after support rotations)
    (endpoints : max before.height after.height + support ≤ height) :
    ∃ count, BoundedTrace height 1 [] before after count ∧ count ≤ 4 * support := by
  obtain ⟨a, b, path, card, _⟩ := execution
  by_cases positive : 0 < a.card
  · obtain ⟨result, cost, depth, heights, _, _⟩ :=
      exists_restrictedPath_of_sameFrontier a b path.toExecution.frontier_eq positive
        (ribs_of_height (slack := max before.height after.height) (le_max_left _ _))
        (ribs_of_height (le_max_right _ _))
    refine ⟨result.length, result.toBoundedTraceNil (heights.imp (fun _ bound => by omega)) depth, by omega⟩
  · have same := path.eq_of_card_zero (by omega)
    subst after
    exact ⟨0, .done _ (by omega), by omega⟩

end Splay.Accounting.OfflineConnectedSupport
