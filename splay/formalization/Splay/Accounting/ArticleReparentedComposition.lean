import Splay.Accounting.ArticlePairingPassRealizer

namespace Splay.Accounting.ArticleBatchDestinationAllocation.BatchReparentedView

open Splay.Lazy

/-- Change the source expression while keeping the literal endpoint view. -/
def transportSource {n : ℕ} {before before' : HeapView n}
    {matching : List (Interface.Pairing n)}
    (after : BatchReparentedView before matching) (equal : before' = before) :
    BatchReparentedView before' matching where
  view := after.view
  rank_eq := after.rank_eq.trans (congrArg HeapView.rank equal).symm
  root_eq := after.root_eq.trans (congrArg HeapView.root equal).symm
  ordered := after.ordered
  paired_parent := after.paired_parent
  paired_side := after.paired_side
  unpaired_parent := by intros; subst before'; exact after.unpaired_parent _ ‹_›
  unpaired_side := by intros; subst before'; exact after.unpaired_side _ ‹_›

/-- Disjoint loser sets allow two successive reparentings to be described by
one simultaneous endpoint. All parents outside those sets remain unchanged. -/
def append {n : ℕ} {view : HeapView n}
    {firstMatching secondMatching : List (Interface.Pairing n)}
    (first : BatchReparentedView view firstMatching)
    (second : BatchReparentedView first.view secondMatching)
    (distinct : ∀ a ∈ firstMatching, ∀ b ∈ secondMatching, a.loser ≠ b.loser) :
    BatchReparentedView view (firstMatching ++ secondMatching) where
  view := second.view
  rank_eq := second.rank_eq.trans first.rank_eq
  root_eq := second.root_eq.trans first.root_eq
  ordered := second.ordered
  paired_parent := by
    intro pairing member
    rcases List.mem_append.mp member with earlier | later
    · rw [second.unpaired_parent pairing.loser (distinct pairing earlier)]
      exact first.paired_parent pairing earlier
    · exact second.paired_parent pairing later
  paired_side := by
    intro pairing member
    rcases List.mem_append.mp member with earlier | later
    · rw [second.unpaired_side pairing.loser (distinct pairing earlier)]
      exact first.paired_side pairing earlier
    · exact second.paired_side pairing later
  unpaired_parent := by
    intro element outside
    rw [second.unpaired_parent element (fun p member => outside p (List.mem_append_right _ member))]
    exact first.unpaired_parent element (fun p member => outside p (List.mem_append_left _ member))
  unpaired_side := by
    intro element outside
    rw [second.unpaired_side element (fun p member => outside p (List.mem_append_right _ member))]
    exact first.unpaired_side element (fun p member => outside p (List.mem_append_left _ member))

/-- An empty matching changes no heap data. -/
def nil {n : ℕ} (view : HeapView n) (ordered : view.HeapOrdered) :
    BatchReparentedView view [] where
  view := view
  rank_eq := rfl
  root_eq := rfl
  ordered := ordered
  paired_parent := by simp
  paired_side := by simp
  unpaired_parent := by intros; rfl
  unpaired_side := by intros; rfl

end Splay.Accounting.ArticleBatchDestinationAllocation.BatchReparentedView
