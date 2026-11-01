import TangoSquared.ProjectedLayouts
import TangoSquared.GlobalGapCover
import TangoSquared.EntryPayments
import TangoSquared.ExitGapBridge

/-!
# The concrete local gadget lower bound

All charges below are actual entry or delayed events in four literal periods.
Their existence and injection have already been proved from normalized accesses;
the remaining calculation combines the local turn identity and the gap cover.
-/

namespace TangoSquared

open Primary CyclicRuns GapChunks TurnAccounting Witnesses NormalizedWords
  DelayedPayments CyclicGapAccounting

private theorem bound_of_layout_exit {H : Nat} {q : Gadget} {xs : List Key}
    (hq : q ∈ allGadgets H) (initial : Key → Bool) (leaves : OnLeaves H xs)
    (normal : Normalized initial H (xs ++ (xs ++ (xs ++ xs))))
    (layout : CyclicLayout q.coarse (xs.filterMap (gadgetProjection H q)))
    (layouts : (cell : activeCells q.coarse (layout.first :: layout.rest)) →
      CycleLayout (selected q.coarse cell.val) (layout.first :: layout.rest))
    (exit_paid : exitTurns (encode layout.first.first (layout.first :: layout.rest)) ≤
      ∑ cell, ((outgoingGaps q.coarse cell.val (layouts cell).chunks).map Gap.delayed).sum) :
    (q.count xs : ℤ) ≤ q.potentialDifference H xs +
      2 * (eventSum H {q} [] (xs ++ (xs ++ (xs ++ xs))) : ℤ) := by
  have valid := allGadgets_valid hq
  have returns := projectedLayout_returnsMatch valid initial leaves normal layout
  have identity := projectedLayout_turn_identity hq leaves layout returns
  have demand := projectedLayout_demand_le hq leaves layout
  have cover := GlobalGapCover.all_cells_cover q.coarse (fun _ _ h => take_mono_lex h _)
    layout.first layout.rest layout.homogeneous layout.boundaries layouts
  obtain ⟨entries⟩ := EntryPayments.layout_family valid initial leaves normal layout
  have budget := entries_layouts_bound {q} (by simp) valid initial leaves normal layout layouts entries
  rw [EntryPayments.card_entryIndex] at budget
  have cover' : nontrivialRuns (layout.first :: layout.rest) ≤
      (∑ cell : activeCells q.coarse (layout.first :: layout.rest),
        ((outgoingGaps q.coarse cell.val (layouts cell).chunks).map Gap.delayed).sum) +
        entryTurns (encode layout.first.first (layout.first :: layout.rest)) +
        groupedJoins q.coarse (layout.first :: layout.rest) := by
    convert cover using 1
    congr 1
  have cover_int := Int.ofNat_le.mpr cover'
  have exit_int := Int.ofNat_le.mpr exit_paid
  have budget_int := Int.ofNat_le.mpr budget
  have demand_int := Int.ofNat_le.mpr demand
  simp only [Int.natCast_add] at cover_int budget_int
  omega

/-- The actual local gadget lower bound, with all witness records constructed
from normalized queries and no assumed charging or simulation hypothesis. -/
theorem gadget_local_bound {H : Nat} {q : Gadget} {xs : List Key}
    (hq : q ∈ allGadgets H) (initial : Key → Bool) (leaves : OnLeaves H xs)
    (normal : Normalized initial H (xs ++ (xs ++ (xs ++ xs)))) :
    (q.count xs : ℤ) ≤ q.potentialDifference H xs +
      2 * (eventSum H {q} [] (xs ++ (xs ++ (xs ++ xs))) : ℤ) := by
  rcases exists_cyclicLayout_or_constant q.coarse
    (xs.filterMap (gadgetProjection H q)) with constant | hlayout
  · rw [gadgetProjection_word leaves] at constant
    obtain ⟨hd, hp⟩ := Gadget.constant_case hq xs leaves constant
    rw [hd, hp]
    omega
  · obtain ⟨layout⟩ := hlayout
    let layouts := activeLayout q.coarse (layout.first :: layout.rest)
    apply bound_of_layout_exit hq initial leaves normal layout layouts
    have h := ExitGapBridge.exitTurns_le_delayed q.coarse
      (fun _ _ h => take_mono_lex h _) layout.first layout.rest
      layout.homogeneous layout.boundaries layouts
    convert h using 1

end TangoSquared
