import MultiSplay.IntervalLayoutPayments
import MultiSplay.IntervalGadgetPotentials
import ChaCha.GadgetLocalBound

/-!
# Actual local lower bounds for arbitrary binary interval hierarchies

The per-gadget bound constructs the same occurrence families and applies the
shared gap-cover and exit-turn theorems. Every counted event is a concrete
entry or delayed record; no cost certificate is a premise.
-/

namespace MultiSplay.IntervalLower

open ChaCha
open ChaCha.Primary ChaCha.CyclicRuns ChaCha.GapChunks ChaCha.TurnAccounting
open ChaCha.Witnesses ChaCha.NormalizedWords ChaCha.DelayedPayments ChaCha.CyclicGapAccounting
open MultiSplay.IntervalLower.DelayedPayments

theorem projectedLayout_returnsMatch {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {xs : List Key}
    (hq : Valid hierarchy q) (initial : Key → Bool) (leaves : OnLeaves H xs)
    (normal : Normalized initial H (xs ++ (xs ++ (xs ++ xs))))
    (layout : CyclicLayout q.coarse (xs.filterMap (gadgetProjection H q))) :
    ReturnsMatch q.coarse (layout.first :: layout.rest) := by
  apply returnsMatch_of_returnWord q.coarse layout.first layout.rest
    layout.homogeneous layout.boundaries
  let runword := ((layout.first :: layout.rest).map Block.word).flatten
  have embed : (xs ++ (xs ++ (xs ++ xs))).filterMap (gadgetProjection H q) =
      layout.cutBefore ++ (runword ++ runword) ++
        (layout.suffix ++ xs.filterMap (gadgetProjection H q)) := by
    simp only [List.filterMap_append, runword, layout.rotation, layout.split, List.append_assoc]
  apply GapInheritance.returnWord_infix q.coarse layout.cutBefore _
    (layout.suffix ++ xs.filterMap (gadgetProjection H q))
  rw [← embed]
  apply gadgetProjection_returnWord hq initial _ normal
  intro x hx
  exact leaves x (by simpa using hx)


theorem projectedLayout_demand_le {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {xs : List Key}
    (hq : q ∈ allGadgets hierarchy) (leaves : OnLeaves H xs)
    (layout : CyclicLayout q.coarse (xs.filterMap (gadgetProjection H q))) :
    q.count xs ≤ nontrivialRuns (layout.first :: layout.rest) := by
  rw [Gadget.count_eq_fine_demands hq xs, ← gadgetProjection_word leaves]
  convert layout.demands_le using 1
  congr 1


theorem projectedLayout_turn_identity {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {xs : List Key}
    (hq : q ∈ allGadgets hierarchy) (leaves : OnLeaves H xs)
    (layout : CyclicLayout q.coarse (xs.filterMap (gadgetProjection H q)))
    (returns : ReturnsMatch q.coarse (layout.first :: layout.rest)) :
    (groupedJoins q.coarse (layout.first :: layout.rest) : ℤ) +
      (TurnAccounting.nontrivialMacroTurns (encode layout.first.first (layout.first :: layout.rest)) : ℤ) =
      q.potentialDifference H xs +
        (TurnAccounting.entryTurns (encode layout.first.first (layout.first :: layout.rest)) : ℤ) +
        (TurnAccounting.exitTurns (encode layout.first.first (layout.first :: layout.rest)) : ℤ) := by
  have h := local_turn_potential_identity q.coarse (fun _ _ h => take_mono_lex h _)
    layout.first layout.rest layout.homogeneous layout.boundaries returns
  have hp : localTurnPotential q.coarse ((layout.first :: layout.rest).map Block.word).flatten =
      q.potentialDifference H xs := by
    rw [layout.rotation, localTurnPotential_swap_append, ← layout.split, gadgetProjection_word leaves,
      ← Gadget.potentialDifference_eq_local hq xs leaves]
  rw [hp] at h
  exact h


private theorem bound_of_layout_exit {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {xs : List Key}
    (hq : q ∈ allGadgets hierarchy) (initial : Key → Bool) (leaves : OnLeaves H xs)
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
theorem gadget_local_bound {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {xs : List Key}
    (hq : q ∈ allGadgets hierarchy) (initial : Key → Bool) (leaves : OnLeaves H xs)
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


end MultiSplay.IntervalLower
