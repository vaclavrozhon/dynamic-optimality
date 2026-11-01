import TangoSquared.DelayedPayments
import TangoSquared.EntryGapBridge

/-! Summing actual selected-cell gaps over the original cyclic run layout. -/

namespace TangoSquared.GlobalGapCover

open CyclicRuns GapChunks CyclicGapAccounting CyclicEntryAccounting TurnAccounting

variable {α C : Type*} [LinearOrder α] [LinearOrder C]

private theorem sum_adjacencyFrom {ι β : Type*} [DecidableEq ι] (s : Finset ι)
    (weight : ι → β → β → Nat) (previous : β) (xs : List β) :
    (∑ i ∈ s, adjacencyFrom (weight i) previous xs) =
      adjacencyFrom (fun x y => ∑ i ∈ s, weight i x y) previous xs := by
  induction xs generalizing previous with
  | nil => simp [adjacencyFrom]
  | cons y ys ih => simp only [adjacencyFrom, Finset.sum_add_distrib, ih]

private theorem adjacencyFrom_mono {β : Type*} (f g : β → β → Nat)
    (previous : β) (xs : List β) (h : ∀ x y, f x y ≤ g x y) :
    adjacencyFrom f previous xs ≤ adjacencyFrom g previous xs := by
  induction xs generalizing previous with
  | nil => exact Nat.le_refl 0
  | cons y ys ih => exact Nat.add_le_add (h previous y) (ih y)

/-- Cell restrictions of the same entry account are disjoint. Any subset of
cells therefore has at most the complete original entry count. -/
theorem sum_cell_entries_le (coarse : α → C) (s : Finset C) (b : Block α) (bs : List (Block α)) :
    (∑ cell ∈ s, cyclicAdjacency
      (fun p q => if coarse q.first = cell then entryWeight p q else 0) b (b :: bs)) ≤
      entryTurns (encode b.first (b :: bs)) := by
  rw [← cyclicAdjacency_entryWeight]
  simp only [cyclicAdjacency]
  rw [sum_adjacencyFrom]
  apply adjacencyFrom_mono
  intro x y
  rw [Finset.sum_ite_eq]
  split <;> omega

/-- Removing cells without a nontrivial run removes zero demand terms only. -/
theorem sum_active_counts (coarse : α → C) (blocks : List (Block α)) :
    (∑ cell ∈ (cells coarse blocks).filter
      (fun cell => (blocks.filter (selected coarse cell)).length > 0),
      (blocks.filter (selected coarse cell)).length) = nontrivialRuns blocks := by
  rw [← sum_selected_counts coarse blocks]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro cell hcell hout
  have hzero : ¬ (blocks.filter (selected coarse cell)).length > 0 := by
    intro hpos
    exact hout (Finset.mem_filter.mpr ⟨hcell, hpos⟩)
  omega

/-- Every nontrivial run is covered by a delayed event, an original entry turn,
or a cyclic fine-word join. All terms count actual occurrence layouts. -/
theorem all_cells_cover (coarse : α → C) (ordered : Monotone coarse)
    (b : Block α) (bs : List (Block α))
    (homogeneous : ∀ z ∈ b :: bs, z.Homogeneous coarse)
    (boundary : DistinctBoundaries (coarse b.first)
      ((b :: bs).map (Block.coarseSingleton coarse)))
    (layouts : (cell : (cells coarse (b :: bs)).filter
      (fun cell => ((b :: bs).filter (selected coarse cell)).length > 0)) →
      CycleLayout (selected coarse cell.val) (b :: bs)) :
    nontrivialRuns (b :: bs) ≤
      (∑ cell, ((outgoingGaps coarse cell.val (layouts cell).chunks).map Gap.delayed).sum) +
        entryTurns (encode b.first (b :: bs)) + groupedJoins coarse (b :: bs) := by
  let active := (cells coarse (b :: bs)).filter
    (fun cell => ((b :: bs).filter (selected coarse cell)).length > 0)
  have cover : (∑ cell : active, ((b :: bs).filter (selected coarse cell.val)).length) ≤
      (∑ cell : active, ((outgoingGaps coarse cell.val (layouts cell).chunks).map Gap.delayed).sum) +
      (∑ cell : active, ((outgoingGaps coarse cell.val (layouts cell).chunks).map Gap.entry).sum) +
      (∑ cell : active, cyclicJoins ((cellBlocks coarse (b :: bs) cell.val).map Block.micro)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun cell _ => layout_cover coarse cell.val (b :: bs) (layouts cell))
  have counts : (∑ cell : active, ((b :: bs).filter (selected coarse cell.val)).length) =
      nontrivialRuns (b :: bs) := by
    rw [Finset.sum_coe_sort active (fun cell => ((b :: bs).filter (selected coarse cell)).length)]
    exact sum_active_counts coarse (b :: bs)
  have entries : (∑ cell : active,
      ((outgoingGaps coarse cell.val (layouts cell).chunks).map Gap.entry).sum) ≤
      entryTurns (encode b.first (b :: bs)) := by
    simp_rw [EntryGapBridge.layout_entries coarse ordered _ b bs _ homogeneous boundary]
    rw [Finset.sum_coe_sort active (fun cell => cyclicAdjacency
      (fun p q => if coarse q.first = cell then entryWeight p q else 0) b (b :: bs))]
    exact sum_cell_entries_le coarse active b bs
  have joins : (∑ cell : active,
      cyclicJoins ((cellBlocks coarse (b :: bs) cell.val).map Block.micro)) ≤
      groupedJoins coarse (b :: bs) := by
    rw [Finset.sum_coe_sort active (fun cell =>
      cyclicJoins ((cellBlocks coarse (b :: bs) cell).map Block.micro))]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)
  rw [counts] at cover
  exact le_trans cover (Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) entries) joins)

end TangoSquared.GlobalGapCover
