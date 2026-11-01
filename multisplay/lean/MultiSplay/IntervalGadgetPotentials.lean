import MultiSplay.IntervalGadgets

/-!
# Exact local and global potentials for an arbitrary interval hierarchy

The shared fragment potentials and local cyclic turn identities are unchanged.
Only the finite family of interval-owner pairs is generalized.
-/

namespace MultiSplay.IntervalLower

open TangoSquared
open TangoSquared.Primary TangoSquared.CyclicRuns

theorem sum_allGadgets {M : Type*} [AddCommMonoid M] {H : Nat} (hierarchy : DepthTree 0 H) (F : Gadget → M) :
    ∑ q ∈ allGadgets hierarchy, F q =
      ∑ s ∈ hierarchy.nodes,
        ∑ u ∈ level s.lo, F ⟨s, u⟩ := by
  unfold allGadgets
  rw [Finset.sum_image]
  · rw [Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro s hs
    have hb := DepthTree.node_bounds _ hs
    have hlt : s.lo < H := by omega
    rw [← Finset.sum_filter]
    have heq : (owners H).filter (fun u => u.length = s.lo) = level s.lo :=
      (level_eq_owner_fiber hlt).symm
    rw [heq]
  · intro a ha b hb h
    cases a
    cases b
    simpa only [Gadget.mk.injEq, Prod.mk.injEq] using h


theorem sum_allGadgets_potentialDifference {H : Nat} (hierarchy : DepthTree 0 H) (xs : List Key) :
    (∑ q ∈ allGadgets hierarchy, q.potentialDifference H xs) =
      ∑ s ∈ hierarchy.nodes,
        splitPotentialDifference H xs s := by
  rw [sum_allGadgets]
  apply Finset.sum_congr rfl
  intro s hs
  have hb := DepthTree.node_bounds _ hs
  exact sum_owner_potentialDifference H xs s (by omega)


theorem allGadgets_potential_le_primary {H : Nat} (hierarchy : DepthTree 0 H) (xs : List Key) (hleaves : OnLeaves H xs) :
    (∑ q ∈ allGadgets hierarchy, q.potentialDifference H xs) ≤ (cyclicPrimary H xs : ℤ) := by
  rw [sum_allGadgets_potentialDifference]
  have heq := fragment_potential_telescope_primary hierarchy xs hleaves
  have hnonneg : 0 ≤ fragmentPotential H xs 0 H := by
    unfold fragmentPotential
    exact Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _)
  omega



theorem Gadget.microPotential_eq_cells {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget}
    (hq : q ∈ allGadgets hierarchy) (xs : List Key) (hleaves : OnLeaves H xs) :
    q.microPotential H xs =
      ∑ v ∈ (level (q.split.cut + 1)).filter (fun v => q.owner.IsPrefix v),
        (wordTurns (cellWord q.coarse ((ownerWord q.owner xs).map q.fine) v) : ℤ) := by
  obtain ⟨hs, hu, hlen⟩ := mem_allGadgets.mp hq
  have hb := DepthTree.node_bounds _ hs
  unfold Gadget.microPotential
  apply Finset.sum_congr rfl
  intro v hv
  obtain ⟨hvlevel, huv⟩ := Finset.mem_filter.mp hv
  rw [← ownerWord_map_take_saturated H (q.split.hi + 1) v xs hleaves]
  have hword := fine_cellWord_eq_child_owner q.owner v (q.split.cut + 1) (q.split.hi + 1)
    ((mem_level v _).1 hvlevel) huv (by omega) xs
  exact congrArg (fun w => (wordTurns w : ℤ)) hword.symm


theorem Gadget.microPotential_eq_visited {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget}
    (hq : q ∈ allGadgets hierarchy) (xs : List Key) (hleaves : OnLeaves H xs) :
    q.microPotential H xs =
      ∑ v ∈ (((ownerWord q.owner xs).map q.fine).map q.coarse).toFinset,
        (wordTurns (cellWord q.coarse ((ownerWord q.owner xs).map q.fine) v) : ℤ) := by
  rw [Gadget.microPotential_eq_cells hq xs hleaves]
  symm
  apply sum_visited_cellWords
  intro z hz
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  obtain ⟨hxin, hpx⟩ := List.mem_filter.mp hx
  have hp : q.owner.IsPrefix x := of_decide_eq_true hpx
  obtain ⟨hs, hu, hlen⟩ := mem_allGadgets.mp hq
  have hb := DepthTree.node_bounds _ hs
  have hxH := hleaves x hxin
  have hproj : q.coarse (q.fine x) = x.take (q.split.cut + 1) := by
    simp only [Gadget.coarse, Gadget.fine, List.take_take, Nat.min_eq_left (by omega : q.split.cut + 1 ≤ q.split.hi + 1)]
  rw [hproj]
  apply Finset.mem_filter.mpr
  constructor
  · apply (mem_level _ _).2
    rw [List.length_take, hxH, Nat.min_eq_left (by omega)]
  · apply List.prefix_iff_eq_take.mpr
    rw [List.take_take, Nat.min_eq_left (by omega : q.owner.length ≤ q.split.cut + 1)]
    exact List.prefix_iff_eq_take.mp hp



theorem Gadget.coarse_fine {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} (hq : q ∈ allGadgets hierarchy) (x : Key) :
    q.coarse (q.fine x) = q.coarse x := by
  have hb := DepthTree.node_bounds _ (mem_allGadgets.mp hq).1
  simp only [Gadget.coarse, Gadget.fine, List.take_take,
    Nat.min_eq_left (by omega : q.split.cut + 1 ≤ q.split.hi + 1)]


theorem Gadget.count_eq_fine_demands {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} (hq : q ∈ allGadgets hierarchy)
    (xs : List Key) : q.count xs = demands q.coarse id ((ownerWord q.owner xs).map q.fine) :=
  (demands_project_fine q.coarse q.fine q.coarse (Gadget.coarse_fine hq) _).symm


theorem Gadget.potentialDifference_eq_local {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget}
    (hq : q ∈ allGadgets hierarchy) (xs : List Key) (hleaves : OnLeaves H xs) :
    q.potentialDifference H xs =
      localTurnPotential q.coarse ((ownerWord q.owner xs).map q.fine) := by
  have hb := DepthTree.node_bounds _ (mem_allGadgets.mp hq).1
  have hmap : (((ownerWord q.owner xs).map q.fine).map q.coarse) =
      (ownerWord q.owner xs).map q.coarse := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp_def, Gadget.coarse, Gadget.fine, List.take_take,
      Nat.min_eq_left (by omega : q.split.cut + 1 ≤ q.split.hi + 1)]
  rw [Gadget.potentialDifference, Gadget.parentPotential_eq_actual q H xs hleaves,
    Gadget.macroPotential_eq_actual q H xs hleaves, Gadget.microPotential_eq_visited hq xs hleaves]
  unfold localTurnPotential
  rw [hmap]
  congr 2
  apply Finset.sum_congr
  · ext v
    simp
  · intro v hv
    rfl


theorem Gadget.layout_local_turn_identity {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget}
    (hq : q ∈ allGadgets hierarchy) (xs : List Key) (hleaves : OnLeaves H xs)
    (layout : CyclicLayout q.coarse ((ownerWord q.owner xs).map q.fine))
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
    rw [layout.rotation, localTurnPotential_swap_append, ← layout.split,
      ← Gadget.potentialDifference_eq_local hq xs hleaves]
  rw [hp] at h
  exact h


theorem Gadget.constant_case {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} (hq : q ∈ allGadgets hierarchy)
    (xs : List Key) (hleaves : OnLeaves H xs)
    (hconstant : CoarseConstant q.coarse ((ownerWord q.owner xs).map q.fine)) :
    q.count xs = 0 ∧ q.potentialDifference H xs = 0 := by
  constructor
  · rw [Gadget.count_eq_fine_demands hq xs]
    cases hw : (ownerWord q.owner xs).map q.fine with
    | nil => rfl
    | cons a as =>
      rw [hw] at hconstant
      apply rlFrom_transitionsFrom_of_same_coarse q.coarse id a as false
      intro y hy
      exact hconstant y (by simp [hy]) a (by simp)
  · rw [Gadget.potentialDifference_eq_local hq xs hleaves]
    exact localTurnPotential_of_constant _ _ hconstant


end MultiSplay.IntervalLower
