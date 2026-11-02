import MultiSplay.LayeredGeometry

/-! # Bounded rotations and split exposures through both persistent layers -/

namespace MultiSplay.Layered.Bounded

open Splay.Tree (BST)
open DynamicOptimality (RawTree)
open Splay.Accounting.OfflineConnectedSupport (heavyHeight heavyUnitCost)

variable {α : Type*}

/-- Simulate a source rotation through both existing layers. -/
theorem rotate_exists {capacity depth : Nat} (state : State capacity α) {target : RawTree α}
    (rotation : Rotation depth state.source target) (shallow : depth ≤ 1) :
    ∃ result : State capacity α, ∃ work : Nat,
      result.source = target ∧ Preparation capacity state.actual result.actual (18 * work) ∧
      work + result.potential ≤ state.potential + 10000128 * (depth + 1) := by
  obtain ⟨targetTree, indexed, same⟩ := rotation.lift state.component.source state.alphabet rfl
  obtain ⟨heavy⟩ := Heavy.exists_rotation indexed state.component.heavyRep state.component.fits
  have initialHeight := state.component.heavyRep.height_le_capacity state.component.fits
  have finalHeight := heavy.finalRep.height_le_capacity (indexed.size_eq ▸ state.component.fits)
  have supportBound := heavy.work_le
  have shallowBound := Nat.mul_le_mul_left (4 * heavyUnitCost capacity + 4) (show depth + 1 ≤ 2 by omega)
  obtain ⟨actual, ribRep, work, count, run, countBound, ribBound⟩ :=
    simulate heavy.path (by dsimp [heavyHeight]; omega) state.component.ribRep state.component.heavyFits
  let component : Component capacity := {
    lower := state.component.lower
    upper := state.component.upper
    source := targetTree
    heavy := heavy.final
    actual := actual
    heavyRep := heavy.finalRep
    side := state.component.side
    ribRep := ribRep
    fits := indexed.size_eq ▸ state.component.fits }
  refine ⟨⟨component, state.alphabet⟩, work, same, BoundedMacros.Preparation.segment state.alphabet run (by omega), ?_⟩
  have heavyBound := heavy.amortized
  change work + (21552 * heavy.finalRep.potential + ribRep.potential) ≤
    (21552 * state.component.heavyRep.potential + state.component.ribRep.potential) + 10000128 * (depth + 1)
  omega

/-- A common split first exposes the pivot through both layers and then
returns the actual pair of heavy/rib histories of each surviving child. -/
theorem split_exists {capacity : Nat} (state : State capacity α)
    {left right : RawTree α} {key : α} (root : state.source = .node left key right) :
    ∃ a b : State capacity α, ∃ work : Nat,
      a.source = left ∧ b.source = right ∧
      Preparation capacity state.actual (.node a.actual key b.actual) (18 * work) ∧
      work + a.potential + b.potential ≤ state.potential + 2478928 := by
  rcases state with ⟨⟨lower, upper, source, heavyTree, actual, heavyRep, side, ribRep, fits⟩, alphabet⟩
  cases source with
  | empty => simp [State.source, DynamicOptimality.BST.toRaw, Auxiliary.map] at root
  | node l r =>
      simp only [State.source, DynamicOptimality.BST.toRaw, Auxiliary.map,
        ChaCha.MTR.Tree.node.injEq] at root
      obtain ⟨heavy⟩ := Heavy.exists_split heavyRep
      have heavyFits : heavyTree.size ≤ capacity := (Rib.same_interval_size (.node l r) heavyTree) ▸ fits
      have initialHeight := heavyRep.height_le_capacity fits
      have exposedHeavyHeight := heavy_node_height heavy.leftRep heavy.rightRep fits
      have supportBound := heavy.work_le
      obtain ⟨exposed, exposedRep, work, count, run, countBound, simulatedBound⟩ :=
        simulate heavy.path (by dsimp [heavyHeight]; omega) ribRep heavyFits
      obtain ⟨rib⟩ := Rib.exists_split exposedRep
      have leftFits : l.size ≤ capacity := by simp only [BST.size] at fits; omega
      have rightFits : r.size ≤ capacity := by simp only [BST.size] at fits; omega
      let a : State capacity α := ⟨⟨_, _, l, heavy.actualLeft, rib.actualLeft,
        heavy.leftRep, true, rib.leftRep, leftFits⟩, alphabet⟩
      let b : State capacity α := ⟨⟨_, _, r, heavy.actualRight, rib.actualRight,
        heavy.rightRep, false, rib.rightRep, rightFits⟩, alphabet⟩
      refine ⟨a, b, work + rib.work, root.1, root.2.2, ?_, ?_⟩
      · have exposedFits : (BST.node heavy.actualLeft heavy.actualRight).size ≤ capacity :=
          (Rib.same_interval_size (.node l r) (.node heavy.actualLeft heavy.actualRight)) ▸ fits
        have hh : (BST.node heavy.actualLeft heavy.actualRight).height ≤ heavyHeight capacity := by
          dsimp [heavyHeight]; omega
        have eh := (exposedRep.height_le exposedFits).trans (Nat.mul_le_mul_right _ hh)
        have rh := rib_node_height rib.leftRep rib.rightRep exposedFits hh
        have rw := rib.work_le
        have finalPath := prepare alphabet rib.path (by omega) rh (by omega)
          exposedRep.geometry.1 (rib_node_geometry rib.leftRep rib.rightRep)
        have physical := (BoundedMacros.Preparation.segment alphabet run (show 3 * count ≤ 18 * work by omega)).trans finalPath
        simpa only [a, b, State.actual, DynamicOptimality.BST.toRaw, Auxiliary.map, root.2.1, Nat.mul_add] using physical
      · have heavyBound := heavy.amortized
        have ribBound := rib.amortized
        change work + rib.work + (21552 * heavy.leftRep.potential + rib.leftRep.potential) +
          (21552 * heavy.rightRep.potential + rib.rightRep.potential) ≤
          (21552 * heavyRep.potential + ribRep.potential) + 2478928
        omega

end MultiSplay.Layered.Bounded
