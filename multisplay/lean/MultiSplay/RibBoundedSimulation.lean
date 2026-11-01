import MultiSplay.RibPathSimulation
import MultiSplay.BoundedMacros

/-!
# Intermediate geometry while the rib layer simulates a heavy macro

Every intermediate comparison tree, including those inside each local rib
update, has the stated height and minor-rib bounds. The same chronological
construction supplies the amortized cost bound and actual shallow rotations.
-/

namespace MultiSplay.Rib

open Splay.Tree (BST)
open Splay.Accounting.OfflineConnectedSupport
  (RibRepresentation HasSupportedPath RootPrefix SupportedPath ribUnitCost
   exists_restrictedPath_of_sameFrontier ribs_of_height)

/-- The source height multiplied by the rib-stack height factor, plus the
maximum supported update at depth at most one. -/
def simulationHeight (capacity height : Nat) : Nat :=
  height * (5 * Nat.clog 2 (capacity + 1)) + 12 * ribUnitCost capacity + 12

theorem simulate_shallow_bounded {capacity height lower upper : Nat} {side : Bool}
    {before after actual : BST lower upper} {a : RootPrefix before} {b : RootPrefix after}
    (path : SupportedPath a b) (shallow : path.DepthBound 1)
    (heights : path.ForallTrees (fun source => source.height ≤ height))
    (representation : RibRepresentation capacity side before actual) (fits : before.size ≤ capacity) :
    ∃ final : BST lower upper, ∃ result : RibRepresentation capacity side after final, ∃ work count : Nat,
      BoundedMacros.Path (simulationHeight capacity height) 20 actual final count ∧
      count ≤ 4 * work ∧ work + result.potential ≤ representation.potential + 5388 * path.length := by
  induction path with
  | nil =>
      refine ⟨actual, representation, 0, 0, .nil actual ?_ ?_, by omega, by simp [SupportedPath.length]⟩
      · have bound := (representation.height_le fits).trans (Nat.mul_le_mul_right _ heights)
        dsimp [simulationHeight]
        omega
      · exact BoundedMacros.ribs_mono _ representation.geometry.1 (by omega)
  | @cons depth lower upper before middle after a b c rotation supported tail ih =>
      obtain ⟨rotated⟩ := exists_rotation rotation representation fits
      have nextFits : middle.size ≤ capacity := rotation.size_eq ▸ fits
      obtain ⟨final, result, work, count, run, countBound, bound⟩ :=
        ih shallow.2 heights.2 rotated.finalRep nextFits
      have beforeHeight := (representation.height_le fits).trans (Nat.mul_le_mul_right _ heights.1)
      have middleHeight : middle.height ≤ height := heights.2.initial
      have afterHeight := (rotated.finalRep.height_le nextFits).trans (Nat.mul_le_mul_right _ middleHeight)
      have localWork : rotated.work ≤ 12 * ribUnitCost capacity + 12 := by
        have localBound := rotated.work_le
        have shallowBound := shallow.1
        have multiplier : (6 * ribUnitCost capacity + 6) * (depth + 1) ≤
            (6 * ribUnitCost capacity + 6) * 2 := Nat.mul_le_mul_left _ (by omega)
        omega
      obtain ⟨localCount, localPath, localCountBound⟩ := BoundedMacros.exists_path rotated.path
        (height := simulationHeight capacity height) (by dsimp [simulationHeight]; omega)
        representation.geometry.1 rotated.finalRep.geometry.1
      refine ⟨final, result, rotated.work + work, localCount + count, localPath.append run, by omega, ?_⟩
      have first := rotated.amortized
      have shallowBound := shallow.1
      simp only [SupportedPath.length]
      omega

/-- Geometry and amortized cost belong to one and the same witness. This is
interval-polymorphic and retains the caller's current rib representation. -/
theorem simulate_supported_bounded {capacity height lower upper support rotations : Nat} {side : Bool}
    {before after actual : BST lower upper}
    (execution : HasSupportedPath before after support rotations)
    (bounded : max before.height after.height + support ≤ height)
    (representation : RibRepresentation capacity side before actual) (fits : before.size ≤ capacity) :
    ∃ final : BST lower upper, ∃ result : RibRepresentation capacity side after final, ∃ work count : Nat,
      BoundedMacros.Path (simulationHeight capacity height) 20 actual final count ∧
      count ≤ 4 * work ∧ work + result.potential ≤ representation.potential + 21552 * support := by
  obtain ⟨a, b, path, card, _⟩ := execution
  by_cases positive : 0 < a.card
  · obtain ⟨restricted, lengthBound, shallow, heights, _, _⟩ :=
      exists_restrictedPath_of_sameFrontier a b path.toExecution.frontier_eq positive
        (ribs_of_height (slack := max before.height after.height) (le_max_left _ _))
        (ribs_of_height (le_max_right _ _))
    obtain ⟨final, result, work, count, run, countBound, bound⟩ := simulate_shallow_bounded (height := height) restricted shallow
      (heights.imp (fun _ h => by omega)) representation fits
    exact ⟨final, result, work, count, run, countBound, by omega⟩
  · have same := path.eq_of_card_zero (by omega)
    subst after
    refine ⟨actual, representation, 0, 0, .nil actual ?_ ?_, by omega, by omega⟩
    · have sourceHeight : before.height ≤ height := by omega
      have actualHeight := (representation.height_le fits).trans (Nat.mul_le_mul_right _ sourceHeight)
      dsimp [simulationHeight]
      omega
    · exact BoundedMacros.ribs_mono _ representation.geometry.1 (by omega)

end MultiSplay.Rib
