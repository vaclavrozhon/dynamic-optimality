import MultiSplay.LayeredForest
import MultiSplay.RibBoundedSimulation
import MultiSplay.BoundedPreparation
import Splay.Accounting.OfflineHeavySimulation

/-!
# Uniform intermediate bounds for the combined forest normalizer

`height` is the height allowance used during a local update. It is cubic in the
binary logarithm of component capacity. A raw join or an exposed split adds at
most one level; the allowance includes this level explicitly.
-/

namespace MultiSplay.Layered.Bounded

open Splay.Tree (BST)
open Splay.Accounting.OfflineConnectedSupport
  (HeavyRepresentation RibRepresentation heavyHeight heavyUnitCost ribUnitCost HasSupportedPath)
open Splay.Accounting.OfflineNormalForm (HasBoundedMinorRibs)

abbrev height (capacity : Nat) : Nat := Rib.simulationHeight capacity (heavyHeight capacity) + 1
abbrev Preparation {α : Type*} (capacity : Nat) := BoundedMacros.Preparation (α := α) (height capacity) 20
def Access {α : Type*} (capacity : Nat) : CommonForest.Access α := fun key before after work =>
  CommonForest.RootAccess key before after work ∧ BoundedMacros.Geometry (height capacity) 20 before

abbrev Trace {α : Type*} (capacity : Nat) := @CommonForest.Trace α (Access capacity) (Preparation capacity)

theorem height_le_logCubed (capacity : Nat) :
    height capacity ≤ 2000 * (Nat.clog 2 (capacity + 1) + 1) ^ 3 := by
  have heavyBound := Splay.Accounting.OfflineConnectedSupport.heavyHeight_le_logSquared capacity
  have multiplied := Nat.mul_le_mul_right (5 * Nat.clog 2 (capacity + 1)) heavyBound
  dsimp [height, Rib.simulationHeight, ribUnitCost]
  nlinarith [Nat.zero_le (Nat.clog 2 (capacity + 1))]

theorem rib_node_geometry {capacity lower pivot upper : Nat}
    {left actualLeft : BST lower pivot} {right actualRight : BST (pivot + 1) upper}
    (leftRep : RibRepresentation capacity true left actualLeft)
    (rightRep : RibRepresentation capacity false right actualRight) :
    HasBoundedMinorRibs (.node actualLeft actualRight) 19 := by
  have l := leftRep.geometry
  have r := rightRep.geometry
  simp only [if_true] at l
  simp only [Bool.false_eq_true, if_false] at r
  exact ⟨by omega, by omega, l.1, r.1⟩

theorem heavy_node_height {capacity lower pivot upper : Nat}
    {left actualLeft : BST lower pivot} {right actualRight : BST (pivot + 1) upper}
    (leftRep : HeavyRepresentation capacity left actualLeft)
    (rightRep : HeavyRepresentation capacity right actualRight)
    (fits : (BST.node left right).size ≤ capacity) :
    (BST.node actualLeft actualRight).height ≤ 6 * Nat.clog 2 (capacity + 1) ^ 2 + 1 := by
  have l := leftRep.height_le_capacity (show left.size ≤ capacity by simp only [BST.size] at fits; omega)
  have r := rightRep.height_le_capacity (show right.size ≤ capacity by simp only [BST.size] at fits; omega)
  simp only [BST.height]
  omega

theorem rib_node_height {capacity lower pivot upper : Nat}
    {left actualLeft : BST lower pivot} {right actualRight : BST (pivot + 1) upper}
    (leftRep : RibRepresentation capacity true left actualLeft)
    (rightRep : RibRepresentation capacity false right actualRight)
    (fits : (BST.node left right).size ≤ capacity)
    (sourceHeight : (BST.node left right).height ≤ heavyHeight capacity) :
    (BST.node actualLeft actualRight).height ≤ heavyHeight capacity * (5 * Nat.clog 2 (capacity + 1)) + 1 := by
  have l := leftRep.height_le (show left.size ≤ capacity by simp only [BST.size] at fits; omega)
  have r := rightRep.height_le (show right.size ≤ capacity by simp only [BST.size] at fits; omega)
  have lh : left.height ≤ heavyHeight capacity := by simp only [BST.height] at sourceHeight; omega
  have rh : right.height ≤ heavyHeight capacity := by simp only [BST.height] at sourceHeight; omega
  have lm := Nat.mul_le_mul_right (5 * Nat.clog 2 (capacity + 1)) lh
  have rm := Nat.mul_le_mul_right (5 * Nat.clog 2 (capacity + 1)) rh
  simp only [BST.height]
  omega

theorem simulate {capacity lower upper support rotations : Nat} {side : Bool}
    {before after actual : BST lower upper}
    (execution : HasSupportedPath before after support rotations)
    (bounded : max before.height after.height + support ≤ heavyHeight capacity)
    (representation : RibRepresentation capacity side before actual) (fits : before.size ≤ capacity) :
    ∃ final : BST lower upper, ∃ result : RibRepresentation capacity side after final, ∃ work count : Nat,
      BoundedMacros.Path (height capacity) 20 actual final count ∧
      count ≤ 4 * work ∧ work + result.potential ≤ representation.potential + 21552 * support := by
  obtain ⟨final, result, work, count, run, countBound, bound⟩ :=
    Rib.simulate_supported_bounded execution bounded representation fits
  exact ⟨final, result, work, count, run.mono (by simp [height]) (by omega), countBound, bound⟩

theorem prepare {α : Type*} {capacity lower upper support rotations : Nat} {a b : BST lower upper}
    (alphabet : Nat → α) (execution : HasSupportedPath a b support rotations)
    (leftHeight : a.height ≤ heavyHeight capacity * (5 * Nat.clog 2 (capacity + 1)) + 1)
    (rightHeight : b.height ≤ heavyHeight capacity * (5 * Nat.clog 2 (capacity + 1)) + 1)
    (localWork : support ≤ 12 * ribUnitCost capacity + 12)
    (leftRibs : HasBoundedMinorRibs a 19) (rightRibs : HasBoundedMinorRibs b 19) :
    Preparation capacity (Auxiliary.map alphabet (DynamicOptimality.BST.toRaw a))
      (Auxiliary.map alphabet (DynamicOptimality.BST.toRaw b)) (18 * support) := by
  obtain ⟨count, path, bound⟩ := BoundedMacros.exists_path execution
    (height := height capacity) (by dsimp [height, Rib.simulationHeight]; omega) leftRibs rightRibs
  exact .segment alphabet path (by omega)

end MultiSplay.Layered.Bounded
