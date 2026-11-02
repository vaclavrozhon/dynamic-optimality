import Splay.Accounting.LogHeightRibCapacity
import Splay.Accounting.OfflineRibbedTrace
import Splay.Accounting.OfflineHeavySimulation

/-!
# Height-preserving physical rib simulation

The stack capacity is the source height plus one. Together with the constant
height distortion, this controls every intermediate physical tree by a
constant times the source height. Initialization is charged once, by the
existing linear potential bound.
-/

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree OfflineNormalForm

/-- Explicit height allowance for the endpoints and the supported local
reconfiguration between them. -/
def linearRibHeight (height : ℕ) : ℕ := 13 * height + 12 * ribUnitCost (height + 1) + 13

namespace RibRepresentation

theorem exists_linearBoundedRotation {n depth height : ℕ} {side : Bool}
    {before after actual : BST 0 n}
    (rotation : BST.RotationAt depth before after) (shallow : depth ≤ 1)
    (representation : RibRepresentation (height + 1) side before actual)
    (beforeHeight : before.height ≤ height) (afterHeight : after.height ≤ height) :
    ∃ (resultTree : BST 0 n) (result : RibRepresentation (height + 1) side after resultTree) (count : ℕ),
      RibbedTrace (linearRibHeight height) 1 20 [] actual resultTree count ∧
      count + 4 * result.potential ≤ 4 * representation.potential + 21552 := by
  obtain ⟨resultTree, result, cost, path, localBound, amortized⟩ :=
    representation.exists_rotation_of_height rotation (by omega)
  have initialHeight := representation.height_le_thirteen
  have finalHeight := result.height_le_thirteen
  obtain ⟨count, trace, countBound⟩ := path.exists_ribbedTrace (height := linearRibHeight height) (by
    have depthBound : (6 * ribUnitCost (height + 1) + 6) * (depth + 1) ≤
        (6 * ribUnitCost (height + 1) + 6) * 2 := Nat.mul_le_mul_left _ (by omega)
    dsimp [linearRibHeight]
    omega) representation.geometry.1 result.geometry.1
  exact ⟨resultTree, result, count, trace, by omega⟩

theorem exists_linearBoundedService {n height : ℕ} {side : Bool} {before actual : BST 0 n}
    (representation : RibRepresentation (height + 1) side before actual)
    (sourceHeight : before.height ≤ height) (key : Fin n) (root : before.HasRoot key.val) :
    ∃ (resultTree : BST 0 n) (result : RibRepresentation (height + 1) side before resultTree) (count : ℕ),
      RibbedTrace (linearRibHeight height) 1 20 [key] actual resultTree count ∧
      count + 4 * result.potential ≤ 4 * representation.potential + 3584 := by
  obtain ⟨left, right, same⟩ := root
  cases same
  obtain ⟨actualLeft, actualRight, leftRep, rightRep, c₁, p₁, b₁, a₁⟩ := representation.exists_split_node
  have initialHeight := representation.height_le_thirteen
  have leftHeight := leftRep.height_le_thirteen
  have rightHeight := rightRep.height_le_thirteen
  have exposedHeight : (BST.node actualLeft actualRight).height ≤ 13 * height + 1 := by
    simp only [BST.height] at sourceHeight ⊢
    omega
  have exposedRibs : HasBoundedMinorRibs (.node actualLeft actualRight) 19 := by
    have leftGeometry := leftRep.geometry
    have rightGeometry := rightRep.geometry
    simp only [if_true] at leftGeometry
    simp only [Bool.false_eq_true, if_false] at rightGeometry
    exact ⟨by omega, by omega, leftGeometry.1, rightGeometry.1⟩
  obtain ⟨resultTree, result, c₂, p₂, b₂, a₂⟩ :=
    exists_join_of_height side leftRep rightRep (by omega)
  have finalHeight := result.height_le_thirteen
  obtain ⟨r₁, trace₁, count₁⟩ := p₁.exists_ribbedTrace (height := linearRibHeight height)
    (by dsimp [linearRibHeight]; omega) representation.geometry.1 exposedRibs
  obtain ⟨r₂, trace₂, count₂⟩ := p₂.exists_ribbedTrace (height := linearRibHeight height)
    (by dsimp [linearRibHeight]; omega) exposedRibs result.geometry.1
  refine ⟨resultTree, result, r₁ + r₂, ?_, by omega⟩
  simpa using trace₁.append (RibbedTrace.serve (access := key) ⟨_, _, rfl⟩ trace₂)

end RibRepresentation

theorem simulate_linearRibTrace {n height rotations : ℕ} {side : Bool} {accesses : List (Fin n)}
    {before after actual : BST 0 n} (trace : BoundedTrace height 1 accesses before after rotations)
    (representation : RibRepresentation (height + 1) side before actual) :
    ∃ (resultTree : BST 0 n) (result : RibRepresentation (height + 1) side after resultTree) (count : ℕ),
      RibbedTrace (linearRibHeight height) 1 20 accesses actual resultTree count ∧
      count + 4 * result.potential ≤ 4 * representation.potential +
        21552 * rotations + 3584 * accesses.length := by
  induction trace generalizing actual with
  | done tree height_le =>
      have bounded := representation.height_le_thirteen
      exact ⟨_, representation, 0, .done _ (by dsimp [linearRibHeight]; omega)
        (representation.geometry.1.mono (by decide)), by simp⟩
  | rotate rotation depth_le height_le tail ih =>
      obtain ⟨middle, middleRep, firstCount, firstTrace, firstCost⟩ :=
        representation.exists_linearBoundedRotation rotation depth_le height_le tail.initial_height
      obtain ⟨resultTree, result, restCount, restTrace, restCost⟩ := ih middleRep
      exact ⟨resultTree, result, firstCount + restCount,
        by simpa using firstTrace.append restTrace, by omega⟩
  | serve root tail ih =>
      obtain ⟨middle, middleRep, firstCount, firstTrace, firstCost⟩ :=
        representation.exists_linearBoundedService tail.initial_height _ root
      obtain ⟨resultTree, result, restCount, restTrace, restCost⟩ := ih middleRep
      refine ⟨resultTree, result, firstCount + restCount,
        by simpa using firstTrace.append restTrace, ?_⟩
      simp only [List.length_cons]
      omega

/-- A physical bounded-depth trace can be made ribless with constant
amortized cost, preserving its height up to a uniform factor. -/
theorem exists_linearRibbedTrace_of_boundedTrace {n height rotations : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n} (trace : BoundedTrace height 1 accesses before after rotations) :
    ∃ (initial final : BST 0 n) (count : ℕ),
      RibbedTrace (linearRibHeight height) 1 20 accesses initial final count ∧
      accesses.length + count ≤ 21552 * (accesses.length + rotations + n) := by
  obtain ⟨initial, ⟨representation⟩⟩ := RibRepresentation.exists_representation_of_height
    (height + 1) false before (by have := trace.initial_height; omega)
  obtain ⟨final, finalRep, count, result, cost⟩ := simulate_linearRibTrace trace representation
  have credit := representation.potential_le_size
  simp only [BST.size_eq_upper] at credit
  exact ⟨initial, final, count, result, by omega⟩

private theorem square_le_eight_pow (level : ℕ) : (level + 1) ^ 2 ≤ 8 * 2 ^ level := by
  induction level with
  | zero => decide
  | succ level ih =>
      by_cases small : level < 2
      · interval_cases level <;> decide
      · have squareStep : (level + 2) ^ 2 ≤ 2 * (level + 1) ^ 2 := by nlinarith
        simp only [pow_succ]
        nlinarith

private theorem pow_clog_le_twice (value : ℕ) : 2 ^ Nat.clog 2 (value + 1) ≤ 2 * (value + 1) := by
  generalize logEq : Nat.clog 2 (value + 1) = level
  cases level with
  | zero => simp; omega
  | succ level =>
      have previous : 2 ^ level < value + 1 := Nat.pow_lt_of_lt_clog (by omega)
      simp only [pow_succ]
      omega

theorem ribUnitCost_le_linear (capacity : ℕ) : ribUnitCost capacity ≤ 1024 * (capacity + 1) := by
  have square := square_le_eight_pow (Nat.clog 2 (capacity + 1))
  have power := pow_clog_le_twice capacity
  dsimp [ribUnitCost]
  omega

theorem linearRibHeight_le (height : ℕ) : linearRibHeight height ≤ 25000 * (height + 1) := by
  have cost := ribUnitCost_le_linear (height + 1)
  dsimp [linearRibHeight]
  omega

/-- Unconditional improved comparison normal form: quadratic logarithmic
height, constant rotation depth, bounded ribs, and cost relative to the
attained BST optimum. The separate weighted-stack construction needed to
replace the square by a first power is not asserted here. -/
theorem exists_structuralLogSquaredComparisonTrace {n : ℕ} (accesses : List (Fin n)) :
    ∃ trace : Splay.Assumptions.NormalForm.ComparisonTrace n accesses,
      trace.cost ≤ 400000000 * (OfflineOptimum.offlineOptCost accesses + n) ∧
      (∀ time, (trace.state time).height ≤ 5025000 * (Nat.clog 2 (n + 1) + 1) ^ 2) ∧
      (∀ step, trace.rotationDepth step ≤ 1) ∧
      (∀ time, HasBoundedMinorRibs (trace.state time) 20) := by
  obtain ⟨before, after, rotations, execution, costEq⟩ := OfflineOptimum.exists_optimalExecution_eq accesses
  obtain ⟨heavyInitial, heavyFinal, heavyCount, heavyTrace, heavyCost⟩ := exists_heavyTrace_of_execution execution
  obtain ⟨initial, final, count, trace, cost⟩ := exists_linearRibbedTrace_of_boundedTrace heavyTrace
  obtain ⟨exactTrace, heights, depths, ribs⟩ := trace.exists_exactTrace
  refine ⟨exactTrace.toComparisonTrace, ?_, ?_, depths, ribs⟩
  · rw [ExactTrace.toComparisonTrace_cost]
    omega
  · intro time
    have bound := heights time
    have linear := linearRibHeight_le (heavyHeight n)
    have heavy := heavyHeight_le_logSquared n
    have positive : 1 ≤ (Nat.clog 2 (n + 1) + 1) ^ 2 := Nat.one_le_pow 2 _ (by omega)
    exact bound.trans (by omega)

end Splay.Accounting.OfflineConnectedSupport
