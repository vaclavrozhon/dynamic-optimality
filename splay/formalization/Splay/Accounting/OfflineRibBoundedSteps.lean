import Splay.Accounting.OfflineRibRotation
import Splay.Accounting.OfflineRibbedTrace

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree OfflineNormalForm

def ribHeight (n height : ℕ) : ℕ := height * (5 * Nat.clog 2 (n + 1)) + 12 * ribUnitCost n + 13

namespace RibRepresentation

theorem height_le_of_bound {capacity lower upper height : ℕ} {side : Bool} {before actual : BST lower upper}
    (representation : RibRepresentation capacity side before actual) (fits : before.size ≤ capacity)
    (source : before.height ≤ height) : actual.height ≤ height * (5 * Nat.clog 2 (capacity + 1)) :=
  (representation.height_le fits).trans (Nat.mul_le_mul_right _ source)

theorem exists_boundedRotation {n depth height : ℕ} {side : Bool} {before after actual : BST 0 n}
    (rotation : BST.RotationAt depth before after) (shallow : depth ≤ 1)
    (representation : RibRepresentation n side before actual)
    (beforeHeight : before.height ≤ height) (afterHeight : after.height ≤ height) :
    ∃ (resultTree : BST 0 n) (result : RibRepresentation n side after resultTree) (count : ℕ),
      RibbedTrace (ribHeight n height) 1 20 [] actual resultTree count ∧
      count + 4 * result.potential ≤ 4 * representation.potential + 21552 := by
  obtain ⟨resultTree, result, cost, path, localBound, amortized⟩ := representation.exists_rotation rotation (by simp)
  have initialHeight := representation.height_le_of_bound (by simp) beforeHeight
  have finalHeight := result.height_le_of_bound (by simp) afterHeight
  obtain ⟨count, trace, countBound⟩ := path.exists_ribbedTrace (height := ribHeight n height) (by
    have depthBound : (6 * ribUnitCost n + 6) * (depth + 1) ≤ (6 * ribUnitCost n + 6) * 2 :=
      Nat.mul_le_mul_left _ (by omega)
    dsimp [ribHeight]
    omega) representation.geometry.1 result.geometry.1
  exact ⟨resultTree, result, count, trace, by omega⟩

theorem exists_boundedService {n height : ℕ} {side : Bool} {before actual : BST 0 n}
    (representation : RibRepresentation n side before actual) (sourceHeight : before.height ≤ height)
    (key : Fin n) (root : before.HasRoot key.val) :
    ∃ (resultTree : BST 0 n) (result : RibRepresentation n side before resultTree) (count : ℕ),
      RibbedTrace (ribHeight n height) 1 20 [key] actual resultTree count ∧
      count + 4 * result.potential ≤ 4 * representation.potential + 3584 := by
  obtain ⟨left, right, same⟩ := root
  cases same
  obtain ⟨actualLeft, actualRight, leftRep, rightRep, c₁, p₁, b₁, a₁⟩ := representation.exists_split_node
  have leftSize := left.size_add_lower_eq_upper
  have rightSize := right.size_add_lower_eq_upper
  have initialHeight := representation.height_le_of_bound (by simp) sourceHeight
  have leftHeight := leftRep.height_le_of_bound (by omega)
    (show left.height ≤ height by simp only [BST.height] at sourceHeight; omega)
  have rightHeight := rightRep.height_le_of_bound (by omega)
    (show right.height ≤ height by simp only [BST.height] at sourceHeight; omega)
  have exposedHeight : (BST.node actualLeft actualRight).height ≤ height * (5 * Nat.clog 2 (n + 1)) + 1 := by
    simp only [BST.height]
    omega
  have exposedRibs : HasBoundedMinorRibs (.node actualLeft actualRight) 19 := by
    have leftGeometry := leftRep.geometry
    have rightGeometry := rightRep.geometry
    simp only [if_true] at leftGeometry
    simp only [Bool.false_eq_true, if_false] at rightGeometry
    exact ⟨by omega, by omega, leftGeometry.1, rightGeometry.1⟩
  obtain ⟨resultTree, result, c₂, p₂, b₂, a₂⟩ := exists_join side leftRep rightRep (by simp)
  have finalHeight := result.height_le_of_bound (by simp) sourceHeight
  obtain ⟨r₁, trace₁, count₁⟩ := p₁.exists_ribbedTrace (height := ribHeight n height)
    (by dsimp [ribHeight]; omega) representation.geometry.1 exposedRibs
  obtain ⟨r₂, trace₂, count₂⟩ := p₂.exists_ribbedTrace (height := ribHeight n height)
    (by dsimp [ribHeight]; omega) exposedRibs result.geometry.1
  refine ⟨resultTree, result, r₁ + r₂, ?_, by omega⟩
  simpa using trace₁.append (RibbedTrace.serve (access := key) ⟨_, _, rfl⟩ trace₂)

end RibRepresentation

end Splay.Accounting.OfflineConnectedSupport
