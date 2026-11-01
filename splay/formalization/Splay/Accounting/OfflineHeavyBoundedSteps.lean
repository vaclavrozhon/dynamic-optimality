import Splay.Accounting.OfflineHeavyRotation
import Splay.Accounting.OfflineRestrictedMacros

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree OfflineNormalForm

def heavyHeight (n : ℕ) : ℕ := 6 * (Nat.clog 2 (n + 1)) ^ 2 + 8 * heavyUnitCost n + 9

namespace HeavyRepresentation

theorem height_le_capacity {capacity lower upper : ℕ} {before after : BST lower upper}
    (representation : HeavyRepresentation capacity before after) (fits : before.size ≤ capacity) :
    after.height ≤ 6 * (Nat.clog 2 (capacity + 1)) ^ 2 := by
  have bound := representation.height_le
  have levels := Nat.clog_mono_right 2 (Nat.add_le_add_right fits 1)
  exact bound.trans (Nat.mul_le_mul_left 6 (Nat.pow_le_pow_left levels 2))

theorem exists_boundedRotation {n depth : ℕ} {before after actual : BST 0 n}
    (rotation : BST.RotationAt depth before after) (shallow : depth ≤ 1)
    (representation : HeavyRepresentation n before actual) :
    ∃ (resultTree : BST 0 n) (result : HeavyRepresentation n after resultTree) (count : ℕ),
      BoundedTrace (heavyHeight n) 1 [] actual resultTree count ∧
      count + 4 * result.potential ≤ 4 * representation.potential + 3712 := by
  obtain ⟨resultTree, result, cost, path, localBound, amortized⟩ :=
    representation.exists_rotation rotation (by simp)
  have initialHeight := representation.height_le_capacity (by simp)
  have finalHeight := result.height_le_capacity (by simp)
  obtain ⟨count, trace, countBound⟩ := path.exists_boundedTrace (height := heavyHeight n) (by
    have depthBound : (4 * heavyUnitCost n + 4) * (depth + 1) ≤ (4 * heavyUnitCost n + 4) * 2 :=
      Nat.mul_le_mul_left _ (by omega)
    dsimp [heavyHeight]
    omega)
  exact ⟨resultTree, result, count, trace, by omega⟩

/-- A request explicitly exposes its original root, serves it, and rejoins
the updated child histories. Equal endpoints and repeated requests are included. -/
theorem exists_boundedService {n : ℕ} {before actual : BST 0 n}
    (representation : HeavyRepresentation n before actual) (key : Fin n) (root : before.HasRoot key.val) :
    ∃ (resultTree : BST 0 n) (result : HeavyRepresentation n before resultTree) (count : ℕ),
      BoundedTrace (heavyHeight n) 1 [key] actual resultTree count ∧
      count + 4 * result.potential ≤ 4 * representation.potential + 920 := by
  obtain ⟨left, right, same⟩ := root
  cases same
  obtain ⟨actualLeft, actualRight, leftRep, rightRep, c₁, p₁, b₁, a₁⟩ := representation.exists_split_node
  have leftSize := left.size_add_lower_eq_upper
  have rightSize := right.size_add_lower_eq_upper
  have initialHeight := representation.height_le_capacity (by simp)
  have leftHeight := leftRep.height_le_capacity (by omega)
  have rightHeight := rightRep.height_le_capacity (by omega)
  have exposedHeight : (BST.node actualLeft actualRight).height ≤
      6 * (Nat.clog 2 (n + 1)) ^ 2 + 1 := by simp only [BST.height]; omega
  obtain ⟨resultTree, result, c₂, p₂, b₂, a₂⟩ := leftRep.exists_join rightRep (by simp)
  have finalHeight := result.height_le_capacity (by simp)
  obtain ⟨r₁, trace₁, count₁⟩ := p₁.exists_boundedTrace (height := heavyHeight n) (by dsimp [heavyHeight]; omega)
  obtain ⟨r₂, trace₂, count₂⟩ := p₂.exists_boundedTrace (height := heavyHeight n) (by dsimp [heavyHeight]; omega)
  refine ⟨resultTree, result, r₁ + r₂, ?_, by omega⟩
  simpa using trace₁.append (BoundedTrace.serve (access := key) ⟨_, _, rfl⟩ trace₂)

end HeavyRepresentation

end Splay.Accounting.OfflineConnectedSupport
