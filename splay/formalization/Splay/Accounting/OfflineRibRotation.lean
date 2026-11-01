import Splay.Accounting.OfflineRibRootOperations

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree

namespace RibRepresentation

/-- The middle hanging subtree changes spine orientation under a rotation;
its two root operations account for that change explicitly. -/
theorem exists_rootRotation {capacity lower upper : ℕ} {side : Bool} {before after actual : BST lower upper}
    (rotation : BST.RootRotation before after) (representation : RibRepresentation capacity side before actual)
    (fits : before.size ≤ capacity) :
    ∃ (resultTree : BST lower upper) (result : RibRepresentation capacity side after resultTree) (cost : ℕ),
      HasSupportedPath actual resultTree cost cost ∧ cost ≤ 6 * ribUnitCost capacity + 6 ∧
      cost + result.potential ≤ representation.potential + 2694 := by
  cases rotation with
  | left a b c =>
      obtain ⟨actualA, actualBC, repA, repBC, c₁, p₁, b₁, a₁⟩ := representation.exists_split_node
      obtain ⟨actualB, actualC, repB, repC, c₂, p₂, b₂, a₂⟩ := repBC.exists_split_node
      obtain ⟨changedB, changedRepB, cM, pM, bM, aM⟩ := repB.exists_reorient false
        (by simp only [BST.size] at fits; omega)
      obtain ⟨actualAB, repAB, c₃, p₃, b₃, a₃⟩ := exists_join true repA changedRepB
        (by simp only [BST.size] at fits ⊢; omega)
      obtain ⟨resultTree, result, c₄, p₄, b₄, a₄⟩ := exists_join side repAB repC
        (by simp only [BST.size] at fits ⊢; omega)
      refine ⟨resultTree, result, c₁ + c₂ + cM + c₃ + c₄ + 6, ?_, by omega, by omega⟩
      exact (((((p₁.trans (p₂.rightContext actualA)).trans
        ((pM.leftContext actualC).rightContext actualA)).trans
        (HasSupportedPath.rootLeft actualA changedB actualC)).trans
        (p₃.leftContext actualC)).trans p₄).mono (by omega) (by omega)
  | right a b c =>
      obtain ⟨actualAB, actualC, repAB, repC, c₁, p₁, b₁, a₁⟩ := representation.exists_split_node
      obtain ⟨actualA, actualB, repA, repB, c₂, p₂, b₂, a₂⟩ := repAB.exists_split_node
      obtain ⟨changedB, changedRepB, cM, pM, bM, aM⟩ := repB.exists_reorient true
        (by simp only [BST.size] at fits; omega)
      obtain ⟨actualBC, repBC, c₃, p₃, b₃, a₃⟩ := exists_join false changedRepB repC
        (by simp only [BST.size] at fits ⊢; omega)
      obtain ⟨resultTree, result, c₄, p₄, b₄, a₄⟩ := exists_join side repA repBC
        (by simp only [BST.size] at fits ⊢; omega)
      refine ⟨resultTree, result, c₁ + c₂ + cM + c₃ + c₄ + 6, ?_, by omega, by omega⟩
      exact (((((p₁.trans (p₂.leftContext actualC)).trans
        ((pM.rightContext actualA).leftContext actualC)).trans
        (HasSupportedPath.rootRight actualA changedB actualC)).trans
        (p₃.rightContext actualA)).trans p₄).mono (by omega) (by omega)

theorem exists_rotation {capacity lower upper depth : ℕ} {side : Bool} {before after actual : BST lower upper}
    (rotation : BST.RotationAt depth before after) (representation : RibRepresentation capacity side before actual)
    (fits : before.size ≤ capacity) :
    ∃ (resultTree : BST lower upper) (result : RibRepresentation capacity side after resultTree) (cost : ℕ),
      HasSupportedPath actual resultTree cost cost ∧
      cost ≤ (6 * ribUnitCost capacity + 6) * (depth + 1) ∧
      cost + result.potential ≤ representation.potential + 2694 * (depth + 1) := by
  induction rotation generalizing side with
  | root rotation => simpa using representation.exists_rootRotation rotation fits
  | leftContext rotation right ih =>
      obtain ⟨actualLeft, actualRight, leftRep, rightRep, c₁, p₁, b₁, a₁⟩ := representation.exists_split_node
      obtain ⟨changed, changedRep, c₂, p₂, b₂, a₂⟩ := ih leftRep (by simp only [BST.size] at fits; omega)
      obtain ⟨resultTree, result, c₃, p₃, b₃, a₃⟩ := exists_join side changedRep rightRep
        (by have size := rotation.size_eq; simp only [BST.size] at fits ⊢; omega)
      refine ⟨resultTree, result, c₁ + c₂ + c₃ + 1, ?_, ?_, by omega⟩
      · exact ((p₁.trans (p₂.leftContext actualRight)).trans p₃).mono (by omega) (by omega)
      · nlinarith
  | rightContext left rotation ih =>
      obtain ⟨actualLeft, actualRight, leftRep, rightRep, c₁, p₁, b₁, a₁⟩ := representation.exists_split_node
      obtain ⟨changed, changedRep, c₂, p₂, b₂, a₂⟩ := ih rightRep (by simp only [BST.size] at fits; omega)
      obtain ⟨resultTree, result, c₃, p₃, b₃, a₃⟩ := exists_join side leftRep changedRep
        (by have size := rotation.size_eq; simp only [BST.size] at fits ⊢; omega)
      refine ⟨resultTree, result, c₁ + c₂ + c₃ + 1, ?_, ?_, by omega⟩
      · exact ((p₁.trans (p₂.rightContext actualLeft)).trans p₃).mono (by omega) (by omega)
      · nlinarith

end RibRepresentation

end Splay.Accounting.OfflineConnectedSupport
