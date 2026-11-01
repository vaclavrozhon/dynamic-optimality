import Splay.Accounting.OfflineHeavySplit

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree

namespace HeavyRepresentation

theorem exists_rootRotation {capacity lower upper : ℕ} {before after actual : BST lower upper}
    (rotation : BST.RootRotation before after)
    (representation : HeavyRepresentation capacity before actual) (fits : before.size ≤ capacity) :
    ∃ (resultTree : BST lower upper) (result : HeavyRepresentation capacity after resultTree)
      (cost : ℕ), HasSupportedPath actual resultTree cost cost ∧
      cost ≤ 4 * heavyUnitCost capacity + 4 ∧
      cost + result.potential ≤ representation.potential + 464 := by
  cases rotation with
  | left a b c =>
      obtain ⟨actualA, actualBC, repA, repBC, c₁, p₁, b₁, a₁⟩ := representation.exists_split_node
      obtain ⟨actualB, actualC, repB, repC, c₂, p₂, b₂, a₂⟩ := repBC.exists_split_node
      obtain ⟨actualAB, repAB, c₃, p₃, b₃, a₃⟩ := repA.exists_join repB
        (by simp only [BST.size] at fits ⊢; omega)
      obtain ⟨resultTree, result, c₄, p₄, b₄, a₄⟩ := repAB.exists_join repC
        (by simp only [BST.size] at fits ⊢; omega)
      refine ⟨resultTree, result, c₁ + c₂ + c₃ + c₄ + 4, ?_, by omega, by omega⟩
      exact ((((p₁.trans (p₂.rightContext actualA)).trans
        (HasSupportedPath.rootLeft actualA actualB actualC)).trans
        (p₃.leftContext actualC)).trans p₄).mono (by omega) (by omega)
  | right a b c =>
      obtain ⟨actualAB, actualC, repAB, repC, c₁, p₁, b₁, a₁⟩ := representation.exists_split_node
      obtain ⟨actualA, actualB, repA, repB, c₂, p₂, b₂, a₂⟩ := repAB.exists_split_node
      obtain ⟨actualBC, repBC, c₃, p₃, b₃, a₃⟩ := repB.exists_join repC
        (by simp only [BST.size] at fits ⊢; omega)
      obtain ⟨resultTree, result, c₄, p₄, b₄, a₄⟩ := repA.exists_join repBC
        (by simp only [BST.size] at fits ⊢; omega)
      refine ⟨resultTree, result, c₁ + c₂ + c₃ + c₄ + 4, ?_, by omega, by omega⟩
      exact ((((p₁.trans (p₂.leftContext actualC)).trans
        (HasSupportedPath.rootRight actualA actualB actualC)).trans
        (p₃.rightContext actualA)).trans p₄).mono (by omega) (by omega)

/-- Every original rotation is simulated against the current representation,
with a depth-linear amortized cost and a separate polylogarithmic local bound. -/
theorem exists_rotation {capacity lower upper depth : ℕ} {before after actual : BST lower upper}
    (rotation : BST.RotationAt depth before after)
    (representation : HeavyRepresentation capacity before actual) (fits : before.size ≤ capacity) :
    ∃ (resultTree : BST lower upper) (result : HeavyRepresentation capacity after resultTree)
      (cost : ℕ), HasSupportedPath actual resultTree cost cost ∧
      cost ≤ (4 * heavyUnitCost capacity + 4) * (depth + 1) ∧
      cost + result.potential ≤ representation.potential + 464 * (depth + 1) := by
  induction rotation with
  | root rotation =>
      simpa using representation.exists_rootRotation rotation fits
  | leftContext rotation right ih =>
      obtain ⟨actualLeft, actualRight, leftRep, rightRep, c₁, p₁, b₁, a₁⟩ := representation.exists_split_node
      obtain ⟨changed, changedRep, c₂, p₂, b₂, a₂⟩ := ih leftRep
        (by simp only [BST.size] at fits; omega)
      obtain ⟨resultTree, result, c₃, p₃, b₃, a₃⟩ := changedRep.exists_join rightRep
        (by have size := rotation.size_eq; simp only [BST.size] at fits ⊢; omega)
      refine ⟨resultTree, result, c₁ + c₂ + c₃ + 1, ?_, ?_, ?_⟩
      · exact ((p₁.trans (p₂.leftContext actualRight)).trans p₃).mono (by omega) (by omega)
      · nlinarith
      · omega
  | rightContext left rotation ih =>
      obtain ⟨actualLeft, actualRight, leftRep, rightRep, c₁, p₁, b₁, a₁⟩ := representation.exists_split_node
      obtain ⟨changed, changedRep, c₂, p₂, b₂, a₂⟩ := ih rightRep
        (by simp only [BST.size] at fits; omega)
      obtain ⟨resultTree, result, c₃, p₃, b₃, a₃⟩ := leftRep.exists_join changedRep
        (by have size := rotation.size_eq; simp only [BST.size] at fits ⊢; omega)
      refine ⟨resultTree, result, c₁ + c₂ + c₃ + 1, ?_, ?_, ?_⟩
      · exact ((p₁.trans (p₂.rightContext actualLeft)).trans p₃).mono (by omega) (by omega)
      · nlinarith
      · omega

end HeavyRepresentation

end Splay.Accounting.OfflineConnectedSupport
