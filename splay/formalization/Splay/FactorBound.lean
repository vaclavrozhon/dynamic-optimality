import Splay.Statement

namespace Splay

/-- Competitiveness with a replaceable factor, including arbitrary initial
trees and the additive initial population. `TargetBound` is the old instance. -/
def FactorBound (model : CostModel) (factor : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n →
    ∀ (initial : model.Initial n) (accesses : List (Fin n)),
      model.splayCost initial accesses ≤ C * (model.optCost accesses + n) * factor n

theorem FactorBound.mono {model : CostModel} {first second : ℕ → ℕ}
    (bound : FactorBound model first) (larger : ∀ n, first n ≤ second n) :
    FactorBound model second := by
  obtain ⟨C, positive, bound⟩ := bound
  exact ⟨C, positive, fun n hn initial accesses =>
    (bound n hn initial accesses).trans (Nat.mul_le_mul_left _ (larger n))⟩

end Splay
