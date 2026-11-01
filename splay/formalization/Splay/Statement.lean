import Splay.Analysis.IteratedLog

namespace Splay

/--
The cost-level interface for the final theorem. It deliberately leaves the BST
representation abstract while fixing all quantifiers and the treatment of the
initial splay-tree configuration.
-/
structure CostModel where
  Initial : ℕ → Type
  splayCost : {n : ℕ} → Initial n → List (Fin n) → ℕ
  optCost : {n : ℕ} → List (Fin n) → ℕ

/--
Exact finite form of the paper's main asymptotic claim. The additive `n` pays
for an arbitrary initial splay-tree configuration; the optimal cost does not
depend on that configuration.
-/
def TargetBound (model : CostModel) : Prop :=
  ∃ C : ℕ, 0 < C ∧
    ∀ (n : ℕ), 0 < n →
      ∀ (initial : model.Initial n) (accesses : List (Fin n)),
        model.splayCost initial accesses ≤
          C * (model.optCost accesses + n) * Analysis.targetFactor n

end Splay
