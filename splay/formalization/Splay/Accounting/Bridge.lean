import Splay.Accounting.Certificate
import Splay.Assumptions.NormalFormBridge

namespace Splay.Accounting

/--
Conditional global accounting hypothesis.

One uniform tuple of constants must work for every universe size, initial
splay tree, and access sequence. Each instance supplies the concrete event
counts and all local inequalities through `Certificate`.
-/
def Hypothesis (model : CostModel) (comparison : ComparisonProfile) : Prop :=
  ∃ constants : Constants,
    ∀ (n : ℕ), 0 < n →
      ∀ (initial : model.Initial n) (accesses : List (Fin n)),
        Nonempty
          (Certificate constants n
            (comparison.cost accesses)
            (comparison.maxHeight accesses)
            (model.splayCost initial accesses))

/-- Exact accounting certificates discharge the conditional core layer. -/
theorem Hypothesis.hasCoreAnalysisBound
    {model : CostModel} {comparison : ComparisonProfile}
    (hypothesis : Hypothesis model comparison) :
    HasCoreAnalysisBound model comparison := by
  obtain ⟨constants, hCertificates⟩ := hypothesis
  refine ⟨constants.coreConstant, constants.coreConstant_pos, ?_⟩
  intro n hN initial accesses
  let certificate :=
    Classical.choice (hCertificates n hN initial accesses)
  have hCost := certificate.cost_bound
  simpa only [gapBound, gapLog, Analysis.heightFactor, Nat.add_comm,
    mul_assoc] using hCost

/--
Conditional form of the paper's main theorem after isolating exactly its two
unproved large dependencies: normal form and global accounting.
-/
theorem targetBound_of_normalForm_and_accounting
    (model : CostModel)
    (normalForm : Assumptions.NormalForm.Hypothesis model)
    (accounting :
      Hypothesis model
        normalForm.realize.comparisonProfile) :
    TargetBound model :=
  Assumptions.NormalForm.targetBound_of_normalForm_and_core
    model normalForm.realize accounting.hasCoreAnalysisBound

end Splay.Accounting
