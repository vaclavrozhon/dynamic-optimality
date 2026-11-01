import Splay.Accounting.PairingClassification
import Splay.Accounting.OfflineOptimum

namespace Splay.Accounting

open OfflineOptimum

/--
The accounting endpoint specialized to the genuine offline rotation optimum.

Unlike the generic reduction, this theorem has no free numerical `optCost`
parameter: `concreteOfflineCostModel` uses the attained minimum over actual
root-serving BST rotation executions.
-/
theorem hypothesis_of_offlineNormalFormThreeLawTranslation
    (realization :
      Assumptions.NormalForm.Realization concreteOfflineCostModel)
    (shape : Interface.Shape)
    (translation :
      ThreeLawTranslationHypothesis
        realization.comparisonProfile shape) :
    Hypothesis concreteOfflineCostModel realization.comparisonProfile := by
  exact
    hypothesis_of_normalFormThreeLawTranslation
      offlineOptCost realization shape translation

/--
Direct target-bound endpoint for a realized normal form of the genuine
offline BST optimum.
-/
theorem targetBound_of_offlineNormalFormRealization_and_threeLawTranslation
    (realization :
      Assumptions.NormalForm.Realization concreteOfflineCostModel)
    (shape : Interface.Shape)
    (translation :
      ThreeLawTranslationHypothesis
        realization.comparisonProfile shape) :
    TargetBound concreteOfflineCostModel := by
  exact
    targetBound_of_normalFormRealization_and_threeLawTranslation
      offlineOptCost realization shape translation

/--
Final proposition-level reduction for the concrete offline optimum.

The only inputs left are the manuscript's normal-form transformation and the
three-law translation residue; the cost model and its optimum are fully
defined and checked inside Lean.
-/
theorem targetBound_of_offlineNormalForm_and_threeLawTranslation
    (normalForm :
      Assumptions.NormalForm.Hypothesis concreteOfflineCostModel)
    (shape : Interface.Shape)
    (translation :
      ThreeLawTranslationHypothesis
        normalForm.realize.comparisonProfile shape) :
    TargetBound concreteOfflineCostModel := by
  exact
    targetBound_of_normalForm_and_threeLawTranslation
      offlineOptCost normalForm shape translation

/--
The accounting endpoint for the genuine offline optimum with the numerical
zig-zig premise replaced by a checked partition of the concrete transcript
slots and an injective charge into proof-indexed activity-history positions.
-/
theorem hypothesis_of_offlineNormalFormClassifiedTranslation
    (realization :
      Assumptions.NormalForm.Realization concreteOfflineCostModel)
    (shape : Interface.Shape)
    (translation :
      ClassifiedThreeLawTranslationHypothesis
        realization.comparisonProfile shape) :
    Hypothesis concreteOfflineCostModel realization.comparisonProfile := by
  exact
    hypothesis_of_normalFormClassifiedThreeLawTranslation
      offlineOptCost realization shape translation

/--
Direct target-bound endpoint from a realized normal form, the genuine
offline optimum, and the checked pairing classification residue.
-/
theorem
    targetBound_of_offlineNormalFormRealization_and_classifiedTranslation
    (realization :
      Assumptions.NormalForm.Realization concreteOfflineCostModel)
    (shape : Interface.Shape)
    (translation :
      ClassifiedThreeLawTranslationHypothesis
        realization.comparisonProfile shape) :
    TargetBound concreteOfflineCostModel := by
  exact
    targetBound_of_normalFormRealization_and_classifiedTranslation
      offlineOptCost realization shape translation

/--
Classified compatibility endpoint for the concrete offline model.

There is no free optimum function and no bare numerical zig-zig field: the
latter is presented through checked transcript/activity slots and two envelope
bounds.  `classifiedThreeLawTranslationHypothesis_iff` proves that this
list-token presentation is propositionally equivalent to the three-law form.
It remains to prove the normal-form theorem and the three combined translation
estimates; manuscript-specific endpoint/adjacency semantics would be an
additional strengthening.
-/
theorem targetBound_of_offlineNormalForm_and_classifiedTranslation
    (normalForm :
      Assumptions.NormalForm.Hypothesis concreteOfflineCostModel)
    (shape : Interface.Shape)
    (translation :
      ClassifiedThreeLawTranslationHypothesis
        normalForm.realize.comparisonProfile shape) :
    TargetBound concreteOfflineCostModel := by
  exact
    targetBound_of_normalForm_and_classifiedTranslation
      offlineOptCost normalForm shape translation

end Splay.Accounting
