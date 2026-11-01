import Splay.Accounting.WitnessedThreeLaw
import Splay.Accounting.OfflineEndpoint

namespace Splay.Accounting

open OfflineOptimum

/--
Concrete offline endpoint with all three translation laws replaced by their
checked semantic witnesses.

There is no free optimum function, no bare internal-activity index, no raw
potential-budget inequality, and no caller-supplied bend telescope.  The
remaining input consists of the uniform normal form plus the exact witnessed
translation residue described by `WitnessedThreeLawTranslationHypothesis`.
-/
theorem targetBound_of_offlineNormalForm_and_witnessedTranslation
    (normalForm :
      Assumptions.NormalForm.Hypothesis concreteOfflineCostModel)
    (shape : Interface.Shape)
    (translation :
      WitnessedThreeLawTranslationHypothesis
        normalForm.realize.comparisonProfile shape) :
    TargetBound concreteOfflineCostModel :=
  targetBound_of_offlineNormalForm_and_threeLawTranslation
    normalForm shape
      (threeLawTranslationHypothesis_of_witnessed translation)

end Splay.Accounting
