import Splay.Accounting.ConcreteBlackBoxBound
import Splay.Interface.SeededCoefficients

namespace Splay

/-- An unconditional instance using the explicit finite dyadic recurrence.
It uses an actual compressed execution at each recursive step. -/
theorem concreteSeededBlackBoxBound :
    FactorBound Accounting.OfflineOptimum.concreteOfflineCostModel
      (fun n => Analysis.coefficientFactor (Interface.seededCoefficients Accounting.articleShape)
        (Accounting.ConstructedPolylogNormalForm.interfaceGapCap n)) :=
  concreteBound_of_activityCoefficients _
    (Interface.seededCoefficients_valid Accounting.articleShape rfl rfl rfl)

end Splay
