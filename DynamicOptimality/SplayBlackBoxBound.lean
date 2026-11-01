import DynamicOptimality.Cost
import Splay.Accounting.IteratedLogEGBound

namespace DynamicOptimality

/-- A replaceable interface estimate, exported using the shared actual
splay cost and offline optimum. -/
theorem splay_competitive_of_activityCoefficients
    (coefficients : Splay.Interface.ActivityCoefficients)
    (valid : Splay.Interface.CoefficientBound Splay.Accounting.articleShape coefficients) :
    Competitive Splay.Accounting.concreteSplayCost
      (fun n => Splay.Analysis.coefficientFactor coefficients
        (Splay.Accounting.ConstructedPolylogNormalForm.interfaceGapCap n)) :=
  Splay.concreteBound_of_activityCoefficients coefficients valid

/-- The black-box improvement with the explicit iterated-log exponential
loss, for arbitrary initial splay trees and the shared attained optimum. -/
theorem splay_eg_competitive :
    Competitive Splay.Accounting.concreteSplayCost Splay.Analysis.egTargetFactor :=
  Splay.concreteIteratedLogEGBound

end DynamicOptimality
