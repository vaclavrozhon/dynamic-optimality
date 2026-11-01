import DynamicOptimality.Cost
import Splay.Accounting.ConcreteTargetBound

/-! The existing splay theorem, exported with the shared definitions. -/

namespace DynamicOptimality

theorem splay_competitive :
    Competitive Splay.Accounting.concreteSplayCost Splay.Analysis.targetFactor :=
  splay_target_iff.mp Splay.concreteTargetBound

end DynamicOptimality
