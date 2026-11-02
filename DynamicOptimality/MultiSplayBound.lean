import MultiSplay.CompetitiveLogHeight

/-! Classical MultiSplay, exported with the shared trees, cost model and OPT. -/

namespace DynamicOptimality

/-- The composed bound at the balanced reference's exact logarithmic capacity:
`L₃(n) * egTargetFactor (ceil(log₂(n+1)))`. -/
theorem multisplay_logarithmic_competitive :
    Competitive MultiSplay.Online.cost
      (MultiSplay.logarithmicFactor Splay.Analysis.egTargetFactor) :=
  MultiSplay.Online.competitive_logarithmic

/-- The actual initialized classical strategy is competitive with factor
`L₃(n) * egTargetFactor (2 L₁(n))`. -/
theorem multisplay_competitive :
    Competitive MultiSplay.Online.cost MultiSplay.shiftedEGFactor :=
  MultiSplay.Online.competitive

end DynamicOptimality
