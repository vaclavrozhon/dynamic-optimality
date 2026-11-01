import MultiSplay.Competitive

/-! Classical MultiSplay, exported with the shared trees, cost model and OPT. -/

namespace DynamicOptimality

/-- The actual initialized classical strategy is competitive with factor
`L₃(n) * egTargetFactor (2 L₁(n))`. -/
theorem multisplay_competitive :
    Competitive MultiSplay.Online.cost MultiSplay.shiftedEGFactor :=
  MultiSplay.Online.competitive

end DynamicOptimality
