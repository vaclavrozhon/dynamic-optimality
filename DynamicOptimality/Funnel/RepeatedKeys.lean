import DynamicOptimality.Funnel.Triangle

/-! # The repeated-column obstruction to an empty-triangle assertion -/

namespace DynamicOptimality.Funnel

/-- The final request sees the first `1` and the later `3`. -/
theorem repeated_column_switch :
    Switch ([1,3,3,2] : List Nat).get Finset.univ 3 0 2 := by decide

/-- Their base rectangle contains the earlier `3`, including its boundary. -/
theorem repeated_column_base_blocked :
    ¬ Visible ([1,3,3,2] : List Nat).get Finset.univ 2 0 := by decide

/-- The convention counts one actual change of side, with no baseline. -/
theorem repeated_column_count : wordCount ([1,3,3,2] : List Nat) = 1 := by decide

end DynamicOptimality.Funnel
