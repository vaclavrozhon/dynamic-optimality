import DynamicOptimality.GeometricOnlineSimulation.ClassIntervals

/-! # Collapsing empty class skeletons into their unchanged hole -/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR

/-- An empty class contributes no physical key. Its one literal hole is
returned directly; any unused credit can be discarded. -/
theorem ClassFrame.Realizes.pack {system : SplitTreeSystem} {height : Nat → Int}
    {time : Int} {lower upper : Nat} {skeleton : RawTree Nat}
    {frame : ClassFrame system skeleton} (valid : frame.Realizes height time lower upper)
    (state : system.State) (same : system.tree state = skeleton) :
    ∃ tree : ClassTree system, tree.Realizes height lower upper ∧
      tree.tree = frame.tree ∧ tree.credit ≤ system.credit state + frame.credit := by
  by_cases empty : skeleton = .empty
  · clear same
    subst skeleton
    cases frame with
    | hole child =>
        cases valid with
        | hole childValid older =>
            exact ⟨child, childValid, rfl, Nat.le_add_left _ _⟩
  · have nonempty : system.tree state ≠ .empty := by simpa only [same] using empty
    subst skeleton
    exact ⟨.node time state nonempty frame, .node valid, rfl, Nat.le_refl _⟩

end DynamicOptimality.GeometricOnlineSimulation
