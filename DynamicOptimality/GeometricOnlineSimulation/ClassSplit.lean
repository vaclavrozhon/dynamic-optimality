import DynamicOptimality.GeometricOnlineSimulation.ClassPacking
import DynamicOptimality.GeometricOnlineSimulation.ClassRotations

/-! # Destructively splitting one equal-time class in its physical tree -/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR SearchRotation

/-- A class-key split lifts to the entire physical tree with exactly the
same rotation count. The credits of both resulting class trees are paid
by the original class credit. -/
theorem ClassFrame.Realizes.split {system : SplitTreeSystem} {height : Nat → Int}
    {time : Int} {lower upper : Nat} {state : system.State}
    {nonempty : system.tree state ≠ .empty}
    {frame : ClassFrame system (system.tree state)}
    (valid : frame.Realizes height time lower upper)
    (key : Nat) (member : key ∈ (system.tree state).inorder) :
    ∃ (front back : ClassTree system) (count : Nat),
      front.Realizes height lower key ∧ back.Realizes height (key+1) upper ∧
      Rotations frame.tree (.node front.tree key back.tree) count ∧
      count + front.credit + back.credit ≤
        (ClassTree.node time state nonempty frame).credit := by
  let result := system.cut state key member
  obtain ⟨target, trace, credit, targetValid⟩ :=
    ClassFrame.rotations_realizes result.rotations frame valid
  cases target with
  | node front _ back =>
      cases targetValid with
      | node lo hi first last sameTime =>
          obtain ⟨frontTree, frontValid, frontEqual, frontCredit⟩ := first.pack result.left rfl
          obtain ⟨backTree, backValid, backEqual, backCredit⟩ := last.pack result.right rfl
          refine ⟨frontTree, backTree, result.count, frontValid, backValid, ?_, ?_⟩
          · simpa only [ClassFrame.tree, frontEqual, backEqual] using trace
          · have budget := result.credit_bound
            simp only [ClassTree.credit, ClassFrame.credit] at credit ⊢
            omega

end DynamicOptimality.GeometricOnlineSimulation
