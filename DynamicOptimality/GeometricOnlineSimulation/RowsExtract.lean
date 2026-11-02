import DynamicOptimality.GeometricOnlineSimulation.ClassSplit

/-! # Causal extraction of a satisfying row

The recursion only inspects the current last-touch heights and the current
row. Every extracted key is a skeleton key of its current highest class;
its destructive split is charged to that class's existing credit.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR SearchRotation

/-- The remaining literal holes contain precisely the untouched intervals. -/
def ClassFrame.Selected {system : SplitTreeSystem} (height : Nat → Int)
    (row : Finset Nat) {skeleton : RawTree Nat} (frame : ClassFrame system skeleton)
    (lower upper : Nat) : Prop :=
  frame.Property (fun key => key ∈ row)
    (fun lo hi child => child.Realizes height lo hi ∧
      ∀ key, lo ≤ key → key < hi → key ∉ row) lower upper

private theorem rotations_size {before after : RawTree Nat} {count : Nat}
    (run : Rotations before after count) : before.size = after.size := by
  induction run with
  | refl => rfl
  | step head tail ih => exact (rotation_size head).trans ih

/-- A satisfying geometric row is exposed as one physical skeleton. Every
untouched class remains a literal subtree, and the rotations consume only
old credit. -/
theorem ClassTree.Realizes.extract {system : SplitTreeSystem} {height : Nat → Int}
    {n : Nat} {row : Finset Nat}
    (satisfies : GreedyMerge.Geometry.RowSatisfies height n row)
    {lower upper : Nat} {tree : ClassTree system}
    (valid : tree.Realizes height lower upper) (inside : upper ≤ n) :
    ∃ (skeleton : RawTree Nat) (frame : ClassFrame system skeleton) (count : Nat),
      Rotations tree.tree frame.tree count ∧ count + frame.credit ≤ tree.credit ∧
      frame.Selected height row lower upper := by
  classical
  generalize measure : tree.tree.size = size
  induction size using Nat.strong_induction_on generalizing lower upper tree with
  | h size ih =>
      by_cases untouched : ∀ key, lower ≤ key → key < upper → key ∉ row
      · exact ⟨.empty, .hole tree, 0, .refl _, by simp [ClassFrame.credit],
          .hole ⟨valid, untouched⟩⟩
      · push_neg at untouched
        obtain ⟨access, accessLo, accessHi, requested⟩ := untouched
        cases tree with
        | empty =>
            cases valid
            omega
        | node time state nonempty original =>
            cases valid with
            | node frameValid =>
                obtain ⟨key, member, keyInRow⟩ :=
                  frameValid.row_hits_class nonempty inside satisfies requested accessLo accessHi
                obtain ⟨keyLo, keyHi, keyTime⟩ := frameValid.key_height key member
                obtain ⟨front, back, count, frontValid, backValid, splitRun, splitBudget⟩ :=
                  frameValid.split (nonempty := nonempty) key member
                have sizes := rotations_size splitRun
                simp only [Tree.size] at sizes
                have frontLess : front.tree.size < size := by
                  simp only [ClassTree.tree] at measure
                  omega
                have backLess : back.tree.size < size := by
                  simp only [ClassTree.tree] at measure
                  omega
                obtain ⟨frontSkeleton, frontFrame, frontCount, frontRun, frontBudget, frontSelected⟩ :=
                  ih front.tree.size frontLess frontValid (by omega) rfl
                obtain ⟨backSkeleton, backFrame, backCount, backRun, backBudget, backSelected⟩ :=
                  ih back.tree.size backLess backValid inside rfl
                refine ⟨.node frontSkeleton key backSkeleton, .node frontFrame key backFrame,
                  count + frontCount + backCount, ?_, ?_, ?_⟩
                · have frontLift := frontRun.plug [.left key back.tree]
                  have backLift := backRun.plug [.right frontFrame.tree key]
                  exact (splitRun.append frontLift).append backLift
                · simp only [ClassFrame.credit]
                  omega
                · exact .node keyLo keyHi frontSelected backSelected keyInRow

end DynamicOptimality.GeometricOnlineSimulation
