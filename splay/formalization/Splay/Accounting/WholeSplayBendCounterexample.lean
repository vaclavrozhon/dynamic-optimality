import Splay.Accounting.WholeSplayBendAggregation

namespace Splay.Accounting.WholeSplayBendCounterexample

open Splay.Accounting.LocalBendGeometry
open Splay.Lazy.Canonical
open Splay.Rank
open Splay.Tree.BST

/-
The six-key counterexample used below has access key `2`.  The comparison
tree is rooted at `2`, while the splay tree reaches `2` through two
left-right/right-left double rotations.
-/

abbrev E0 : BST 0 0 := .empty 0
abbrev E1 : BST 1 1 := .empty 1
abbrev E2 : BST 2 2 := .empty 2
abbrev E3 : BST 3 3 := .empty 3
abbrev E4 : BST 4 4 := .empty 4
abbrev E5 : BST 5 5 := .empty 5
abbrev E6 : BST 6 6 := .empty 6

abbrev one : BST 1 2 := .node E1 E2
abbrev four : BST 4 5 := .node E4 E5
abbrev threeFour : BST 3 5 := .node E3 four

abbrev comparisonLeft : BST 0 2 :=
  .node E0 one

abbrev comparisonRight : BST 3 6 :=
  .node (.node E3 E4) (.node E5 E6)

/-- Serving comparison tree, with accessed key `2` at its root. -/
abbrev comparison : BST 0 6 :=
  .node comparisonLeft comparisonRight

/-- Initial splay tree.  The search path to `2` is `L,R,R,L`. -/
abbrev before : BST 0 6 :=
  .node
    (.node E0
      (.node E1
        (.node (.node E2 E3) four)))
    E6

/-- Tree after the contextual right-left zig-zag at depth two. -/
abbrev middle : BST 0 6 :=
  .node
    (.node E0
      (.node one threeFour))
    E6

/-- Tree after the final root left-right zig-zag. -/
abbrev after : BST 0 6 :=
  .node
    (.node E0 one)
    (.node threeFour E6)

/-- The serving comparison tree really is rooted at the accessed key. -/
theorem comparison_hasRoot : comparison.HasRoot 2 :=
  ⟨.node E0 (.node E1 E2),
    .node (.node E3 E4) (.node E5 E6), rfl⟩

/-- First contextual right-left zig-zag. -/
theorem firstStep : DoubleRotationAt 2 2 before middle :=
  .leftContext
    (.rightContext E0
      (.root (.zigZagRightLeft E1 E2 E3 four)))
    E6

/-- Boolean orientation certificate for the first step. -/
theorem firstOrientation :
    DoubleOrientationAt false
      (depth := 2) (key := 2) before middle :=
  .leftContext
    (.rightContext E0
      (.zigZagRightLeft E1 E2 E3 four))
    E6

/-- Final root left-right zig-zag. -/
theorem secondStep : DoubleRotationAt 0 2 middle after :=
  .root (.zigZagLeftRight E0 one threeFour E6)

/-- Boolean orientation certificate for the second step. -/
theorem secondOrientation :
    DoubleOrientationAt false
      (depth := 0) (key := 2) middle after :=
  .zigZagLeftRight E0 one threeFour E6

/-- The endpoint tree has the accessed key at its root. -/
theorem after_hasRoot : after.HasRoot 2 :=
  ⟨.node E0 one, .node threeFour E6, rfl⟩

/-- The concrete two-step bottom-up splay execution. -/
theorem execution : SplayExecution 2 before after :=
  .next (.double firstStep)
    (.next (.double secondStep) (.done after_hasRoot))

/-- Its proof-relevant transcript contains exactly two zig-zags. -/
theorem transcript :
    SplayExecutionTranscript 2 execution
      [.zigZag, .zigZag] 0 0 2 :=
  .zigZag firstStep firstOrientation
    (.next (.double secondStep) (.done after_hasRoot))
    (.zigZag secondStep secondOrientation
      (.done after_hasRoot)
      (.done after_hasRoot))

abbrev comparisonSnapshot : Snapshot 6 :=
  Snapshot.ofTree comparison

private theorem heavyBranch_eq_of_explicitMin
    {lower root upper : ℕ}
    (left : BST lower root) (right : BST (root + 1) upper)
    (upper_le : upper ≤ 6)
    (candidate : External 6)
    (minimum :
      IsIntervalMin comparisonSnapshot.rank
        ⟨2 * lower, by
          have := left.lower_le_upper
          have := right.lower_le_upper
          omega⟩
        ⟨2 * upper, by omega⟩ candidate)
    (branch : TernaryBranch)
    (contains : branch.Contains root candidate.val) :
    let node : AtNode 6 := {
      lower := lower
      root := root
      upper := upper
      left := left
      right := right
      upper_le_n := upper_le
    }
    node.heavyBranch comparisonSnapshot = branch := by
  let node : AtNode 6 := {
    lower := lower
    root := root
    upper := upper
    left := left
    right := right
    upper_le_n := upper_le
  }
  have minimum' :
      IsIntervalMin comparisonSnapshot.rank
        node.wholeLower node.wholeUpper candidate := by
    simpa [node, AtNode.wholeLower, AtNode.wholeUpper] using minimum
  have heavy :
      comparisonSnapshot.IsHeavyBranch
        node.wholeLower node.wholeUpper root branch :=
    ⟨candidate, minimum', contains⟩
  exact
    (comparisonSnapshot.heavyBranch_unique
      node.wholeLower node.wholeUpper node.whole_nonempty root heavy).symm

private theorem valueTwo_global_min :
    IsIntervalMin comparisonSnapshot.rank
      (⟨0, by omega⟩ : External 6)
      (⟨12, by omega⟩ : External 6)
      (⟨5, by omega⟩ : External 6) := by
  refine ⟨by simp, by simp, ?_⟩
  intro node _ _
  change externalDepth comparison 5 ≤
    externalDepth comparison node.val
  simp [externalDepth]

private theorem valueTwo_interval_min
    {lower upper : External 6}
    (lower_le : lower.val ≤ 5)
    (upper_ge : 5 ≤ upper.val) :
    IsIntervalMin comparisonSnapshot.rank lower upper
      (⟨5, by omega⟩ : External 6) := by
  refine ⟨?_, ?_, ?_⟩
  · change lower.val ≤ 5
    exact lower_le
  · change 5 ≤ upper.val
    exact upper_ge
  intro node _ _
  change externalDepth comparison 5 ≤
    externalDepth comparison node.val
  simp [externalDepth]

private theorem valueZero_left_interval_min :
    IsIntervalMin comparisonSnapshot.rank
      (⟨0, by omega⟩ : External 6)
      (⟨4, by omega⟩ : External 6)
      (⟨1, by omega⟩ : External 6) := by
  refine ⟨by simp, by simp, ?_⟩
  intro node _ nodeUpper
  have node_lt_root : node.val < 5 := by
    change node.val ≤ 4 at nodeUpper
    omega
  change externalDepth comparison 1 ≤
    externalDepth comparison node.val
  rw [externalDepth_node_of_lt_root comparisonLeft comparisonRight
    (by omega)]
  rw [externalDepth_root]
  rw [externalDepth_node_of_lt_root comparisonLeft comparisonRight
    node_lt_root]
  omega

private theorem valueOne_interval_min :
    IsIntervalMin comparisonSnapshot.rank
      (⟨2, by omega⟩ : External 6)
      (⟨4, by omega⟩ : External 6)
      (⟨3, by omega⟩ : External 6) := by
  refine ⟨by simp, by simp, ?_⟩
  intro node nodeLower nodeUpper
  have root_lt_node : 1 < node.val := by
    change 2 ≤ node.val at nodeLower
    omega
  have node_lt_globalRoot : node.val < 5 := by
    change node.val ≤ 4 at nodeUpper
    omega
  change externalDepth comparison 3 ≤
    externalDepth comparison node.val
  rw [externalDepth_node_of_lt_root comparisonLeft comparisonRight
    (by omega)]
  rw [externalDepth_node_of_root_lt E0 one (by omega)]
  rw [externalDepth_root]
  rw [externalDepth_node_of_lt_root comparisonLeft comparisonRight
    node_lt_globalRoot]
  rw [externalDepth_node_of_root_lt E0 one root_lt_node]
  omega

private theorem valueFour_right_interval_min
    {lower upper : External 6}
    (lower_gt : 5 < lower.val)
    (lower_le : lower.val ≤ 9)
    (upper_ge : 9 ≤ upper.val) :
    IsIntervalMin comparisonSnapshot.rank lower upper
      (⟨9, by omega⟩ : External 6) := by
  refine ⟨?_, ?_, ?_⟩
  · change lower.val ≤ 9
    exact lower_le
  · change 9 ≤ upper.val
    exact upper_ge
  intro node nodeLower _
  have globalRoot_lt_node : 5 < node.val := by
    change lower.val ≤ node.val at nodeLower
    omega
  change externalDepth comparison 9 ≤
    externalDepth comparison node.val
  rw [externalDepth_node_of_root_lt comparisonLeft comparisonRight
    (by omega)]
  rw [externalDepth_root]
  rw [externalDepth_node_of_root_lt comparisonLeft comparisonRight
    globalRoot_lt_node]
  omega

abbrev nodeAt
    {lower root upper : ℕ}
    (left : BST lower root) (right : BST (root + 1) upper)
    (upper_le : upper ≤ 6) : AtNode 6 where
  lower := lower
  root := root
  upper := upper
  left := left
  right := right
  upper_le_n := upper_le

theorem before_root_heavy :
    (nodeAt
      (.node E0
        (.node E1 (.node (.node E2 E3) four)))
      E6 (by omega)).heavyBranch comparisonSnapshot = .left := by
  apply heavyBranch_eq_of_explicitMin
    (candidate := (⟨5, by omega⟩ : External 6))
  · exact valueTwo_global_min
  · simp [TernaryBranch.Contains]

theorem before_zero_heavy :
    (nodeAt E0
      (.node E1 (.node (.node E2 E3) four))
      (by omega)).heavyBranch comparisonSnapshot = .right := by
  apply heavyBranch_eq_of_explicitMin
    (candidate := (⟨5, by omega⟩ : External 6))
  · apply valueTwo_interval_min <;> simp
  · simp [TernaryBranch.Contains]

theorem before_one_heavy :
    (nodeAt E1
      (.node (.node E2 E3) four)
      (by omega)).heavyBranch comparisonSnapshot = .right := by
  apply heavyBranch_eq_of_explicitMin
    (candidate := (⟨5, by omega⟩ : External 6))
  · apply valueTwo_interval_min <;> simp
  · simp [TernaryBranch.Contains]

theorem before_three_heavy :
    (nodeAt (.node E2 E3) four
      (by omega)).heavyBranch comparisonSnapshot = .left := by
  apply heavyBranch_eq_of_explicitMin
    (candidate := (⟨5, by omega⟩ : External 6))
  · apply valueTwo_interval_min <;> simp
  · simp [TernaryBranch.Contains]

theorem before_two_heavy :
    (nodeAt E2 E3
      (by omega)).heavyBranch comparisonSnapshot = .middle := by
  apply heavyBranch_eq_of_explicitMin
    (candidate := (⟨5, by omega⟩ : External 6))
  · apply valueTwo_interval_min <;> simp
  · simp [TernaryBranch.Contains]

theorem four_heavy :
    (nodeAt E4 E5
      (by omega)).heavyBranch comparisonSnapshot = .middle := by
  apply heavyBranch_eq_of_explicitMin
    (candidate := (⟨9, by omega⟩ : External 6))
  · apply valueFour_right_interval_min <;> simp
  · simp [TernaryBranch.Contains]

theorem bends_before :
    bends comparisonSnapshot before =
      {(⟨0, by omega⟩ : Fin 6), (⟨3, by omega⟩ : Fin 6)} := by
  simp [bends, bendsFrom, before,
    before_root_heavy, before_zero_heavy, before_one_heavy,
    before_three_heavy, before_two_heavy, four_heavy,
    bendAt, Turns, childIncoming]

theorem middle_root_heavy :
    (nodeAt
      (.node E0 (.node one threeFour))
      E6 (by omega)).heavyBranch comparisonSnapshot = .left := by
  apply heavyBranch_eq_of_explicitMin
    (candidate := (⟨5, by omega⟩ : External 6))
  · exact valueTwo_global_min
  · simp [TernaryBranch.Contains]

theorem middle_zero_heavy :
    (nodeAt E0 (.node one threeFour)
      (by omega)).heavyBranch comparisonSnapshot = .right := by
  apply heavyBranch_eq_of_explicitMin
    (candidate := (⟨5, by omega⟩ : External 6))
  · apply valueTwo_interval_min <;> simp
  · simp [TernaryBranch.Contains]

theorem middle_two_heavy :
    (nodeAt one threeFour
      (by omega)).heavyBranch comparisonSnapshot = .middle := by
  apply heavyBranch_eq_of_explicitMin
    (candidate := (⟨5, by omega⟩ : External 6))
  · apply valueTwo_interval_min <;> simp
  · simp [TernaryBranch.Contains]

theorem one_heavy :
    (nodeAt E1 E2
      (by omega)).heavyBranch comparisonSnapshot = .middle := by
  apply heavyBranch_eq_of_explicitMin
    (candidate := (⟨3, by omega⟩ : External 6))
  · exact valueOne_interval_min
  · simp [TernaryBranch.Contains]

theorem three_heavy :
    (nodeAt E3 four
      (by omega)).heavyBranch comparisonSnapshot = .right := by
  apply heavyBranch_eq_of_explicitMin
    (candidate := (⟨9, by omega⟩ : External 6))
  · apply valueFour_right_interval_min <;> simp
  · simp [TernaryBranch.Contains]

theorem bends_middle :
    bends comparisonSnapshot middle =
      {(⟨0, by omega⟩ : Fin 6)} := by
  simp [bends, bendsFrom, middle,
    middle_root_heavy, middle_zero_heavy, middle_two_heavy,
    one_heavy, three_heavy, four_heavy,
    bendAt, Turns, childIncoming]

theorem after_root_heavy :
    (nodeAt
      (.node E0 one)
      (.node threeFour E6)
      (by omega)).heavyBranch comparisonSnapshot = .middle := by
  apply heavyBranch_eq_of_explicitMin
    (candidate := (⟨5, by omega⟩ : External 6))
  · exact valueTwo_global_min
  · simp [TernaryBranch.Contains]

theorem after_zero_heavy :
    (nodeAt E0 one
      (by omega)).heavyBranch comparisonSnapshot = .middle := by
  apply heavyBranch_eq_of_explicitMin
    (candidate := (⟨1, by omega⟩ : External 6))
  · exact valueZero_left_interval_min
  · simp [TernaryBranch.Contains]

theorem after_five_heavy :
    (nodeAt threeFour E6
      (by omega)).heavyBranch comparisonSnapshot = .left := by
  apply heavyBranch_eq_of_explicitMin
    (candidate := (⟨9, by omega⟩ : External 6))
  · apply valueFour_right_interval_min <;> simp
  · simp [TernaryBranch.Contains]

theorem bends_after :
    bends comparisonSnapshot after =
      {(⟨3, by omega⟩ : Fin 6)} := by
  simp [bends, bendsFrom, after,
    after_root_heavy, after_zero_heavy, one_heavy,
    after_five_heavy, three_heavy, four_heavy,
    bendAt, Turns, childIncoming]

/-- Concrete constants sufficient for all individual steps in the example. -/
abbrev constants : BendConstants where
  initial := 0
  splay := 7
  comparisonRotation := 0

/--
The canonical chronological finite witness for the serving comparison tree.
Every one of its two zig-zag actions is locally sound.
-/
noncomputable def witness :
    SplayExecutionFiniteBendWitness
      constants comparisonSnapshot transcript :=
  SplayExecutionTranscript.finiteBendWitness
    (constants := constants)
    (key := (⟨2, by omega⟩ : Fin 6))
    transcript comparison comparison_hasRoot (by decide)

/--
Endpoint set difference sees only bend `0`: bend `3` was removed by the
first zig-zag and recreated by the second.
-/
theorem endpoint_removed_eq_one :
    witness.wholeSplayAction.removed = 1 := by
  simp [SplayExecutionFiniteBendWitness.wholeSplayAction,
    BendAction.between, bends_before, bends_after]

/-- The endpoint action records the transcript's exact two zig-zags. -/
theorem endpoint_zigZag_eq_two :
    witness.wholeSplayAction.zigZag = 2 := by
  rfl

/--
The collapsed endpoint action is not locally sound: it has two zig-zags but
only one endpoint-persistent removed bend.
-/
theorem endpoint_not_locallySound :
    ¬ witness.wholeSplayAction.LocallySound constants := by
  intro sound
  have removal := sound.1
  rw [endpoint_zigZag_eq_two, endpoint_removed_eq_one] at removal
  omega

/--
Formal refutation of the former endpoint aggregation residue, even though
the comparison tree serves the accessed key and every chronological action
is locally sound.
-/
theorem not_wholeSplayAggregationLaw :
    ¬ SplayExecutionFiniteBendWitness.WholeSplayAggregationLaw witness := by
  intro aggregation
  exact endpoint_not_locallySound
    (aggregation witness.all_actions_locallySound)

/--
The multiplicity-preserving replacement keeps both removal events and hence
does satisfy the unconditional zig-zag removal half.
-/
theorem two_le_chronological_removed :
    2 ≤ witness.chronologicalAction.removed :=
  witness.zigZag_le_chronological_removed

end Splay.Accounting.WholeSplayBendCounterexample
