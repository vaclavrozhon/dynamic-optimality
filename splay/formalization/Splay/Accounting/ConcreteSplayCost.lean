import Splay.Accounting.SemanticReduction
import Splay.Lazy.SplaySequenceTrace

namespace Splay.Accounting

open Splay.Tree.BST

abbrev BST := Splay.Tree.BST

set_option linter.unusedVariables false in
/--
The orientation of a contextual double rotation, propagated through its
surrounding search-tree context.

This relation lives in `Prop`: it can inspect the proof of
`DoubleRotationAt` without trying to compute data by eliminating a proof into
`Type`.
-/
inductive DoubleOrientationAt :
    Bool → {depth key lower upper : ℕ} →
      BST lower upper → BST lower upper → Prop
  | zigZigLeft
      {lower first second third upper : ℕ}
      (a : BST lower first)
      (b : BST (first + 1) second)
      (c : BST (second + 1) third)
      (d : BST (third + 1) upper) :
      DoubleOrientationAt true (depth := 0) (key := first)
        (.node (.node (.node a b) c) d)
        (.node a (.node b (.node c d)))
  | zigZigRight
      {lower first second third upper : ℕ}
      (a : BST lower first)
      (b : BST (first + 1) second)
      (c : BST (second + 1) third)
      (d : BST (third + 1) upper) :
      DoubleOrientationAt true (depth := 0) (key := third)
        (.node a (.node b (.node c d)))
        (.node (.node (.node a b) c) d)
  | zigZagLeftRight
      {lower first second third upper : ℕ}
      (a : BST lower first)
      (b : BST (first + 1) second)
      (c : BST (second + 1) third)
      (d : BST (third + 1) upper) :
      DoubleOrientationAt false (depth := 0) (key := second)
        (.node (.node a (.node b c)) d)
        (.node (.node a b) (.node c d))
  | zigZagRightLeft
      {lower first second third upper : ℕ}
      (a : BST lower first)
      (b : BST (first + 1) second)
      (c : BST (second + 1) third)
      (d : BST (third + 1) upper) :
      DoubleOrientationAt false (depth := 0) (key := second)
        (.node a (.node (.node b c) d))
        (.node (.node a b) (.node c d))
  | leftContext
      {isZigZig : Bool} {depth key lower root upper : ℕ}
      {before after : BST lower root}
      (step :
        DoubleOrientationAt isZigZig
          (depth := depth) (key := key) before after)
      (right : BST (root + 1) upper) :
      DoubleOrientationAt isZigZig
        (depth := depth.succ) (key := key)
        (.node before right) (.node after right)
  | rightContext
      {isZigZig : Bool} {depth key lower root upper : ℕ}
      (left : BST lower root)
      {before after : BST (root + 1) upper}
      (step :
        DoubleOrientationAt isZigZig
          (depth := depth) (key := key) before after) :
      DoubleOrientationAt isZigZig
        (depth := depth.succ) (key := key)
        (.node left before) (.node left after)

/-- Every genuine contextual double rotation has its actual orientation. -/
theorem exists_doubleOrientationAt
    {depth key lower upper : ℕ} {before after : BST lower upper}
    (step : DoubleRotationAt depth key before after) :
    ∃ isZigZig : Bool,
      DoubleOrientationAt isZigZig
        (depth := depth) (key := key) before after := by
  induction step with
  | root step =>
      cases step with
      | zigZigLeft a b c d =>
          exact ⟨true, .zigZigLeft a b c d⟩
      | zigZigRight a b c d =>
          exact ⟨true, .zigZigRight a b c d⟩
      | zigZagLeftRight a b c d =>
          exact ⟨false, .zigZagLeftRight a b c d⟩
      | zigZagRightLeft a b c d =>
          exact ⟨false, .zigZagRightLeft a b c d⟩
  | leftContext step right ih =>
      obtain ⟨isZigZig, orientation⟩ := ih
      exact ⟨isZigZig, .leftContext orientation right⟩
  | rightContext left step ih =>
      obtain ⟨isZigZig, orientation⟩ := ih
      exact ⟨isZigZig, .rightContext left orientation⟩

/--
Exact counts of final zigs and the two genuine double-rotation orientations
in one complete splay execution.
-/
inductive SplayExecutionCounts (key : ℕ) :
    {lower upper : ℕ} → BST lower upper → BST lower upper →
      ℕ → ℕ → ℕ → Prop
  | done {lower upper : ℕ} {tree : BST lower upper}
      (root : tree.HasRoot key) :
      SplayExecutionCounts key tree tree 0 0 0
  | zig {lower upper : ℕ} {before middle after : BST lower upper}
      {zig zigZig zigZag : ℕ}
      (step : Zig key before middle)
      (tail :
        SplayExecutionCounts key middle after zig zigZig zigZag) :
      SplayExecutionCounts key before after
        (zig + 1) zigZig zigZag
  | zigZig {depth lower upper : ℕ}
      {before middle after : BST lower upper}
      {zig zigZig zigZag : ℕ}
      (step : DoubleRotationAt depth key before middle)
      (orientation :
        DoubleOrientationAt true
          (depth := depth) (key := key) before middle)
      (tail :
        SplayExecutionCounts key middle after zig zigZig zigZag) :
      SplayExecutionCounts key before after
        zig (zigZig + 1) zigZag
  | zigZag {depth lower upper : ℕ}
      {before middle after : BST lower upper}
      {zig zigZig zigZag : ℕ}
      (step : DoubleRotationAt depth key before middle)
      (orientation :
        DoubleOrientationAt false
          (depth := depth) (key := key) before middle)
      (tail :
        SplayExecutionCounts key middle after zig zigZig zigZag) :
      SplayExecutionCounts key before after
        zig zigZig (zigZag + 1)

namespace SplayExecutionCounts

/-- The counts recover the exact ordinary-rotation count of an execution. -/
theorem depth_eq_and_zig_le_one
    {key lower upper : ℕ} {before after : BST lower upper}
    {zig zigZig zigZag : ℕ}
    (counts :
      SplayExecutionCounts key before after zig zigZig zigZag) :
    before.depth key = zig + 2 * zigZig + 2 * zigZag ∧
      zig ≤ 1 := by
  induction counts with
  | done root =>
      simp [depth_eq_zero_of_hasRoot root]
  | @zig lower upper before middle after
      zig zigZig zigZag step tail ih =>
      have middleDepth := step.depth_after_eq_zero
      have tailZero :
          zig + 2 * zigZig + 2 * zigZag = 0 := by
        omega
      constructor
      · rw [step.depth_before_eq_one]
        omega
      · omega
  | @zigZig depth lower upper before middle after
      zig zigZig zigZag step orientation tail ih =>
      constructor
      · rw [step.depth_before_eq, step.depth_after_eq] at *
        omega
      · exact ih.2
  | @zigZag depth lower upper before middle after
      zig zigZig zigZag step orientation tail ih =>
      constructor
      · rw [step.depth_before_eq, step.depth_after_eq] at *
        omega
      · exact ih.2

end SplayExecutionCounts

/-- Every structural splay execution admits the exact orientation counts. -/
theorem splayExecution_exists_counts
    {key lower upper : ℕ} {before after : BST lower upper}
    (execution : SplayExecution key before after) :
    ∃ zig zigZig zigZag,
      SplayExecutionCounts key before after zig zigZig zigZag := by
  induction execution with
  | done root =>
      exact ⟨0, 0, 0, .done root⟩
  | next head tail ih =>
      obtain ⟨zig, zigZig, zigZag, tailCounts⟩ := ih
      cases head with
      | zig step =>
          exact
            ⟨zig + 1, zigZig, zigZag,
              .zig step tailCounts⟩
      | double step =>
          obtain ⟨isZigZig, orientation⟩ :=
            exists_doubleOrientationAt step
          cases isZigZig with
          | false =>
              exact
                ⟨zig, zigZig, zigZag + 1,
                  .zigZag step orientation tailCounts⟩
          | true =>
              exact
                ⟨zig, zigZig + 1, zigZag,
                  .zigZig step orientation tailCounts⟩

/--
Aggregating the real execution counts across a dependent splay sequence
recovers its exact ordinary-rotation count.  There is at most one final zig
per request.
-/
theorem splaySequence_exists_counts
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    (sequence : SplaySequence accesses before after) :
    ∃ zig zigZig zigZag,
      sequence.rotationCount =
        zig + 2 * zigZig + 2 * zigZag ∧
      zig ≤ accesses.length := by
  induction sequence with
  | done tree =>
      exact ⟨0, 0, 0, by simp⟩
  | @next access accesses before middle after head tail ih =>
      obtain ⟨headZig, headZigZig, headZigZag, headCounts⟩ :=
        splayExecution_exists_counts head
      have headProperties :=
        headCounts.depth_eq_and_zig_le_one
      obtain ⟨tailZig, tailZigZig, tailZigZag,
          tailRotations, tailZigBound⟩ := ih
      refine
        ⟨headZig + tailZig,
          headZigZig + tailZigZig,
          headZigZag + tailZigZag, ?_, ?_⟩
      · rw [SplaySequence.rotationCount_next,
          headProperties.1, tailRotations]
        omega
      · simp only [List.length_cons]
        omega

/-- A chosen structural sequence witnessing the deterministic cost model. -/
noncomputable def chosenSplaySequenceWitness
    {n : ℕ} (initial : BST 0 n) (accesses : List (Fin n)) :
    Σ final : BST 0 n,
      SplaySequence accesses initial final := by
  classical
  let existence :=
    SplaySequence.exists_sequence initial accesses
  let final := Classical.choose existence
  let sequence :=
    Classical.choice (Classical.choose_spec existence)
  exact ⟨final, sequence⟩

noncomputable def chosenSplaySequence
    {n : ℕ} (initial : BST 0 n) (accesses : List (Fin n)) :
    SplaySequence accesses initial
      (chosenSplaySequenceWitness initial accesses).1 :=
  (chosenSplaySequenceWitness initial accesses).2

/--
A concrete BST cost model.  Its splay cost is one unit per request plus the
exact number of ordinary rotations in a fixed chosen standard splay sequence.
This generic constructor accepts the comparison cost as a parameter;
`Accounting.OfflineOptimum.concreteOfflineCostModel` later instantiates it
with the attained root-based offline rotation optimum.
-/
noncomputable def concreteSplayCost
    {n : ℕ} (initial : BST 0 n) (accesses : List (Fin n)) : ℕ :=
  accesses.length +
    (chosenSplaySequence initial accesses).rotationCount

noncomputable def concreteSplayCostModel
    (optCost : {n : ℕ} → List (Fin n) → ℕ) : CostModel where
  Initial := fun n => BST 0 n
  splayCost := concreteSplayCost
  optCost := optCost

/--
The minimal semantic cost witness used by accounting.  It records an actual
structural sequence, its real orientation counts, and the sole model-specific
law relating the external cost to that sequence.
-/
structure SplayCostRealization
    (splayCost : ℕ) {n : ℕ}
    (initial : BST 0 n) (accesses : List (Fin n)) where
  final : BST 0 n
  sequence : SplaySequence accesses initial final
  zig : ℕ
  zigZig : ℕ
  zigZag : ℕ
  rotations_eq :
    sequence.rotationCount =
      zig + 2 * zigZig + 2 * zigZag
  zig_le : zig ≤ accesses.length
  cost_le :
    splayCost ≤ accesses.length + sequence.rotationCount

namespace SplayCostRealization

/-- The witness discharges the semantic certificate's cost decomposition. -/
theorem cost_decomposition
    {splayCost : ℕ} {n : ℕ}
    {initial : BST 0 n} {accesses : List (Fin n)}
    (realization :
      SplayCostRealization splayCost initial accesses) :
    splayCost ≤
      accesses.length + accesses.length +
        2 * realization.zigZig + 2 * realization.zigZag := by
  calc
    splayCost ≤
        accesses.length + realization.sequence.rotationCount :=
      realization.cost_le
    _ = accesses.length +
          (realization.zig +
            2 * realization.zigZig +
            2 * realization.zigZag) := by
      rw [realization.rotations_eq]
    _ ≤ accesses.length + accesses.length +
          2 * realization.zigZig + 2 * realization.zigZag := by
      have zigLe := realization.zig_le
      omega

end SplayCostRealization

/--
The concrete model has a cost realization for every initial tree and request
list, with counts obtained from the actual chosen sequence orientations.
-/
theorem concreteSplayCostModel_realization
    (_optCost : {n : ℕ} → List (Fin n) → ℕ)
    {n : ℕ} (initial : BST 0 n) (accesses : List (Fin n)) :
    Nonempty
      (SplayCostRealization
        (concreteSplayCost initial accesses)
        initial accesses) := by
  let sequence := chosenSplaySequence initial accesses
  obtain ⟨zig, zigZig, zigZag, rotationsEq, zigLe⟩ :=
    splaySequence_exists_counts sequence
  exact
    ⟨{ final := (chosenSplaySequenceWitness initial accesses).1
       sequence := sequence
       zig := zig
       zigZig := zigZig
       zigZag := zigZag
       rotations_eq := rotationsEq
       zig_le := zigLe
       cost_le := by
         simp [concreteSplayCost, sequence] }⟩

@[simp]
theorem concreteSplayCostModel_splayCost
    (optCost : {n : ℕ} → List (Fin n) → ℕ)
    {n : ℕ} (initial : BST 0 n) (accesses : List (Fin n)) :
    @CostModel.splayCost
        (concreteSplayCostModel optCost) n initial accesses =
      concreteSplayCost initial accesses :=
  rfl

end Splay.Accounting
