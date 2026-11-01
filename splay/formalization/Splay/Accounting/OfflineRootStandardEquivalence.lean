import Splay.Accounting.OfflineOptimum

namespace Splay.Accounting.OfflineOptimum

open Splay.Tree.BST

namespace RotationExecution

/--
An ordinary rotation execution can be undone step for step, with exactly the
same rotation count.

The reverse order is important: after undoing the tail, the inverse of the
head rotation is appended at the end.
-/
protected theorem symm
    {length lower upper : ℕ}
    {before after : BST lower upper}
    (execution : RotationExecution length before after) :
    RotationExecution length after before := by
  induction execution with
  | refl =>
      exact .refl
  | step head tail ih =>
      simpa [Nat.succ_eq_add_one] using
        ih.append (RotationExecution.singleton head.symm)

end RotationExecution

/--
An offline execution in the standard search-cost BST model.

Before each request, arbitrary ordinary rotations may be performed.  The
request is then charged one plus its depth in the resulting tree.  The
natural-number index is the exact sum of rotation costs and search costs.

Putting rotations before rather than after a request is only a choice of
where to cut the intervals between consecutive requests.  It matches the
timing of `OfflineOptimum.Execution` and makes the model comparison exact.
-/
inductive StandardExecution {n : ℕ} :
    List (Fin n) → BST 0 n → BST 0 n → ℕ → Prop
  | done (tree : BST 0 n) :
      StandardExecution [] tree tree 0
  | next {access : Fin n} {accesses : List (Fin n)}
      {before served after : BST 0 n}
      {prefixRotations tailCost : ℕ}
      (prefixExecution :
        RotationExecution prefixRotations before served)
      (tail :
        StandardExecution accesses served after tailCost) :
      StandardExecution (access :: accesses) before after
        (prefixRotations + (1 + served.depth access.val) + tailCost)

namespace Execution

/--
Every root-model execution is a standard-model execution of exactly the same
total cost.  Its searches have depth zero, so only the mandatory request unit
and the already-recorded rotations remain.
-/
theorem toStandardExecution
    {n rotations : ℕ}
    {accesses : List (Fin n)}
    {before after : BST 0 n}
    (execution : Execution accesses before after rotations) :
    StandardExecution accesses before after
      (accesses.length + rotations) := by
  induction execution with
  | done tree =>
      exact .done tree
  | @next access accesses before served after
      prefixRotations tailRotations prefixExecution root tail ih =>
      have depthZero : served.depth access.val = 0 :=
        depth_eq_zero_of_hasRoot root
      have built :=
        StandardExecution.next (access := access) prefixExecution ih
      simpa [depthZero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using built

end Execution

namespace StandardExecution

/--
A standard-model execution can be simulated in the root model with at most a
factor-two increase in total cost.

At a request of depth `d`, splay the requested key to the root using exactly
`d` rotations.  If another request follows, undo those rotations before
simulating the standard tail.  The last undo is unnecessary because the
offline final tree is unconstrained.  Existing standard-model rotations are
copied verbatim.

The target final tree is existential because omitting that last undo can
change the endpoint, while never changing the served request sequence.
-/
theorem exists_rootExecution
    {n cost : ℕ}
    {accesses : List (Fin n)}
    {before after : BST 0 n}
    (execution : StandardExecution accesses before after cost) :
    ∃ (targetAfter : BST 0 n) (rotations : ℕ),
      Execution accesses before targetAfter rotations ∧
        accesses.length + rotations ≤ 2 * cost := by
  induction execution with
  | done tree =>
      exact ⟨tree, 0, .done tree, by simp⟩
  | @next access accesses before served after
      prefixRotations tailCost prefixExecution tail ih =>
      obtain ⟨rooted, splay⟩ :=
        SplayExecution.exists_splay served
          (Nat.zero_le access.val) access.isLt
      have toRoot :
          RotationExecution (served.depth access.val) served rooted :=
        splay.toRotationExecution
      have headPrefix :
          RotationExecution
            (prefixRotations + served.depth access.val)
            before rooted :=
        prefixExecution.append toRoot
      by_cases noTail : accesses = []
      · subst accesses
        cases tail with
        | done =>
            have targetExecution :
                Execution [access] before rooted
                  (prefixRotations + served.depth access.val) := by
              simpa using
                (Execution.next
                  (access := access)
                  (prefixRotations :=
                    prefixRotations + served.depth access.val)
                  (tailRotations := 0)
                  headPrefix splay.hasRoot_after (.done rooted))
            refine
              ⟨rooted, prefixRotations + served.depth access.val,
                targetExecution, ?_⟩
            simp only [List.length_cons, List.length_nil]
            omega
      · obtain
          ⟨targetAfter, tailRotations, targetTail, tailBound⟩ := ih
        have undo :
            RotationExecution (served.depth access.val) rooted served :=
          Splay.Accounting.OfflineOptimum.RotationExecution.symm toRoot
        have targetTailFromRoot :
            Execution accesses rooted targetAfter
              (served.depth access.val + tailRotations) :=
          Execution.prependRotations noTail undo targetTail
        have targetExecution :
            Execution (access :: accesses) before targetAfter
              ((prefixRotations + served.depth access.val) +
                (served.depth access.val + tailRotations)) :=
          Execution.next
            (access := access)
            (prefixRotations :=
              prefixRotations + served.depth access.val)
            (tailRotations :=
              served.depth access.val + tailRotations)
            headPrefix splay.hasRoot_after targetTailFromRoot
        refine
          ⟨targetAfter,
            (prefixRotations + served.depth access.val) +
              (served.depth access.val + tailRotations),
            targetExecution, ?_⟩
        simp only [List.length_cons]
        omega

/--
Endpoint-preserving form of the factor-two simulation.

`Execution` has no constructor for rotations after the last request.  This
theorem therefore returns such a final restoration explicitly.  Executing the
root trace and then `restore` reaches exactly the final tree of the source
standard execution, and the combined cost still has factor two.  This is the
literal formal counterpart of the manuscript instruction to undo the
access-to-root rotations after serving a request.
-/
theorem exists_rootExecution_with_restore
    {n cost : ℕ}
    {accesses : List (Fin n)}
    {before after : BST 0 n}
    (execution : StandardExecution accesses before after cost) :
    ∃ (targetAfter : BST 0 n)
        (rotations restoreRotations : ℕ),
      Execution accesses before targetAfter rotations ∧
        RotationExecution restoreRotations targetAfter after ∧
        accesses.length + rotations + restoreRotations ≤ 2 * cost := by
  induction execution with
  | done tree =>
      exact ⟨tree, 0, 0, .done tree, .refl, by simp⟩
  | @next access accesses before served after
      prefixRotations tailCost prefixExecution tail ih =>
      obtain ⟨rooted, splay⟩ :=
        SplayExecution.exists_splay served
          (Nat.zero_le access.val) access.isLt
      have toRoot :
          RotationExecution (served.depth access.val) served rooted :=
        splay.toRotationExecution
      have undo :
          RotationExecution (served.depth access.val) rooted served :=
        Splay.Accounting.OfflineOptimum.RotationExecution.symm toRoot
      have headPrefix :
          RotationExecution
            (prefixRotations + served.depth access.val)
            before rooted :=
        prefixExecution.append toRoot
      by_cases noTail : accesses = []
      · subst accesses
        cases tail with
        | done =>
            have targetExecution :
                Execution [access] before rooted
                  (prefixRotations + served.depth access.val) := by
              simpa using
                (Execution.next
                  (access := access)
                  (prefixRotations :=
                    prefixRotations + served.depth access.val)
                  (tailRotations := 0)
                  headPrefix splay.hasRoot_after (.done rooted))
            refine
              ⟨rooted,
                prefixRotations + served.depth access.val,
                served.depth access.val,
                targetExecution, undo, ?_⟩
            simp only [List.length_cons, List.length_nil]
            omega
      · obtain
          ⟨targetAfter, tailRotations, restoreRotations,
            targetTail, restore, tailBound⟩ := ih
        have targetTailFromRoot :
            Execution accesses rooted targetAfter
              (served.depth access.val + tailRotations) :=
          Execution.prependRotations noTail undo targetTail
        have targetExecution :
            Execution (access :: accesses) before targetAfter
              ((prefixRotations + served.depth access.val) +
                (served.depth access.val + tailRotations)) :=
          Execution.next
            (access := access)
            (prefixRotations :=
              prefixRotations + served.depth access.val)
            (tailRotations :=
              served.depth access.val + tailRotations)
            headPrefix splay.hasRoot_after targetTailFromRoot
        refine
          ⟨targetAfter,
            (prefixRotations + served.depth access.val) +
              (served.depth access.val + tailRotations),
            restoreRotations,
            targetExecution, restore, ?_⟩
        simp only [List.length_cons]
        omega

end StandardExecution

/-- The total costs attained by standard-model executions. -/
def FeasibleStandardCost {n : ℕ}
    (accesses : List (Fin n)) (cost : ℕ) : Prop :=
  ∃ (initial final : BST 0 n),
    StandardExecution accesses initial final cost

/-- Every request sequence has a standard-model execution. -/
theorem exists_feasibleStandardCost
    {n : ℕ} (accesses : List (Fin n)) :
    ∃ cost, FeasibleStandardCost accesses cost := by
  obtain ⟨initial, final, rotations, rootExecution, costEq⟩ :=
    exists_optimalExecution_eq accesses
  refine
    ⟨accesses.length + rotations, initial, final,
      rootExecution.toStandardExecution⟩

/-- The attained optimum in the standard search-cost model. -/
noncomputable def standardOptCost
    {n : ℕ} (accesses : List (Fin n)) : ℕ :=
  by
    classical
    exact Nat.find (exists_feasibleStandardCost accesses)

/-- The standard optimum is attained by a concrete execution. -/
theorem standardOptCost_feasible
    {n : ℕ} (accesses : List (Fin n)) :
    FeasibleStandardCost accesses (standardOptCost accesses) := by
  classical
  exact Nat.find_spec (exists_feasibleStandardCost accesses)

/-- The standard optimum is below every feasible standard execution. -/
theorem standardOptCost_le
    {n cost : ℕ} {accesses : List (Fin n)}
    (feasible : FeasibleStandardCost accesses cost) :
    standardOptCost accesses ≤ cost := by
  classical
  simpa [standardOptCost] using
    Nat.find_min' (exists_feasibleStandardCost accesses) feasible

/--
The standard-model optimum is no larger than the root-model optimum, because
every root execution is a same-cost standard execution.
-/
theorem standardOptCost_le_offlineOptCost
    {n : ℕ} (accesses : List (Fin n)) :
    standardOptCost accesses ≤ offlineOptCost accesses := by
  obtain ⟨initial, final, rotations, rootExecution, costEq⟩ :=
    exists_optimalExecution_eq accesses
  have feasible :
      FeasibleStandardCost accesses (accesses.length + rotations) :=
    ⟨initial, final, rootExecution.toStandardExecution⟩
  rw [costEq]
  exact standardOptCost_le feasible

/--
Conversely, the root-model optimum is at most twice the standard-model
optimum.  Together with `standardOptCost_le_offlineOptCost`, this is the
kernel-checked Appendix model-equivalence theorem.
-/
theorem offlineOptCost_le_two_mul_standardOptCost
    {n : ℕ} (accesses : List (Fin n)) :
    offlineOptCost accesses ≤ 2 * standardOptCost accesses := by
  obtain ⟨initial, final, standardExecution⟩ :=
    standardOptCost_feasible accesses
  obtain
    ⟨targetAfter, rotations, rootExecution, rootCostBound⟩ :=
    standardExecution.exists_rootExecution
  calc
    offlineOptCost accesses ≤ accesses.length + rotations :=
      offlineOptCost_le_ofExecution rootExecution
    _ ≤ 2 * standardOptCost accesses :=
      rootCostBound

/--
Unrestricted preparation rotations can occur at arbitrarily large depth below
an already-rooted request.

For every `depth`, the witness serves a single request at an unchanged root
while performing one rotation at depth `depth + 1`.  The construction wraps a
smaller witness below a new maximum root, so the rotation depth increases
without increasing the recorded rotation count.

As with the fixed four-key witness in
`OfflineStructuralExecutionNormalForm`, these executions are deliberately not
claimed optimal.  The family rules out obtaining a bounded-depth or
root-connected support premise merely by eliminating the constructors of the
active execution type; an optimal-execution normalization theorem is genuinely
needed.
-/
theorem exists_rootedAccessExecution_with_unboundedPreparationDepth
    (depth : ℕ) :
    ∃ (n : ℕ), 0 < n ∧
      ∃ (access : Fin n) (before after : BST 0 n),
        RotationAt depth.succ before after ∧
          before.HasRoot access.val ∧
          after.HasRoot access.val ∧
          Execution [access] before after 1 := by
  induction depth with
  | zero =>
      let empty0 : BST 0 0 := .empty 0
      let empty1 : BST 1 1 := .empty 1
      let empty2 : BST 2 2 := .empty 2
      let empty3 : BST 3 3 := .empty 3
      let beforeLeft : BST 0 2 :=
        .node empty0 (.node empty1 empty2)
      let afterLeft : BST 0 2 :=
        .node (.node empty0 empty1) empty2
      let before : BST 0 3 :=
        .node beforeLeft empty3
      let after : BST 0 3 :=
        .node afterLeft empty3
      let access : Fin 3 := ⟨2, by omega⟩
      have rotation : RotationAt 1 before after := by
        exact
          .leftContext
            (.root (.left empty0 empty1 empty2))
            empty3
      have beforeRoot : before.HasRoot access.val := by
        exact ⟨beforeLeft, empty3, rfl⟩
      have afterRoot : after.HasRoot access.val := by
        exact ⟨afterLeft, empty3, rfl⟩
      have execution : Execution [access] before after 1 := by
        simpa using
          (Execution.next
            (access := access)
            (prefixRotations := 1)
            (tailRotations := 0)
            (RotationExecution.singleton rotation)
            afterRoot
            (.done after))
      exact
        ⟨3, by omega, access, before, after,
          rotation, beforeRoot, afterRoot, execution⟩
  | succ depth ih =>
      obtain
        ⟨n, n_pos, access, before, after,
          rotation, beforeRoot, afterRoot, execution⟩ := ih
      let empty : BST (n + 1) (n + 1) := .empty (n + 1)
      let wrappedBefore : BST 0 (n + 1) :=
        .node before empty
      let wrappedAfter : BST 0 (n + 1) :=
        .node after empty
      let wrappedAccess : Fin (n + 1) :=
        ⟨n, Nat.lt_succ_self n⟩
      have wrappedRotation :
          RotationAt depth.succ.succ wrappedBefore wrappedAfter := by
        exact .leftContext rotation empty
      have wrappedBeforeRoot :
          wrappedBefore.HasRoot wrappedAccess.val := by
        exact ⟨before, empty, rfl⟩
      have wrappedAfterRoot :
          wrappedAfter.HasRoot wrappedAccess.val := by
        exact ⟨after, empty, rfl⟩
      have wrappedExecution :
          Execution [wrappedAccess] wrappedBefore wrappedAfter 1 := by
        simpa using
          (Execution.next
            (access := wrappedAccess)
            (prefixRotations := 1)
            (tailRotations := 0)
            (RotationExecution.singleton wrappedRotation)
            wrappedAfterRoot
            (.done wrappedAfter))
      exact
        ⟨n + 1, by omega, wrappedAccess, wrappedBefore, wrappedAfter,
          wrappedRotation, wrappedBeforeRoot, wrappedAfterRoot,
          wrappedExecution⟩

end Splay.Accounting.OfflineOptimum
