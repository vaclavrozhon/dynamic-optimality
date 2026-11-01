import Splay.Accounting.ConcreteSplayCost
import Splay.Lazy.NormalFormSchedule

namespace Splay.Accounting.OfflineOptimum

open Splay.Tree.BST

abbrev BST := Splay.Tree.BST

/--
An offline root-based BST execution.

This is the rotation-only model stated in the active text of
`preliminaries.tex`: rotations may occur at any tree depth and each costs one.
The initial tree is supplied externally and is therefore free, as in the
competitive statement.  To serve the head request, the execution performs an
actual finite sequence of ordinary rotations and ends with the requested key
at the root.  The remaining requests continue from that same tree.

Only rotations are indexed here.  `offlineOptCost` below adds exactly one unit
for every served request.
-/
inductive Execution {n : ℕ} :
    List (Fin n) → BST 0 n → BST 0 n → ℕ → Prop
  | done (tree : BST 0 n) :
      Execution [] tree tree 0
  | next {access : Fin n} {accesses : List (Fin n)}
      {before served after : BST 0 n}
      {prefixRotations tailRotations : ℕ}
      (prefixExecution :
        RotationExecution prefixRotations before served)
      (root : served.HasRoot access.val)
      (tail :
        Execution accesses served after tailRotations) :
      Execution (access :: accesses) before after
        (prefixRotations + tailRotations)

namespace Execution

/--
A standard bottom-up splay sequence is, in particular, a valid offline BST
execution with exactly the same ordinary-rotation count.
-/
theorem ofSplaySequence
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    (sequence : SplaySequence accesses before after) :
    Execution accesses before after sequence.rotationCount := by
  induction sequence with
  | done tree =>
      exact .done tree
  | @next access accesses before middle after head tail ih =>
      rw [SplaySequence.rotationCount_next]
      exact .next head.toRotationExecution head.hasRoot_after ih

/--
The standard splay execution uses at most `n` rotations per request.  This is
a coarse but fully internal finite upper bound for the offline optimum.
-/
theorem splaySequence_rotationCount_le
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    (sequence : SplaySequence accesses before after) :
    sequence.rotationCount ≤ accesses.length * n := by
  induction sequence with
  | done tree =>
      simp
  | @next access accesses before middle after head tail ih =>
      rw [SplaySequence.rotationCount_next]
      have headDepth_le : before.depth access.val ≤ n := by
        calc
          before.depth access.val ≤ before.size :=
            before.depth_le_size access.val
          _ = n := before.size_eq_upper
      calc
        before.depth access.val + tail.rotationCount ≤
            n + accesses.length * n :=
          Nat.add_le_add headDepth_le ih
        _ = (access :: accesses).length * n := by
          simp [Nat.succ_mul, Nat.add_comm]

/-- Concatenation composes genuine executions and adds their rotation counts. -/
theorem append
    {n prefixRotations suffixRotations : ℕ}
    {firstRequests secondRequests : List (Fin n)}
    {before middle after : BST 0 n}
    (first :
      Execution firstRequests before middle prefixRotations)
    (second :
      Execution secondRequests middle after suffixRotations) :
    Execution (firstRequests ++ secondRequests) before after
      (prefixRotations + suffixRotations) := by
  induction first with
  | done tree =>
      simpa using second
  | @next access accesses before served middle
      headRotations tailRotations head root tail ih =>
      simpa [Nat.add_assoc] using
        (Execution.next head root (ih second))

/-- A list of requests already rooted in one tree needs no rotations. -/
theorem ofAllRooted
    {n : ℕ} {accesses : List (Fin n)}
    (tree : BST 0 n)
    (rooted :
      ∀ access ∈ accesses, tree.HasRoot access.val) :
    Execution accesses tree tree 0 := by
  induction accesses with
  | nil =>
      exact .done tree
  | cons access accesses ih =>
      have headRoot := rooted access (by simp)
      have tailRooted :
          ∀ request ∈ accesses, tree.HasRoot request.val := by
        intro request member
        exact rooted request (by simp [member])
      simpa using
        (Execution.next (.refl) headRoot (ih tailRooted))

/--
Rotations before a nonempty execution may be absorbed into the first access.
-/
theorem prependRotations
    {n prefixRotations tailRotations : ℕ}
    {accesses : List (Fin n)}
    {before middle after : BST 0 n}
    (nonempty : accesses ≠ [])
    (prefixExecution :
      RotationExecution prefixRotations before middle)
    (tail :
      Execution accesses middle after tailRotations) :
    Execution accesses before after
      (prefixRotations + tailRotations) := by
  cases tail with
  | done tree =>
      exact (nonempty rfl).elim
  | @next access accesses served firstServed after
      firstRotations restRotations first root rest =>
      simpa [Nat.add_assoc] using
        (Execution.next (prefixExecution.append first) root rest)

end Execution

namespace ComparisonTraceBridge

open Splay.Assumptions.NormalForm
open Splay.Assumptions.NormalForm.ComparisonTrace

/-- A request group contains at least one actual request key. -/
private theorem RequestGroup.requests_nonempty
    {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses}
    (group : RequestGroup trace) :
    group.requests ≠ [] := by
  simpa [RequestGroup.requests] using group.requestIndices_nonempty

/--
The chronological schedule of a comparison trace is itself a genuine offline
BST execution.  Rotations after the final request may be discarded, hence the
inequality rather than equality in the rotation count.
-/
theorem Schedule.exists_offlineExecution
    {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {beforeSplay afterSplay : BST 0 n}
    (schedule :
      Schedule trace groups time beforeSplay afterSplay) :
    ∃ (final : BST 0 n) (rotations : ℕ),
      Execution schedule.servedRequests
          (trace.state time) final rotations ∧
        rotations ≤ schedule.comparisonRotationCount := by
  induction schedule with
  | @finish time tree comparison =>
      exact
        ⟨trace.state time, 0, .done (trace.state time),
          Nat.zero_le _⟩
  | @next group groups time before middle after
      ordered comparison splay tail ih =>
      obtain ⟨final, tailRotations, tailExecution, tailBound⟩ := ih
      have groupExecution :
          Execution group.requests
            (trace.state group.time) (trace.state group.time) 0 :=
        Execution.ofAllRooted
          (trace.state group.time)
          (fun request member => group.serves member)
      have joined :
          Execution
            (group.requests ++ tail.servedRequests)
            (trace.state group.time) final
            (0 + tailRotations) :=
        groupExecution.append tailExecution
      have requestsNonempty :
          group.requests ++ tail.servedRequests ≠ [] :=
        List.append_ne_nil_of_left_ne_nil
          (RequestGroup.requests_nonempty group)
          tail.servedRequests
      have withPrefix :
          Execution
            (group.requests ++ tail.servedRequests)
            (trace.state time) final
            ((group.time.val - time.val) +
              (0 + tailRotations)) :=
        Execution.prependRotations
          requestsNonempty comparison joined
      refine
        ⟨final, group.time.val - time.val + tailRotations,
          ?_, ?_⟩
      · simpa [Schedule.servedRequests] using withPrefix
      · simp only [Schedule.comparisonRotationCount]
        exact Nat.add_le_add_left tailBound _

end ComparisonTraceBridge

/-- The rotation counts realized by genuine offline executions. -/
def FeasibleRotationCost {n : ℕ}
    (accesses : List (Fin n)) (rotations : ℕ) : Prop :=
  ∃ (initial final : BST 0 n),
    Execution accesses initial final rotations

/-- A canonical indexed BST, used only to witness nonemptiness. -/
def canonicalTree : (n : ℕ) → BST 0 n
  | 0 => .empty 0
  | n + 1 => .node (canonicalTree n) (.empty (n + 1))

/-- Every request sequence has at least one genuine offline execution. -/
theorem exists_feasibleRotationCost
    {n : ℕ} (accesses : List (Fin n)) :
    ∃ rotations, FeasibleRotationCost accesses rotations := by
  obtain ⟨final, ⟨sequence⟩⟩ :=
    SplaySequence.exists_sequence (canonicalTree n) accesses
  exact
    ⟨sequence.rotationCount, canonicalTree n, final,
      Execution.ofSplaySequence sequence⟩

/--
The exact offline optimum number of rotations.

This is a genuine minimum, not an infimum or an unconstrained cost annotation:
feasibility is inhabited above and `Nat.find` selects the least feasible
natural number.
-/
noncomputable def offlineRotationOpt
    {n : ℕ} (accesses : List (Fin n)) : ℕ :=
  by
    classical
    exact Nat.find (exists_feasibleRotationCost accesses)

/-- The selected minimum is attained by an actual BST execution. -/
theorem offlineRotationOpt_feasible
    {n : ℕ} (accesses : List (Fin n)) :
    FeasibleRotationCost accesses (offlineRotationOpt accesses) := by
  classical
  exact Nat.find_spec (exists_feasibleRotationCost accesses)

/-- The selected rotation count is no larger than any feasible one. -/
theorem offlineRotationOpt_le
    {n : ℕ} {accesses : List (Fin n)} {rotations : ℕ}
    (feasible : FeasibleRotationCost accesses rotations) :
    offlineRotationOpt accesses ≤ rotations := by
  classical
  simpa [offlineRotationOpt] using
    Nat.find_min' (exists_feasibleRotationCost accesses) feasible

/--
Root-based offline BST cost: one unit per request plus the least number of
actual rotations, with the initial tree chosen freely.
-/
noncomputable def offlineOptCost
    {n : ℕ} (accesses : List (Fin n)) : ℕ :=
  accesses.length + offlineRotationOpt accesses

/-- An optimal cost is realized by concrete initial/final trees and a trace. -/
theorem exists_optimalExecution
    {n : ℕ} (accesses : List (Fin n)) :
    ∃ (initial final : BST 0 n),
      Execution accesses initial final
        (offlineOptCost accesses - accesses.length) := by
  obtain ⟨initial, final, execution⟩ :=
    offlineRotationOpt_feasible accesses
  refine ⟨initial, final, ?_⟩
  simpa [offlineOptCost] using execution

/-- Every request contributes its mandatory unit to the offline cost. -/
theorem requests_le_offlineOptCost
    {n : ℕ} (accesses : List (Fin n)) :
    accesses.length ≤ offlineOptCost accesses := by
  simp [offlineOptCost]

/-- The optimum is below the cost of every genuine offline execution. -/
theorem offlineOptCost_le_ofExecution
    {n rotations : ℕ} {accesses : List (Fin n)}
    {initial final : BST 0 n}
    (execution : Execution accesses initial final rotations) :
    offlineOptCost accesses ≤ accesses.length + rotations := by
  exact Nat.add_le_add_left
    (offlineRotationOpt_le ⟨initial, final, execution⟩)
    accesses.length

/--
The optimum is both attained and equal to the ordinary request-plus-rotation
cost of its attaining execution.
-/
theorem exists_optimalExecution_eq
    {n : ℕ} (accesses : List (Fin n)) :
    ∃ (initial final : BST 0 n) (rotations : ℕ),
      Execution accesses initial final rotations ∧
        offlineOptCost accesses = accesses.length + rotations := by
  obtain ⟨initial, final, execution⟩ :=
    offlineRotationOpt_feasible accesses
  exact
    ⟨initial, final, offlineRotationOpt accesses, execution, rfl⟩

/-- The empty request sequence has exactly zero offline cost. -/
@[simp]
theorem offlineOptCost_nil (n : ℕ) :
    offlineOptCost ([] : List (Fin n)) = 0 := by
  have feasible : FeasibleRotationCost ([] : List (Fin n)) 0 :=
    ⟨canonicalTree n, canonicalTree n, .done (canonicalTree n)⟩
  have minimum : offlineRotationOpt ([] : List (Fin n)) ≤ 0 :=
    offlineRotationOpt_le feasible
  simp [offlineOptCost, Nat.eq_zero_of_le_zero minimum]

/-- A single request costs exactly its mandatory request unit. -/
@[simp]
theorem offlineOptCost_singleton
    {n : ℕ} (access : Fin n) :
    offlineOptCost [access] = 1 := by
  obtain ⟨served, splay⟩ :=
    SplayExecution.exists_splay (canonicalTree n)
      (Nat.zero_le access.val) access.isLt
  have feasible : FeasibleRotationCost [access] 0 :=
    ⟨served, served,
      .next (.refl) splay.hasRoot_after (.done served)⟩
  have minimum : offlineRotationOpt [access] ≤ 0 :=
    offlineRotationOpt_le feasible
  simp [offlineOptCost, Nat.eq_zero_of_le_zero minimum]

/-- Zero optimum occurs exactly for the empty request list. -/
theorem offlineOptCost_eq_zero_iff
    {n : ℕ} {accesses : List (Fin n)} :
    offlineOptCost accesses = 0 ↔ accesses = [] := by
  constructor
  · intro costZero
    have lengthZero : accesses.length = 0 := by
      have := requests_le_offlineOptCost accesses
      omega
    exact List.eq_nil_of_length_eq_zero lengthZero
  · rintro rfl
    exact offlineOptCost_nil n

/-- The optimum is no larger than any concrete standard splay execution. -/
theorem offlineOptCost_le_splaySequenceCost
    {n : ℕ} {accesses : List (Fin n)}
    {initial final : BST 0 n}
    (sequence : SplaySequence accesses initial final) :
    offlineOptCost accesses ≤
      accesses.length + sequence.rotationCount := by
  exact offlineOptCost_le_ofExecution
    (Execution.ofSplaySequence sequence)

/-- In particular, the optimum is below the repository's concrete splay cost. -/
theorem offlineOptCost_le_concreteSplayCost
    {n : ℕ} (initial : BST 0 n) (accesses : List (Fin n)) :
    offlineOptCost accesses ≤ concreteSplayCost initial accesses := by
  simpa [concreteSplayCost] using
    offlineOptCost_le_splaySequenceCost
      (chosenSplaySequence initial accesses)

/--
Every repository `ComparisonTrace` costs at least the genuine offline optimum.
This connects the new optimum to the exact trace type consumed by normal form.
-/
theorem offlineOptCost_le_comparisonTraceCost
    {n : ℕ} {accesses : List (Fin n)}
    (trace :
      Splay.Assumptions.NormalForm.ComparisonTrace n accesses) :
    offlineOptCost accesses ≤ trace.cost := by
  open Splay.Assumptions.NormalForm.ComparisonTrace in
    obtain
      ⟨groups, finalSplay, schedule, flattened, ordered,
        groupsRooted, comparisonCount⟩ :=
      trace.exists_normalFormSchedule (canonicalTree n)
  obtain ⟨final, rotations, execution, rotations_le⟩ :=
    ComparisonTraceBridge.Schedule.exists_offlineExecution schedule
  have executionOfAccesses :
      Execution accesses (trace.state 0) final rotations := by
    have requestsEq : schedule.servedRequests = accesses := by
      simpa
        [Splay.Assumptions.NormalForm.ComparisonTrace.Schedule.servedRequests]
        using flattened
    exact Eq.mp
      (congrArg
        (fun requests =>
          Execution requests (trace.state 0) final rotations)
        requestsEq)
      execution
  calc
    offlineOptCost accesses ≤ accesses.length + rotations :=
      offlineOptCost_le_ofExecution executionOfAccesses
    _ ≤ accesses.length + trace.rotationCount := by
      apply Nat.add_le_add_left
      rw [← comparisonCount]
      exact rotations_le
    _ = trace.cost := rfl

/-- A uniform finite upper bound, independent of the chosen initial tree. -/
theorem offlineOptCost_le_requestBound
    {n : ℕ} (accesses : List (Fin n)) :
    offlineOptCost accesses ≤
      accesses.length + accesses.length * n := by
  let sequence :=
    chosenSplaySequence (canonicalTree n) accesses
  calc
    offlineOptCost accesses ≤
        accesses.length + sequence.rotationCount :=
      offlineOptCost_le_splaySequenceCost sequence
    _ ≤ accesses.length + accesses.length * n :=
      Nat.add_le_add_left
        (Execution.splaySequence_rotationCount_le sequence)
        accesses.length

/-- The concrete splay model instantiated with the genuine offline optimum. -/
noncomputable def concreteOfflineCostModel : CostModel :=
  concreteSplayCostModel offlineOptCost

@[simp]
theorem concreteOfflineCostModel_optCost
    {n : ℕ} (accesses : List (Fin n)) :
    @CostModel.optCost concreteOfflineCostModel n accesses =
      offlineOptCost accesses :=
  rfl

end Splay.Accounting.OfflineOptimum
