import Splay.Accounting.ArticleHistoryTranscript
import Splay.Lazy.CanonicalInitializationCost
import Splay.Interface.InitialColumnIncidenceAssembly

namespace Splay.Accounting

open Splay.Rank Splay.Tree.BST Splay.Lazy Splay.Lazy.Canonical Splay.Assumptions.NormalForm

/-- A complete run includes its actual canonical initialization and the
entire chronological schedule of comparison rotations and splay requests. -/
structure ArticleInitializedExecution {n : ℕ} (params : Interface.Parameters) (bounds : StructuralBounds)
    {accesses : List (Fin n)} (comparison : ComparisonTrace n accesses) (tree : BST 0 n) where
  growingLimit : 2 ≤ params.growingLimit
  initialValueBound : Analysis.contractedGap (Snapshot.ofTree comparison.initialTree).withTruePriority.maxRank ≤ params.valueBound
  finalTree : BST 0 n
  execution : ArticleChronologicalExecution params
    ⟨comparison.initialTree, tree, canonicalState (Snapshot.ofTree comparison.initialTree).withTruePriority tree⟩
    comparison.finalTree finalTree accesses comparison.rotationCount
    (articleRequestBirthBudget bounds.neighborDepthSlack) (articleFullComparisonBirthBudget bounds.maxRotationDepth)

namespace ArticleInitializedExecution

variable {n : ℕ} {params : Interface.Parameters} {bounds : StructuralBounds}
  {accesses : List (Fin n)} {comparison : ComparisonTrace n accesses} {tree : BST 0 n}
  (run : ArticleInitializedExecution params bounds comparison tree)

noncomputable def initial (_run : ArticleInitializedExecution params bounds comparison tree) : Lazy.State n :=
  emptyCanonicalState (Snapshot.ofTree comparison.initialTree).withTruePriority tree

noncomputable def final : Lazy.State n := run.execution.final

noncomputable def events : List (Event n) := canonicalInitializationEvents
  (Snapshot.ofTree comparison.initialTree).withTruePriority tree ++ run.execution.history.events

noncomputable def operations : List (Interface.Operation n) := eraseOperations run.events

noncomputable def goodCount : ℕ := run.execution.history.goodCount

noncomputable def boundaryCount : ℕ := run.execution.history.boundaryCount

theorem trace : Trace params run.initial run.events run.final :=
  (emptyCanonicalState_canonicalState_trace _ tree params run.growingLimit run.initialValueBound).append run.execution.history.trace

theorem initialState : run.initial.toInterface.Initial params :=
  emptyCanonicalState_toInterface_initial _ tree params run.initialValueBound

theorem represented : run.final.Represents params (Snapshot.ofTree comparison.finalTree).withTruePriority run.finalTree :=
  run.execution.represents

theorem blocks : run.final.blocks.length ≤ (2 * n + 1) * 2 +
    articleRequestBirthBudget bounds.neighborDepthSlack * accesses.length +
    articleFullComparisonBirthBudget bounds.maxRotationDepth * comparison.rotationCount := by
  simpa only [final, canonicalState_blocks_length] using run.execution.births

/-- Append-only block storage counts every historical creation, including
blocks subsequently emptied by splits or deletion. -/
theorem totalBlockGrowth_eq : Interface.totalBlockGrowth run.operations = run.final.blocks.length := by
  have count := run.trace.blocks_length_eq
  simpa only [initial, emptyCanonicalState_blocks, List.length_nil, Nat.zero_add, operations] using count.symm

theorem good_le : run.goodCount ≤ (2 * n + 1) * params.valueBound +
    8 * params.valueBound * run.boundaryCount + 3 * params.valueBound * comparison.rotationCount := by
  have paid := run.execution.history.gap_pays_good
  rw [run.execution.rotations_eq] at paid
  have initialBound := geometricGapPotential_le (canonicalState_represents
    (Snapshot.ofTree comparison.initialTree).withTruePriority tree params run.growingLimit run.initialValueBound).stable
  change geometricGapPotential run.execution.final + run.goodCount ≤ geometricGapPotential
    (canonicalState (Snapshot.ofTree comparison.initialTree).withTruePriority tree) +
    8 * params.valueBound * run.boundaryCount + 3 * params.valueBound * comparison.rotationCount at paid
  omega

theorem inserts : Interface.totalInserts run.operations ≤ 2 * n + 1 + comparison.rotationCount + 2 * run.boundaryCount := by
  have setup := canonicalInitializationEvents_inserts (Snapshot.ofTree comparison.initialTree).withTruePriority tree
  have later := run.execution.history.inserts
  rw [run.execution.rotations_eq] at later
  simp only [operations, events, eraseOperations_append, Interface.totalInserts_append, boundaryCount]
  omega

/-- The geometric telescope pays all good passes; only initialization,
comparison rotations and boundary rows remain in the value-increase budget. -/
theorem increases : Interface.totalIncreases run.operations ≤
    4 * params.valueBound * (2 * n + 1) + 16 * params.valueBound * run.boundaryCount +
      6 * params.valueBound * comparison.rotationCount := by
  have setup := canonicalInitializationEvents_increases (Snapshot.ofTree comparison.initialTree).withTruePriority tree params run.initialValueBound
  have later := run.execution.history.increases
  rw [run.execution.rotations_eq] at later
  have good := run.good_le
  change Interface.totalIncreases (eraseOperations run.execution.history.events) ≤ run.goodCount +
    8 * params.valueBound * run.boundaryCount + 3 * params.valueBound * comparison.rotationCount at later
  simp only [operations, events, eraseOperations_append, Interface.totalIncreases_append]
  nlinarith

theorem activity_eq : Interface.totalActivity run.operations =
    Interface.totalActivity (eraseOperations run.execution.history.events) := by
  simp only [operations, events, eraseOperations_append, Interface.totalActivity_append,
    canonicalInitializationEvents_activity, Nat.zero_add]

theorem zigZigs : 2 * (concreteSplayTranscript tree accesses).zigZig ≤
    Interface.totalActivity run.operations + comparison.rotationCount + 2 * run.boundaryCount := by
  rw [run.activity_eq]
  exact run.execution.concrete_zigZigs_le_activity_add_boundary

theorem valueChanges : Interface.totalValueChanges run.operations ≤
    9 * params.valueBound * (2 * n + 1) + 32 * params.valueBound * run.boundaryCount +
      12 * params.valueBound * comparison.rotationCount := by
  have values := run.trace.toInterface.totalValueChanges_le run.initialState.1
  have increases := run.increases
  change Interface.totalValueChanges run.operations ≤ 2 * Interface.totalIncreases run.operations +
    (2 * n + 1) * params.valueBound at values
  nlinarith

/-- The unconditional interface theorem now applies to the very same run.
Its two constants are uniform in the tree size and the gap value bound. -/
theorem activity_bound :
    ∃ insertConstant valueChangeConstant : ℕ, 0 < insertConstant ∧ 0 < valueChangeConstant ∧
      Interface.totalActivity run.operations ≤
        insertConstant * params.valueBound * (2 * n + 1 + comparison.rotationCount + 2 * run.boundaryCount) +
        valueChangeConstant * Nat.clog 2 params.valueBound *
          (9 * params.valueBound * (2 * n + 1) + 32 * params.valueBound * run.boundaryCount +
            12 * params.valueBound * comparison.rotationCount) := by
  obtain ⟨insertConstant, valueChangeConstant, insertPositive, changePositive, bound⟩ := Interface.activityBound params.toShape
  refine ⟨insertConstant, valueChangeConstant, insertPositive, changePositive,
    (bound params rfl run.initialState run.trace.toInterface).trans ?_⟩
  exact Nat.add_le_add (Nat.mul_le_mul_left _ run.inserts) (Nat.mul_le_mul_left _ run.valueChanges)

/-- Actual initialization and all local geometry are constructed from the
structurally normal comparison trace and one sufficient numeric gap cap. -/
theorem exists_of_normal (normal : IsStructurallyNormal bounds comparison)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound : ∀ time, Analysis.contractedGap (2 * (Snapshot.ofTree (comparison.state time)).maxRank + 1) ≤ params.valueBound) :
    Nonempty (ArticleInitializedExecution params bounds comparison tree) := by
  have initialBound : Analysis.contractedGap (Snapshot.ofTree comparison.initialTree).withTruePriority.maxRank ≤ params.valueBound :=
    (Analysis.contractedGap_mono (Nat.le_add_right _ 1)).trans (valueBound 0)
  obtain ⟨groups, finalTree, schedule, requests, _, _, _⟩ := comparison.exists_normalFormSchedule tree
  obtain ⟨execution⟩ := ArticleChronologicalExecution.exists_schedule normal valueBound schedule
    (canonicalState_represents _ tree params growingLimit initialBound)
  refine ⟨⟨growingLimit, initialBound, finalTree, ?_⟩⟩
  simpa only [ComparisonTrace.initialTree, ComparisonTrace.Schedule.servedRequests, requests, Fin.val_zero, Nat.sub_zero] using execution

end ArticleInitializedExecution
end Splay.Accounting
