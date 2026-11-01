import Splay.Accounting.ProvenancedProductiveEventCharge
import Splay.Interface.InitialColumnIncidenceAssembly
import Splay.Interface.WShiftTrace

namespace Splay.Accounting

/--
The exact semantic residue behind the two quotient-envelope inequalities.

The productive-operation partition itself is already automatic.  The two
fields below are the remaining manuscript-specific facts:

* paid slots are bounded by the unimportant slots plus the base paid charge;
* unimportant slots satisfy the strong local activity charge.

No trace-validity, join-history, activity-history, or shift-incidence field is
repeated here: all of those are automatic for an initialized interface trace.
-/
structure SemanticProductiveEventCharge
    (constants : TranslationConstants)
    {n : ℕ} (operations : List (Interface.Operation n))
    (nearCost height : ℕ) where
  classification : ProductiveEventClassification operations
  paid_le_unimportant :
    classification.paidSlots.length ≤
      classification.unimportantSlots.length +
        constants.semantic.paid * (n + nearCost) * gapLog height
  local_charge :
    unimportantChargeCoefficient constants height *
        classification.unimportantSlots.length ≤
      16 * Interface.totalActivity operations

namespace SemanticProductiveEventCharge

/--
The semantic paid and local-charge laws imply exactly the two quotient
envelope inequalities consumed by the potential reduction.
-/
def toEnvelopeClassification
    {constants : TranslationConstants}
    {n : ℕ} {operations : List (Interface.Operation n)}
    {nearCost height : ℕ}
    (charge :
      SemanticProductiveEventCharge constants operations nearCost height) :
    EnvelopeProductiveEventClassification
      constants operations nearCost height where
  classification := charge.classification
  unimportant_le :=
    le_unimportantEnvelope_of_local_charge charge.local_charge
  paid_le := by
    apply charge.paid_le_unimportant.trans
    unfold paidEnvelope
    exact
      Nat.add_le_add_right
        (le_unimportantEnvelope_of_local_charge charge.local_charge) _

/-- The semantic residue therefore proves the count-only envelope budget. -/
theorem toBudget
    {constants : TranslationConstants}
    {n : ℕ} {operations : List (Interface.Operation n)}
    {nearCost height : ℕ}
    (charge :
      SemanticProductiveEventCharge constants operations nearCost height) :
    EnvelopeProductiveEventBudget constants operations nearCost height :=
  charge.toEnvelopeClassification.toBudget

end SemanticProductiveEventCharge

/--
All Join/Activity/Shift infrastructure that is already forced by an
initialized legal interface trace.

This record is used below to state the specification boundary precisely:
even this complete automatic infrastructure does not choose or bound the
semantic paid/unimportant productive-event classes.
-/
structure AutomaticJoinActivityShiftFacts
    {n : ℕ} {params : Interface.Parameters}
    {initial final : Interface.State n}
    {operations : List (Interface.Operation n)}
    (initialState : initial.Initial params)
    (trace : Interface.Trace params initial operations final) : Prop where
  joinHistory :
    ∃ finalLabels occurrences,
      Interface.JoinHistory params initial [] operations occurrences
          final finalLabels ∧
        finalLabels.length = final.blocks.length ∧
        occurrences.length =
          Interface.totalInserts operations +
            Interface.totalActivity operations
  activityHistory :
    ∃ finalLabels occurrences,
      Interface.ActivityHistory params initial [] operations occurrences
          final finalLabels ∧
        finalLabels.length = final.blocks.length ∧
        (∀ occurrence ∈ occurrences,
          occurrence.root ∈ finalLabels) ∧
        Interface.totalActivity operations =
          ∑ key ∈ Interface.lineageRunKeys occurrences,
            Interface.lineageRunActivity occurrences key
  shiftHistory :
    ∃ snapshots : List Interface.PairShiftSnapshot,
      snapshots.length = Interface.totalActivity operations ∧
        Nonempty
          (Interface.SnapshotChainPartition params operations snapshots) ∧
        Interface.totalWShift snapshots ≤
          ((params.valueBound *
            Interface.totalInserts operations : ℕ) : ℤ)
  incidenceActivity :
    ∃ insertConstant valueChangeConstant : ℕ,
      0 < insertConstant ∧
        0 < valueChangeConstant ∧
        Interface.totalActivity operations ≤
          insertConstant * params.valueBound *
              Interface.totalInserts operations +
            valueChangeConstant * Nat.clog 2 params.valueBound *
              (2 * Interface.totalIncreases operations +
                (2 * n + 1) * params.valueBound)

namespace AutomaticJoinActivityShiftFacts

/-- The complete automatic infrastructure is constructible from every trace. -/
theorem ofTrace
    {n : ℕ} {params : Interface.Parameters}
    {initial final : Interface.State n}
    {operations : List (Interface.Operation n)}
    (initialState : initial.Initial params)
    (trace : Interface.Trace params initial operations final) :
    AutomaticJoinActivityShiftFacts initialState trace where
  joinHistory :=
    Interface.JoinHistory.lift_initial initialState trace
  activityHistory :=
    trace.existsActivityGrouping initialState
  shiftHistory :=
    Interface.LifetimeHistory.exists_pairShiftSnapshots_partition_of_trace
      initialState trace
  incidenceActivity :=
    Interface.activity_le_inserts_and_increases
      (Interface.activityBound params.toShape) initialState trace

end AutomaticJoinActivityShiftFacts

namespace ProductiveEnvelopeInfrastructureCounterexample

open PotentialBudgetCounterexample

/-- One increase followed by one decrease, repeated a chosen number of times. -/
def cycleOperations : ℕ → List (Interface.Operation 1)
  | 0 => []
  | cycles + 1 =>
      .valueChange element .increase ::
        .valueChange element .decrease ::
          cycleOperations cycles

/-- The decrease returns the one-step counterexample state to its initial state. -/
theorem decrease_step :
    Interface.Step (minimalParameters shape)
      increasedState
      (.valueChange element .decrease)
      (emptyPotentialState 1) := by
  refine
    ⟨increasedState_valid,
      Interface.Effect.decrease ?_ rfl ?_,
      (emptyPotentialState_initial shape 1).1⟩
  · simp [increasedState, emptyPotentialState]
  · funext candidate
    by_cases same : candidate = element
    · subst candidate
      simp [increasedState, emptyPotentialState]
    · simp [increasedState, emptyPotentialState, same]

/-- Arbitrarily many zero-activity increase/decrease cycles are legal. -/
theorem cycle_trace (cycles : ℕ) :
    Interface.Trace (minimalParameters shape)
      (emptyPotentialState 1)
      (cycleOperations cycles)
      (emptyPotentialState 1) := by
  induction cycles with
  | zero =>
      exact .nil (emptyPotentialState_initial shape 1).1
  | succ cycles ih =>
      exact
        .cons increase_step
          (.cons decrease_step ih)

@[simp]
theorem totalActivity_cycleOperations (cycles : ℕ) :
    Interface.totalActivity (cycleOperations cycles) = 0 := by
  induction cycles with
  | zero =>
      rfl
  | succ cycles ih =>
      rw [cycleOperations]
      simp only [Interface.totalActivity, List.map_cons, List.sum_cons,
        Interface.Operation.activity, zero_add]
      change Interface.totalActivity (cycleOperations cycles) = 0
      exact ih

@[simp]
theorem totalInserts_cycleOperations (cycles : ℕ) :
    Interface.totalInserts (cycleOperations cycles) = 0 := by
  induction cycles with
  | zero =>
      rfl
  | succ cycles ih =>
      rw [cycleOperations]
      simp only [Interface.totalInserts, List.map_cons, List.sum_cons,
        Interface.Operation.insertCount, zero_add]
      change Interface.totalInserts (cycleOperations cycles) = 0
      exact ih

@[simp]
theorem totalIncreases_cycleOperations (cycles : ℕ) :
    Interface.totalIncreases (cycleOperations cycles) = cycles := by
  induction cycles with
  | zero =>
      rfl
  | succ cycles ih =>
      rw [cycleOperations]
      simp only [Interface.totalIncreases, List.map_cons, List.sum_cons,
        Interface.Operation.increaseCount, zero_add]
      change
        1 + Interface.totalIncreases (cycleOperations cycles) =
          cycles + 1
      omega

@[simp]
theorem productiveEvents_cycleOperations (cycles : ℕ) :
    productiveEvents (cycleOperations cycles) = cycles := by
  simp [productiveEvents]

/--
For every fixed translation constant and advertised cost/height, a sufficiently
long initialized legal cycle trace carries all automatic Join/Activity/Shift
facts but has no envelope-bounded productive classification.

Consequently those automatic certificates cannot prove the two semantic
productive-event envelope laws together without a genuinely new charging
premise.
-/
theorem automaticFacts_do_not_force_envelopeClassification
    (constants : TranslationConstants) (nearCost height : ℕ) :
    let cycles :=
      paidEnvelope constants 1 nearCost height 0 + 1
    ∃ (initial final : Interface.State 1)
        (operations : List (Interface.Operation 1)),
      initial.Initial (minimalParameters shape) ∧
        Interface.Trace (minimalParameters shape)
          initial operations final ∧
        (minimalParameters shape).valueBound ≤ gapBound height ∧
        Nonempty
          (AutomaticJoinActivityShiftFacts
            (initialState :=
              (emptyPotentialState_initial shape 1))
            (cycle_trace cycles)) ∧
        ¬ Nonempty
          (EnvelopeProductiveEventClassification
            constants operations nearCost height) := by
  dsimp only
  let cycles :=
    paidEnvelope constants 1 nearCost height 0 + 1
  refine
    ⟨emptyPotentialState 1, emptyPotentialState 1,
      cycleOperations cycles,
      emptyPotentialState_initial shape 1,
      cycle_trace cycles,
      ?_,
      ⟨AutomaticJoinActivityShiftFacts.ofTrace
        (emptyPotentialState_initial shape 1)
        (cycle_trace cycles)⟩,
      ?_⟩
  · simpa [minimalParameters] using two_le_gapBound height
  · rintro ⟨classification⟩
    have budget := classification.toBudget
    unfold EnvelopeProductiveEventBudget ProductiveEventBudget at budget
    simp only
      [totalActivity_cycleOperations,
        unimportantEnvelope, Nat.mul_zero, Nat.zero_div,
        productiveEvents_cycleOperations] at budget
    dsimp only [cycles] at budget
    omega

end ProductiveEnvelopeInfrastructureCounterexample

namespace InitializedRealizedNormalFormSchedule

/--
The exact realized operation list already carries all automatic
Join/Activity/Shift facts; these do not need to be included in the semantic
productive charge premise below.
-/
theorem automaticJoinActivityShiftFacts
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : Assumptions.NormalForm.ComparisonTrace n accesses}
    (realized :
      InitializedRealizedNormalFormSchedule
        params initialTree comparison) :
    AutomaticJoinActivityShiftFacts
      realized.execution.initial_toInterface_initial
      realized.execution.toInterface :=
  AutomaticJoinActivityShiftFacts.ofTrace
    realized.execution.initial_toInterface_initial
    realized.execution.toInterface

/-- Minimal productive-event premise on the exact realized operation list. -/
abbrev SemanticProductiveCharge
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : Assumptions.NormalForm.ComparisonTrace n accesses}
    (realized :
      InitializedRealizedNormalFormSchedule
        params initialTree comparison)
    (constants : TranslationConstants)
    (nearCost height : ℕ) :=
  SemanticProductiveEventCharge constants
    (Lazy.eraseOperations realized.execution.events)
    nearCost height

/--
Once the two exact semantic charge laws are supplied, all quotient-envelope,
trace-identity, and realized-schedule plumbing is automatic.
-/
def witnessedEnvelopePotentialResidueOfSemanticCharge
    {constants : TranslationConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : Assumptions.NormalForm.ComparisonTrace n accesses}
    (realized :
      InitializedRealizedNormalFormSchedule
        params initialTree comparison)
    (nearCost height : ℕ)
    (valueBound_le : params.valueBound ≤ gapBound height)
    (charge :
      realized.SemanticProductiveCharge constants nearCost height) :
    WitnessedEnvelopePotentialResidue constants params
      (Lazy.eraseOperations realized.execution.events)
      nearCost height where
  valueBound_le := valueBound_le
  productiveClassification := charge.toEnvelopeClassification

end InitializedRealizedNormalFormSchedule

namespace ProvenancedInitializedRealizedNormalFormSchedule

/--
The recursively provenanced execution inherits the same automatic
Join/Activity/Shift package.
-/
theorem automaticJoinActivityShiftFacts
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : Assumptions.NormalForm.ComparisonTrace n accesses}
    (provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison) :
    AutomaticJoinActivityShiftFacts
      provenanced.realized.execution.initial_toInterface_initial
      provenanced.realized.execution.toInterface :=
  provenanced.realized.automaticJoinActivityShiftFacts

/-- The same minimal premise on the exact recursively provenanced execution. -/
abbrev SemanticProductiveCharge
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : Assumptions.NormalForm.ComparisonTrace n accesses}
    (provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison)
    (constants : TranslationConstants)
    (nearCost height : ℕ) :=
  SemanticProductiveEventCharge constants
    (Lazy.eraseOperations provenanced.realized.execution.events)
    nearCost height

/--
Schedule-provenanced endpoint whose only productive-event input is the two
field semantic charge record above.
-/
def witnessedEnvelopePotentialResidueOfSemanticCharge
    {constants : TranslationConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : Assumptions.NormalForm.ComparisonTrace n accesses}
    (provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison)
    (nearCost height : ℕ)
    (valueBound_le : params.valueBound ≤ gapBound height)
    (charge :
      provenanced.SemanticProductiveCharge constants nearCost height) :
    WitnessedEnvelopePotentialResidue constants params
      (Lazy.eraseOperations provenanced.realized.execution.events)
      nearCost height :=
  provenanced.realized.witnessedEnvelopePotentialResidueOfSemanticCharge
    nearCost height valueBound_le charge

end ProvenancedInitializedRealizedNormalFormSchedule

end Splay.Accounting
