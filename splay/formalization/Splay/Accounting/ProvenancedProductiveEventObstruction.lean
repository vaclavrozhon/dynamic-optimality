import Splay.Accounting.ProductiveEventEnvelopeBridge

namespace Splay.Accounting

namespace ProductiveEventClassification

/--
Putting every productive operation in the paid class makes the strong local
activity charge automatic: the unimportant list is empty.

Thus, on a cost-sensitive realized schedule, the productive-event residue can
be reduced to one schedule-specific upper bound on the total number of
productive operations.
-/
def semanticAllPaidOfProductiveBound
    {constants : TranslationConstants}
    {n : ℕ} {operations : List (Interface.Operation n)}
    {nearCost height : ℕ}
    (productive_le :
      productiveEvents operations ≤
        constants.semantic.paid * (n + nearCost) * gapLog height) :
    SemanticProductiveEventCharge constants operations nearCost height where
  classification := allPaid operations
  paid_le_unimportant := by
    simpa using productive_le
  local_charge := by
    simp

end ProductiveEventClassification

namespace ProvenancedInitializedRealizedNormalFormSchedule

/--
Schedule-specific integration of the all-paid classification.

The strong `local_charge` field is discharged without a premise.  The only
remaining input is a cost-sensitive bound on the productive operations of
the exact provenanced execution.
-/
def semanticProductiveChargeOfProductiveBound
    {constants : TranslationConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : Assumptions.NormalForm.ComparisonTrace n accesses}
    (provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison)
    (nearCost height : ℕ)
    (productive_le :
      productiveEvents
          (Lazy.eraseOperations
            provenanced.realized.execution.events) ≤
        constants.semantic.paid * (n + nearCost) * gapLog height) :
    provenanced.SemanticProductiveCharge constants nearCost height :=
  ProductiveEventClassification.semanticAllPaidOfProductiveBound
    productive_le

/--
The corresponding exact witnessed-potential endpoint.  This removes
`local_charge` entirely from the caller-facing residue.
-/
def witnessedEnvelopePotentialResidueOfProductiveBound
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
    (productive_le :
      productiveEvents
          (Lazy.eraseOperations
            provenanced.realized.execution.events) ≤
        constants.semantic.paid * (n + nearCost) * gapLog height) :
    WitnessedEnvelopePotentialResidue constants params
      (Lazy.eraseOperations
        provenanced.realized.execution.events)
      nearCost height :=
  provenanced.witnessedEnvelopePotentialResidueOfSemanticCharge
    nearCost height valueBound_le
    (provenanced.semanticProductiveChargeOfProductiveBound
      nearCost height productive_le)

end ProvenancedInitializedRealizedNormalFormSchedule

end Splay.Accounting

namespace Splay.Lazy

/--
One productive zero-activity rich loop: increase one value and immediately
decrease it back.
-/
def productiveValueCycles {n : ℕ}
    (element : Element n) : ℕ → List (Event n)
  | 0 => []
  | cycles + 1 =>
      .operation (.valueChange element .increase) ::
        .operation (.valueChange element .decrease) ::
          productiveValueCycles element cycles

namespace State

/-- Increasing and then decreasing the same rich value restores the state. -/
@[simp]
theorem decreaseValue_increaseValue
    {n : ℕ} (state : State n) (element : Element n) :
    (state.increaseValue element).decreaseValue element = state := by
  cases state with
  | mk view blocks value =>
      simp only [increaseValue, decreaseValue]
      congr
      funext queried
      by_cases equal : queried = element
      · subst queried
        simp
      · simp [equal]

/--
Arbitrarily many productive value loops are legal whenever the selected
initial value has one unit of slack.
-/
theorem productiveValueCycles_trace
    {n : ℕ} {params : Interface.Parameters}
    (state : State n) (element : Element n)
    (valid : state.Valid params)
    (slack : state.value element < params.valueBound)
    (cycles : ℕ) :
    Trace params state (productiveValueCycles element cycles) state := by
  induction cycles with
  | zero =>
      exact Trace.nil valid
  | succ cycles ih =>
      have increaseStep :
          Step params state
            (.operation (.valueChange element .increase))
            (state.increaseValue element) :=
        state.increaseValue_step element valid slack
      have increasedValid :
          (state.increaseValue element).Valid params :=
        increaseStep.after_valid
      have canDecrease :
          1 < (state.increaseValue element).value element := by
        have positive := (valid.toInterface.2.1 element).1
        change 1 ≤ state.value element at positive
        simp only [increaseValue, Function.update_self]
        omega
      have decreaseStep :
          Step params (state.increaseValue element)
            (.operation (.valueChange element .decrease))
            ((state.increaseValue element).decreaseValue element) :=
        (state.increaseValue element).decreaseValue_step
          element increasedValid canDecrease
      have tailTrace :
          Trace params
            ((state.increaseValue element).decreaseValue element)
            (productiveValueCycles element cycles) state := by
        simpa using ih
      simpa [productiveValueCycles] using
        Trace.cons increaseStep
          (Trace.cons decreaseStep tailTrace)

end State

@[simp]
theorem totalActivity_productiveValueCycles
    {n : ℕ} (element : Element n) (cycles : ℕ) :
    Interface.totalActivity
        (eraseOperations (productiveValueCycles element cycles)) = 0 := by
  induction cycles with
  | zero =>
      rfl
  | succ cycles ih =>
      rw [productiveValueCycles]
      change
        (List.map Interface.Operation.activity
          (eraseOperations
            (productiveValueCycles element cycles))).sum = 0 at ih
      change
        Interface.totalActivity
          ([.valueChange element .increase,
            .valueChange element .decrease] ++
            eraseOperations (productiveValueCycles element cycles)) = 0
      calc
        Interface.totalActivity
            ([.valueChange element .increase,
              .valueChange element .decrease] ++
              eraseOperations (productiveValueCycles element cycles)) =
            Interface.totalActivity
                ([.valueChange element .increase,
                  .valueChange element .decrease] :
                  List (Interface.Operation n)) +
              Interface.totalActivity
                (eraseOperations
                  (productiveValueCycles element cycles)) := by
            simp [Interface.totalActivity]
            omega
        _ = 0 := by
          simp [Interface.totalActivity,
            Interface.Operation.activity, ih]

@[simp]
theorem productiveEvents_productiveValueCycles
    {n : ℕ} (element : Element n) (cycles : ℕ) :
    Splay.Accounting.productiveEvents
        (eraseOperations (productiveValueCycles element cycles)) =
      cycles := by
  induction cycles with
  | zero =>
      rfl
  | succ cycles ih =>
      rw [productiveValueCycles]
      change
        Splay.Accounting.productiveEvents
          ([.valueChange element .increase,
            .valueChange element .decrease] ++
            eraseOperations (productiveValueCycles element cycles)) =
          cycles + 1
      calc
        Splay.Accounting.productiveEvents
            ([.valueChange element .increase,
              .valueChange element .decrease] ++
              eraseOperations (productiveValueCycles element cycles)) =
            Splay.Accounting.productiveEvents
                ([.valueChange element .increase,
                  .valueChange element .decrease] :
                  List (Interface.Operation n)) +
              Splay.Accounting.productiveEvents
                (eraseOperations
                  (productiveValueCycles element cycles)) := by
            simp [Splay.Accounting.productiveEvents,
              Interface.totalInserts, Interface.totalIncreases]
            omega
        _ = cycles + 1 := by
          rw [ih]
          simp [Splay.Accounting.productiveEvents,
            Interface.totalInserts, Interface.totalIncreases,
            Interface.Operation.insertCount,
            Interface.Operation.increaseCount]
          omega

namespace Initialization

/--
Prefix an initialized execution by productive value loops at its genuine
empty-block initial state.

The represented endpoint is unchanged.  This construction is the precise
reason that the current `Initialization` record is not yet cost-sensitive:
its trace is checked, but its event list is not authenticated as the
canonical initializer's event list.
-/
def prependProductiveValueCycles
    {n : ℕ} {params : Interface.Parameters}
    {snapshot : Rank.Snapshot n} {tree : Tree.BST 0 n}
    (initialization : Initialization params snapshot tree)
    (element : Element n) (cycles : ℕ)
    (slack :
      (Canonical.emptyCanonicalState snapshot tree).value element <
        params.valueBound) :
    Initialization params snapshot tree where
  valueBound := initialization.valueBound
  final := initialization.final
  events :=
    productiveValueCycles element cycles ++ initialization.events
  trace :=
    (Canonical.emptyCanonicalState snapshot tree).productiveValueCycles_trace
      element
      (Canonical.emptyCanonicalState_valid snapshot tree params
        initialization.valueBound)
      slack cycles
      |>.append initialization.trace
  final_represents := initialization.final_represents

end Initialization

namespace InitializedTransition

/-- Lift productive initialization padding to a complete initialized run. -/
def prependProductiveValueCycles
    {n : ℕ} {params : Interface.Parameters}
    {beforeSnapshot afterSnapshot : Rank.Snapshot n}
    {beforeTree afterTree : Tree.BST 0 n}
    (execution :
      InitializedTransition params
        beforeSnapshot beforeTree afterSnapshot afterTree)
    (element : Element n) (cycles : ℕ)
    (slack :
      (Canonical.emptyCanonicalState
        beforeSnapshot beforeTree).value element <
          params.valueBound) :
    InitializedTransition params
      beforeSnapshot beforeTree afterSnapshot afterTree where
  initialization :=
    execution.initialization.prependProductiveValueCycles
      element cycles slack
  transition := execution.transition

@[simp]
theorem prependProductiveValueCycles_events
    {n : ℕ} {params : Interface.Parameters}
    {beforeSnapshot afterSnapshot : Rank.Snapshot n}
    {beforeTree afterTree : Tree.BST 0 n}
    (execution :
      InitializedTransition params
        beforeSnapshot beforeTree afterSnapshot afterTree)
    (element : Element n) (cycles : ℕ)
    (slack :
      (Canonical.emptyCanonicalState
        beforeSnapshot beforeTree).value element <
          params.valueBound) :
    (execution.prependProductiveValueCycles
        element cycles slack).events =
      productiveValueCycles element cycles ++ execution.events := by
  change
    (productiveValueCycles element cycles ++
        execution.initialization.events) ++
      execution.transition.events =
    productiveValueCycles element cycles ++
      (execution.initialization.events ++ execution.transition.events)
  exact List.append_assoc _ _ _

end InitializedTransition

end Splay.Lazy

namespace Splay.Accounting

namespace ProvenancedInitializedRealizedNormalFormSchedule

/--
The current schedule-provenance type is closed under arbitrary productive
padding of the initialization trace.

In particular, recursive comparison/splay provenance does not prevent this
padding: it authenticates only the represented transition suffix, while the
`Initialization` event list remains unconstrained beyond trace validity.
-/
def prependProductiveValueCycles
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : Assumptions.NormalForm.ComparisonTrace n accesses}
    (provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison)
    (element : Lazy.Element n) (cycles : ℕ)
    (slack :
      (Lazy.Canonical.emptyCanonicalState
          (Rank.Snapshot.ofTree comparison.initialTree)
          initialTree).value element <
        params.valueBound) :
    ProvenancedInitializedRealizedNormalFormSchedule
      params initialTree comparison where
  realized :=
    { groups := provenanced.realized.groups
      finalSplayTree := provenanced.realized.finalSplayTree
      schedule := provenanced.realized.schedule
      execution :=
        provenanced.realized.execution.prependProductiveValueCycles
          element cycles slack
      requests_eq := provenanced.realized.requests_eq
      groups_ordered := provenanced.realized.groups_ordered
      comparison_serves := provenanced.realized.comparison_serves
      comparisonRotationCount_eq :=
        provenanced.realized.comparisonRotationCount_eq }
  provenance :=
    { transitionProvenance :=
        provenanced.provenance.transitionProvenance }

@[simp]
theorem prependProductiveValueCycles_events
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : Assumptions.NormalForm.ComparisonTrace n accesses}
    (provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison)
    (element : Lazy.Element n) (cycles : ℕ)
    (slack :
      (Lazy.Canonical.emptyCanonicalState
          (Rank.Snapshot.ofTree comparison.initialTree)
          initialTree).value element <
        params.valueBound) :
    (provenanced.prependProductiveValueCycles
        element cycles slack).realized.execution.events =
      Lazy.productiveValueCycles element cycles ++
        provenanced.realized.execution.events := by
  exact
    Lazy.InitializedTransition.prependProductiveValueCycles_events
      provenanced.realized.execution element cycles slack

@[simp]
theorem prependProductiveValueCycles_totalActivity
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : Assumptions.NormalForm.ComparisonTrace n accesses}
    (provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison)
    (element : Lazy.Element n) (cycles : ℕ)
    (slack :
      (Lazy.Canonical.emptyCanonicalState
          (Rank.Snapshot.ofTree comparison.initialTree)
          initialTree).value element <
        params.valueBound) :
    Interface.totalActivity
        (Lazy.eraseOperations
          ((provenanced.prependProductiveValueCycles
            element cycles slack).realized.execution.events)) =
      Interface.totalActivity
        (Lazy.eraseOperations
          provenanced.realized.execution.events) := by
  rw [prependProductiveValueCycles_events]
  rw [Lazy.eraseOperations_append]
  rw [show
    Interface.totalActivity
        (Lazy.eraseOperations (Lazy.productiveValueCycles element cycles) ++
          Lazy.eraseOperations provenanced.realized.execution.events) =
      Interface.totalActivity
          (Lazy.eraseOperations
            (Lazy.productiveValueCycles element cycles)) +
        Interface.totalActivity
          (Lazy.eraseOperations
            provenanced.realized.execution.events) by
      simp [Interface.totalActivity]]
  rw [Lazy.totalActivity_productiveValueCycles]
  simp

@[simp]
theorem prependProductiveValueCycles_productiveEvents
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : Assumptions.NormalForm.ComparisonTrace n accesses}
    (provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison)
    (element : Lazy.Element n) (cycles : ℕ)
    (slack :
      (Lazy.Canonical.emptyCanonicalState
          (Rank.Snapshot.ofTree comparison.initialTree)
          initialTree).value element <
        params.valueBound) :
    productiveEvents
        (Lazy.eraseOperations
          ((provenanced.prependProductiveValueCycles
            element cycles slack).realized.execution.events)) =
      cycles +
        productiveEvents
          (Lazy.eraseOperations
            provenanced.realized.execution.events) := by
  rw [prependProductiveValueCycles_events]
  rw [Lazy.eraseOperations_append]
  have appendEq :
      productiveEvents
          (Lazy.eraseOperations (Lazy.productiveValueCycles element cycles) ++
            Lazy.eraseOperations provenanced.realized.execution.events) =
        productiveEvents
            (Lazy.eraseOperations
              (Lazy.productiveValueCycles element cycles)) +
          productiveEvents
            (Lazy.eraseOperations
              provenanced.realized.execution.events) := by
    simp [productiveEvents, Interface.totalInserts,
      Interface.totalIncreases]
    omega
  rw [appendEq, Lazy.productiveEvents_productiveValueCycles]

/--
Schedule-specific obstruction.

For every current provenanced initialized schedule with one unit of slack,
and for every fixed advertised envelope, another value of the *same exact
schedule-provenance type* has the same structural schedule, endpoints, and
activity but admits no envelope-bounded productive classification.

Therefore `paid_le_unimportant` cannot be proved from the current
`ProvenancedInitializedRealizedNormalFormSchedule` record.  At minimum the
initialization must be authenticated as the canonical initializer (and the
same issue must be excluded at each local transition segment).
-/
theorem exists_sameSchedule_without_envelopeClassification
    (constants : TranslationConstants)
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : Assumptions.NormalForm.ComparisonTrace n accesses}
    (provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison)
    (element : Lazy.Element n)
    (slack :
      (Lazy.Canonical.emptyCanonicalState
          (Rank.Snapshot.ofTree comparison.initialTree)
          initialTree).value element <
        params.valueBound)
    (nearCost height : ℕ) :
    ∃ padded :
        ProvenancedInitializedRealizedNormalFormSchedule
          params initialTree comparison,
      padded.realized.groups = provenanced.realized.groups ∧
        padded.realized.finalSplayTree =
          provenanced.realized.finalSplayTree ∧
        padded.realized.schedule.comparisonRotationCount =
          provenanced.realized.schedule.comparisonRotationCount ∧
        Interface.totalActivity
            (Lazy.eraseOperations
              padded.realized.execution.events) =
          Interface.totalActivity
            (Lazy.eraseOperations
              provenanced.realized.execution.events) ∧
        ¬ Nonempty
          (EnvelopeProductiveEventClassification constants
            (Lazy.eraseOperations
              padded.realized.execution.events)
            nearCost height) := by
  let activity :=
    Interface.totalActivity
      (Lazy.eraseOperations
        provenanced.realized.execution.events)
  let unimportant :=
    unimportantEnvelope constants height activity
  let bound :=
    paidEnvelope constants n nearCost height unimportant +
      unimportant
  let cycles := bound + 1
  let padded :=
    provenanced.prependProductiveValueCycles
      element cycles slack
  refine ⟨padded, rfl, rfl, rfl, ?_, ?_⟩
  · exact
      prependProductiveValueCycles_totalActivity
        provenanced element cycles slack
  · rintro ⟨classification⟩
    have counts := classification.classification.counts_eq
    have paidBound := classification.paid_le
    have unimportantBound := classification.unimportant_le
    have activityEq :
        Interface.totalActivity
            (Lazy.eraseOperations
              padded.realized.execution.events) =
          activity := by
      exact
        prependProductiveValueCycles_totalActivity
          provenanced element cycles slack
    have productiveEq :
        productiveEvents
            (Lazy.eraseOperations
              padded.realized.execution.events) =
          cycles +
            productiveEvents
              (Lazy.eraseOperations
                provenanced.realized.execution.events) := by
      exact
        prependProductiveValueCycles_productiveEvents
          provenanced element cycles slack
    rw [activityEq] at paidBound unimportantBound
    change
      classification.classification.paidSlots.length ≤
        paidEnvelope constants n nearCost height unimportant
      at paidBound
    change
      classification.classification.unimportantSlots.length ≤
        unimportant
      at unimportantBound
    rw [productiveEq] at counts
    dsimp only [cycles, bound] at counts
    omega

end ProvenancedInitializedRealizedNormalFormSchedule

end Splay.Accounting
