import Splay.Accounting.EnvelopeReduction
import Splay.Lazy.CanonicalTrace

namespace Splay.Accounting

/--
The exact productive-event count left after the verified value potential has
already absorbed all decreases.

Only inserts and increases occur in `PotentialBudget`; conversions, creates,
deletes, passes, splits, and decreases need no additional count here.
-/
def productiveEvents {n : ℕ}
    (operations : List (Interface.Operation n)) : ℕ :=
  Interface.totalInserts operations +
    Interface.totalIncreases operations

/--
Every abstract operation contributes to at most one productive category.
-/
theorem operation_productiveCount_le_one {n : ℕ}
    (operation : Interface.Operation n) :
    operation.insertCount + operation.increaseCount ≤ 1 := by
  cases operation with
  | valueChange element delta =>
      cases delta <;>
        simp [Interface.Operation.insertCount,
          Interface.Operation.increaseCount]
  | _ =>
      simp [Interface.Operation.insertCount,
        Interface.Operation.increaseCount]

theorem productiveEvents_le_length {n : ℕ}
    (operations : List (Interface.Operation n)) :
    productiveEvents operations ≤ operations.length := by
  induction operations with
  | nil =>
      simp [productiveEvents, Interface.totalInserts,
        Interface.totalIncreases]
  | cons operation operations ih =>
      have headBound :=
        operation_productiveCount_le_one operation
      unfold productiveEvents at ih ⊢
      simp only [Interface.totalInserts,
        Interface.totalIncreases, List.map_cons, List.sum_cons,
        List.length_cons] at ih ⊢
      omega

/-- Erasing rich silent events cannot increase event-list length. -/
theorem eraseOperations_length_le {n : ℕ}
    (events : List (Lazy.Event n)) :
    (Lazy.eraseOperations events).length ≤ events.length := by
  induction events with
  | nil =>
      rfl
  | cons event events ih =>
      cases event with
      | operation operation =>
          change
            (operation :: Lazy.eraseOperations events).length ≤
              (Lazy.Event.operation operation :: events).length
          exact Nat.succ_le_succ ih
      | silent =>
          change
            (Lazy.eraseOperations events).length ≤
              (Lazy.Event.silent :: events).length
          simpa only [List.length_cons] using
            ih.trans (Nat.le_succ events.length)

/--
A coarse bridge for realized lazy schedules: productive visible operations
are bounded by the length of their rich event list.
-/
theorem productiveEvents_eraseOperations_le {n : ℕ}
    (events : List (Lazy.Event n)) :
    productiveEvents (Lazy.eraseOperations events) ≤ events.length :=
  (productiveEvents_le_length _).trans
    (eraseOperations_length_le events)

/--
The minimal unweighted event-count residue suggested by the manuscript:
every productive event is charged either to a paid or an unimportant item.
-/
def ProductiveEventBudget {n : ℕ}
    (operations : List (Interface.Operation n))
    (paid unimportant : ℕ) : Prop :=
  productiveEvents operations ≤ paid + unimportant

/--
An operational weighted residue with the corrected initial value potential
removed.  The theorem below pays for that initial term automatically.
-/
def OperationalPotentialBudget
    (constants : SemanticConstants)
    (insertConstant valueChangeConstant : ℕ)
    {n : ℕ} (params : Interface.Parameters)
    (operations : List (Interface.Operation n))
    (height paid unimportant : ℕ) : Prop :=
  insertConstant * params.valueBound *
        Interface.totalInserts operations +
      valueChangeConstant * Nat.clog 2 params.valueBound *
        (2 * Interface.totalIncreases operations) ≤
    constants.interface *
      (paid * gapBound height * gapLog height +
        unimportant * gapBound height * gapLog height)

/--
The logarithmic parameter bound follows from the value-bound/gap bound.
-/
theorem clog_valueBound_le_gapLog
    {params : Interface.Parameters} {height : ℕ}
    (valueBound_le : params.valueBound ≤ gapBound height) :
    Nat.clog 2 params.valueBound ≤ gapLog height := by
  unfold gapLog Analysis.stabilizedLog
  exact
    Nat.clog_mono_right 2
      (valueBound_le.trans (Nat.le_max_right 2 (gapBound height)))

/--
The stabilized logarithmic factor is at most its square.
-/
theorem gapLog_le_sq (height : ℕ) :
    gapLog height ≤ gapLog height ^ 2 := by
  have positive := gapLog_pos height
  calc
    gapLog height = gapLog height * 1 := by simp
    _ ≤ gapLog height * gapLog height :=
      Nat.mul_le_mul_left _ positive
    _ = gapLog height ^ 2 := by ring

/--
The corrected initial `(2*n+1)` value potential is paid by the base term.

The factor three is exact for positive `n`:
`2*n+1 ≤ 3*n`.  No operation-count or classification premise is used.
-/
theorem initialPotential_le_base
    {constants : SemanticConstants}
    {valueChangeConstant n nearCost height : ℕ}
    {params : Interface.Parameters}
    (n_pos : 0 < n)
    (valueBound_le : params.valueBound ≤ gapBound height)
    (interface_dominates :
      3 * valueChangeConstant ≤ constants.interface) :
    valueChangeConstant * Nat.clog 2 params.valueBound *
        ((2 * n + 1) * params.valueBound) ≤
      constants.interface *
        ((n + nearCost) * gapBound height * gapLog height ^ 2) := by
  have elementCount_le : 2 * n + 1 ≤ 3 * n := by omega
  have mass_le :
      (2 * n + 1) * params.valueBound ≤
        (3 * n) * gapBound height :=
    Nat.mul_le_mul elementCount_le valueBound_le
  have log_le :=
    clog_valueBound_le_gapLog valueBound_le
  have weighted_le :
      valueChangeConstant * Nat.clog 2 params.valueBound *
          ((2 * n + 1) * params.valueBound) ≤
        valueChangeConstant * gapLog height *
          ((3 * n) * gapBound height) :=
    Nat.mul_le_mul
      (Nat.mul_le_mul_left valueChangeConstant log_le)
      mass_le
  have coefficient_base_le :
      (3 * valueChangeConstant) * n ≤
        constants.interface * (n + nearCost) :=
    Nat.mul_le_mul interface_dominates
      (Nat.le_add_right n nearCost)
  have scaled_le :
      (3 * valueChangeConstant) * n *
          gapBound height * gapLog height ≤
        constants.interface * (n + nearCost) *
          gapBound height * gapLog height ^ 2 :=
    Nat.mul_le_mul
      (Nat.mul_le_mul coefficient_base_le le_rfl)
      (gapLog_le_sq height)
  calc
    valueChangeConstant * Nat.clog 2 params.valueBound *
          ((2 * n + 1) * params.valueBound) ≤
        valueChangeConstant * gapLog height *
          ((3 * n) * gapBound height) :=
      weighted_le
    _ = (3 * valueChangeConstant) * n *
          gapBound height * gapLog height := by ring
    _ ≤ constants.interface * (n + nearCost) *
          gapBound height * gapLog height ^ 2 :=
      scaled_le
    _ = constants.interface *
          ((n + nearCost) * gapBound height *
            gapLog height ^ 2) := by ring

/--
Adding the automatically bounded initial potential turns the operational
residue into the original `PotentialBudget`.
-/
theorem potentialBudget_of_operational
    {constants : SemanticConstants}
    {insertConstant valueChangeConstant : ℕ}
    {n nearCost height paid unimportant : ℕ}
    {params : Interface.Parameters}
    {operations : List (Interface.Operation n)}
    (n_pos : 0 < n)
    (valueBound_le : params.valueBound ≤ gapBound height)
    (interface_dominates :
      3 * valueChangeConstant ≤ constants.interface)
    (operational :
      OperationalPotentialBudget constants
        insertConstant valueChangeConstant params operations
        height paid unimportant) :
    PotentialBudget constants insertConstant valueChangeConstant
      params operations nearCost height paid unimportant := by
  have initialBound :=
    initialPotential_le_base
      (constants := constants)
      (valueChangeConstant := valueChangeConstant)
      (n := n) (nearCost := nearCost) (height := height)
      (params := params)
      n_pos valueBound_le interface_dominates
  unfold OperationalPotentialBudget at operational
  unfold PotentialBudget
  calc
    insertConstant * params.valueBound *
          Interface.totalInserts operations +
        valueChangeConstant * Nat.clog 2 params.valueBound *
          (2 * Interface.totalIncreases operations +
            (2 * n + 1) * params.valueBound) =
      (insertConstant * params.valueBound *
          Interface.totalInserts operations +
        valueChangeConstant * Nat.clog 2 params.valueBound *
          (2 * Interface.totalIncreases operations)) +
        valueChangeConstant * Nat.clog 2 params.valueBound *
          ((2 * n + 1) * params.valueBound) := by ring
    _ ≤
      constants.interface *
          (paid * gapBound height * gapLog height +
            unimportant * gapBound height * gapLog height) +
        constants.interface *
          ((n + nearCost) * gapBound height *
            gapLog height ^ 2) :=
      Nat.add_le_add operational initialBound
    _ = constants.interface *
        (paid * gapBound height * gapLog height +
          unimportant * gapBound height * gapLog height +
          (n + nearCost) * gapBound height *
            gapLog height ^ 2) := by ring

/--
The unweighted productive-event residue implies the operational weighted
budget once the semantic interface coefficient dominates the two local
operation coefficients.
-/
theorem operationalPotentialBudget_of_productiveEvents
    {constants : SemanticConstants}
    {insertConstant valueChangeConstant : ℕ}
    {n height paid unimportant : ℕ}
    {params : Interface.Parameters}
    {operations : List (Interface.Operation n)}
    (valueBound_le : params.valueBound ≤ gapBound height)
    (insert_dominated :
      insertConstant ≤ constants.interface)
    (increase_dominated :
      2 * valueChangeConstant ≤ constants.interface)
    (events :
      ProductiveEventBudget operations paid unimportant) :
    OperationalPotentialBudget constants
      insertConstant valueChangeConstant params operations
      height paid unimportant := by
  let gap := gapBound height
  let log := gapLog height
  let inserts := Interface.totalInserts operations
  let increases := Interface.totalIncreases operations
  have gap_pos : 0 < gap := gapBound_pos height
  have log_pos : 0 < log := gapLog_pos height
  have log_le :
      Nat.clog 2 params.valueBound ≤ log :=
    clog_valueBound_le_gapLog valueBound_le
  have insertTerm :
      insertConstant * params.valueBound * inserts ≤
        constants.interface * gap * log * inserts := by
    have coefficient :
        insertConstant * params.valueBound ≤
          constants.interface * gap * log := by
      calc
        insertConstant * params.valueBound ≤
            constants.interface * gap :=
          Nat.mul_le_mul insert_dominated valueBound_le
        _ = constants.interface * gap * 1 := by simp
        _ ≤ constants.interface * gap * log :=
          Nat.mul_le_mul_left _ log_pos
    exact Nat.mul_le_mul_right inserts coefficient
  have increaseTerm :
      valueChangeConstant * Nat.clog 2 params.valueBound *
          (2 * increases) ≤
        constants.interface * gap * log * increases := by
    have coefficient :
        2 * valueChangeConstant *
            Nat.clog 2 params.valueBound ≤
          constants.interface * gap * log := by
      calc
        2 * valueChangeConstant *
              Nat.clog 2 params.valueBound ≤
            constants.interface * log :=
          Nat.mul_le_mul increase_dominated log_le
        _ = constants.interface * 1 * log := by simp
        _ ≤ constants.interface * gap * log :=
          Nat.mul_le_mul_right log
            (Nat.mul_le_mul_left _ gap_pos)
    calc
      valueChangeConstant * Nat.clog 2 params.valueBound *
            (2 * increases) =
          (2 * valueChangeConstant *
            Nat.clog 2 params.valueBound) * increases := by ring
      _ ≤ constants.interface * gap * log * increases :=
        Nat.mul_le_mul_right increases coefficient
  unfold ProductiveEventBudget productiveEvents at events
  unfold OperationalPotentialBudget
  calc
    insertConstant * params.valueBound *
          Interface.totalInserts operations +
        valueChangeConstant * Nat.clog 2 params.valueBound *
          (2 * Interface.totalIncreases operations) ≤
      constants.interface * gap * log * inserts +
        constants.interface * gap * log * increases :=
      Nat.add_le_add insertTerm increaseTerm
    _ = constants.interface * gap * log *
          (inserts + increases) := by ring
    _ ≤ constants.interface * gap * log *
          (paid + unimportant) :=
      Nat.mul_le_mul_left _ events
    _ = constants.interface *
        (paid * gapBound height * gapLog height +
          unimportant * gapBound height * gapLog height) := by
      simp only [gap, log]
      ring

/--
The complete potential budget follows from one unweighted productive-event
count, the natural parameter bound, and dominance of the activity constants.
-/
theorem potentialBudget_of_productiveEvents
    {constants : SemanticConstants}
    {insertConstant valueChangeConstant : ℕ}
    {n nearCost height paid unimportant : ℕ}
    {params : Interface.Parameters}
    {operations : List (Interface.Operation n)}
    (n_pos : 0 < n)
    (valueBound_le : params.valueBound ≤ gapBound height)
    (insert_dominated :
      insertConstant ≤ constants.interface)
    (valueChange_dominated :
      3 * valueChangeConstant ≤ constants.interface)
    (events :
      ProductiveEventBudget operations paid unimportant) :
    PotentialBudget constants insertConstant valueChangeConstant
      params operations nearCost height paid unimportant :=
  potentialBudget_of_operational n_pos valueBound_le
    valueChange_dominated
    (operationalPotentialBudget_of_productiveEvents
      valueBound_le insert_dominated
      ((by omega) : 2 * valueChangeConstant ≤ constants.interface)
      events)

/--
The productive-event residue specialized to the canonical unimportant and
paid envelopes used by `ThreeLawTranslationCertificate`.
-/
def EnvelopeProductiveEventBudget
    (constants : TranslationConstants)
    {n : ℕ} (operations : List (Interface.Operation n))
    (nearCost height : ℕ) : Prop :=
  let unimportant :=
    unimportantEnvelope constants height
      (Interface.totalActivity operations)
  ProductiveEventBudget operations
    (paidEnvelope constants n nearCost height unimportant)
    unimportant

/--
One exact count of inserts plus increases is sufficient to construct the
canonical-envelope `PotentialBudget`.
-/
theorem envelopePotentialBudget_of_productiveEvents
    {constants : TranslationConstants}
    {insertConstant valueChangeConstant : ℕ}
    {n nearCost height : ℕ}
    {params : Interface.Parameters}
    {operations : List (Interface.Operation n)}
    (n_pos : 0 < n)
    (valueBound_le : params.valueBound ≤ gapBound height)
    (insert_dominated :
      insertConstant ≤ constants.semantic.interface)
    (valueChange_dominated :
      3 * valueChangeConstant ≤ constants.semantic.interface)
    (events :
      EnvelopeProductiveEventBudget constants operations
        nearCost height) :
    PotentialBudget constants.semantic
      insertConstant valueChangeConstant params operations
      nearCost height
      (paidEnvelope constants n nearCost height
        (unimportantEnvelope constants height
          (Interface.totalActivity operations)))
      (unimportantEnvelope constants height
        (Interface.totalActivity operations)) := by
  unfold EnvelopeProductiveEventBudget at events
  exact
    potentialBudget_of_productiveEvents n_pos valueBound_le
      insert_dominated valueChange_dominated events

/--
The two uniform coefficient choices needed by the reduction.  They are
selected once, together with the translation constants, rather than proved
separately for every trace.
-/
structure PotentialCoefficientDominance
    (constants : TranslationConstants)
    (insertConstant valueChangeConstant : ℕ) : Prop where
  insert_le :
    insertConstant ≤ constants.semantic.interface
  valueChange_le :
    3 * valueChangeConstant ≤ constants.semantic.interface

/--
The exact per-instance residue after all generic potential arithmetic is
removed: choose the natural height-scaled value bound and charge the number
of inserts plus increases.
-/
structure EnvelopePotentialResidue
    (constants : TranslationConstants)
    {n : ℕ} (params : Interface.Parameters)
    (operations : List (Interface.Operation n))
    (nearCost height : ℕ) : Prop where
  valueBound_le :
    params.valueBound ≤ gapBound height
  productive_events :
    EnvelopeProductiveEventBudget constants operations nearCost height

namespace EnvelopePotentialResidue

/-- The minimal residue constructs the full canonical-envelope budget. -/
theorem toPotentialBudget
    {constants : TranslationConstants}
    {insertConstant valueChangeConstant : ℕ}
    {n nearCost height : ℕ}
    {params : Interface.Parameters}
    {operations : List (Interface.Operation n)}
    (n_pos : 0 < n)
    (dominance :
      PotentialCoefficientDominance constants
        insertConstant valueChangeConstant)
    (residue :
      EnvelopePotentialResidue constants params operations
        nearCost height) :
    PotentialBudget constants.semantic
      insertConstant valueChangeConstant params operations
      nearCost height
      (paidEnvelope constants n nearCost height
        (unimportantEnvelope constants height
          (Interface.totalActivity operations)))
      (unimportantEnvelope constants height
        (Interface.totalActivity operations)) :=
  envelopePotentialBudget_of_productiveEvents
    n_pos residue.valueBound_le dominance.insert_le
      dominance.valueChange_le residue.productive_events

end EnvelopePotentialResidue

/-- Minimal value-bound extension of a fixed structural interface shape. -/
def minimalParameters (shape : Interface.Shape) :
    Interface.Parameters where
  toShape := shape
  valueBound := 2
  valueBound_ge_two := le_rfl

/--
The parameter choice naturally used by a height-bounded realized schedule.
It simultaneously gives the initialization lower bound and the potential
reduction's upper bound by definition.
-/
def heightParameters (shape : Interface.Shape) (height : ℕ) :
    Interface.Parameters where
  toShape := shape
  valueBound := gapBound height
  valueBound_ge_two := by
    unfold gapBound Analysis.contractedGap Analysis.gapBucket
    have positive :
        0 < Nat.clog 2 (height + 1 + 1) :=
      Nat.clog_pos (by omega) (by omega)
    omega

/--
The canonical empty-block, unit-value initial state.  It is independent of
the structural shape because there are no growing blocks yet.
-/
def emptyPotentialState (n : ℕ) : Interface.State n where
  blocks := []
  value := fun _ => 1

@[simp]
theorem minimalParameters_toShape (shape : Interface.Shape) :
    (minimalParameters shape).toShape = shape :=
  rfl

@[simp]
theorem minimalParameters_valueBound (shape : Interface.Shape) :
    (minimalParameters shape).valueBound = 2 :=
  rfl

@[simp]
theorem heightParameters_toShape
    (shape : Interface.Shape) (height : ℕ) :
    (heightParameters shape height).toShape = shape :=
  rfl

@[simp]
theorem heightParameters_valueBound
    (shape : Interface.Shape) (height : ℕ) :
    (heightParameters shape height).valueBound = gapBound height :=
  rfl

/-- The contracted gap is always at least the minimal value bound two. -/
theorem two_le_gapBound (height : ℕ) :
    2 ≤ gapBound height := by
  unfold gapBound Analysis.contractedGap Analysis.gapBucket
  have positive :
      0 < Nat.clog 2 (height + 1 + 1) :=
    Nat.clog_pos (by omega) (by omega)
  omega

/--
`heightParameters` also satisfies the canonical initialization premise for
every comparison tree below the advertised height.
-/
theorem ofTree_contractedGap_le_heightParameters
    {n height : ℕ} {tree : Tree.BST 0 n}
    (height_le : tree.height ≤ height)
    (shape : Interface.Shape) :
    Analysis.contractedGap
        (Rank.Snapshot.ofTree tree).maxRank ≤
      (heightParameters shape height).valueBound := by
  change
    Analysis.contractedGap tree.height ≤
      Analysis.contractedGap (height + 1)
  exact
    Analysis.contractedGap_mono
      (height_le.trans (by omega))

/-- The empty unit-value state is a genuine abstract-interface initial state. -/
theorem emptyPotentialState_initial
    (shape : Interface.Shape) (n : ℕ) :
    (emptyPotentialState n).Initial (minimalParameters shape) := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · simp [emptyPotentialState, Interface.State.allElements]
    · intro element
      simp [emptyPotentialState, minimalParameters]
    · intro creator
      simp [emptyPotentialState, Interface.State.growingCount]
  · rfl

/-- The empty operation sequence is a valid trace from the canonical state. -/
theorem emptyPotentialState_trace
    (shape : Interface.Shape) (n : ℕ) :
    Interface.Trace (minimalParameters shape)
      (emptyPotentialState n) [] (emptyPotentialState n) :=
  .nil (emptyPotentialState_initial shape n).1

/--
For the permissive existential trace interface, `PotentialBudget` alone can
always be witnessed by the empty trace once the interface coefficient pays
the corrected initial potential.

This theorem is intentionally explicit about what it does *not* establish:
the empty trace is not asserted to realize a splay schedule or any pairing
classification.
-/
theorem emptyTrace_potentialBudget
    {constants : SemanticConstants}
    {insertConstant valueChangeConstant : ℕ}
    {n nearCost height paid unimportant : ℕ}
    (n_pos : 0 < n)
    (interface_dominates :
      3 * valueChangeConstant ≤ constants.interface)
    (shape : Interface.Shape) :
    PotentialBudget constants insertConstant valueChangeConstant
      (minimalParameters shape) ([] : List (Interface.Operation n))
      nearCost height paid unimportant := by
  apply potentialBudget_of_operational
    n_pos (two_le_gapBound height) interface_dominates
  simp [OperationalPotentialBudget, Interface.totalInserts,
    Interface.totalIncreases]

/--
Packaged existence form of the canonical empty-trace observation.
-/
theorem exists_emptyTrace_potentialBudget
    {constants : SemanticConstants}
    {insertConstant valueChangeConstant : ℕ}
    {n nearCost height paid unimportant : ℕ}
    (n_pos : 0 < n)
    (interface_dominates :
      3 * valueChangeConstant ≤ constants.interface)
    (shape : Interface.Shape) :
    ∃ (params : Interface.Parameters)
        (initial final : Interface.State n)
        (operations : List (Interface.Operation n)),
      params.toShape = shape ∧
        initial.Initial params ∧
        Interface.Trace params initial operations final ∧
        PotentialBudget constants insertConstant valueChangeConstant
          params operations nearCost height paid unimportant := by
  exact
    ⟨minimalParameters shape,
      emptyPotentialState n, emptyPotentialState n, [],
      rfl, emptyPotentialState_initial shape n,
      emptyPotentialState_trace shape n,
      emptyTrace_potentialBudget n_pos interface_dominates shape⟩

namespace PotentialBudgetCounterexample

/-- A fixed admissible shape used only for the finite obstruction below. -/
def shape : Interface.Shape where
  growingLimit := 0
  exemptPasses := 0
  matchingNumerator := 1
  matchingDenominator := 2
  matchingNumerator_pos := by omega
  matchingFraction_le_half := by omega

/--
The element whose value is increased in the one-step obstruction trace.
-/
def element : Interface.Element 1 :=
  ⟨0, by omega⟩

/-- Endpoint of one legal increase from the canonical unit-value state. -/
def increasedState : Interface.State 1 where
  blocks := []
  value :=
    Function.update (emptyPotentialState 1).value element 2

theorem increasedState_valid :
    increasedState.Valid (minimalParameters shape) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [increasedState, Interface.State.allElements]
  · intro candidate
    by_cases same : candidate = element
    · subst candidate
      simp [increasedState, emptyPotentialState,
        minimalParameters]
    · simp [increasedState, emptyPotentialState,
        minimalParameters, same]
  · intro creator
    simp [increasedState, Interface.State.growingCount]

theorem increase_step :
    Interface.Step (minimalParameters shape)
      (emptyPotentialState 1)
      (.valueChange element .increase)
      increasedState := by
  refine
    ⟨(emptyPotentialState_initial shape 1).1,
      Interface.Effect.increase ?_ ?_ ?_,
      increasedState_valid⟩
  · simp [emptyPotentialState, minimalParameters]
  · rfl
  · rfl

/-- A genuine initialized interface trace containing one productive event. -/
theorem increase_trace :
    Interface.Trace (minimalParameters shape)
      (emptyPotentialState 1)
      [.valueChange element .increase]
      increasedState :=
  Interface.Trace.cons increase_step
    (.nil increasedState_valid)

/--
Constants satisfying both coefficient-dominance conditions of the reduction.
-/
def constants : SemanticConstants where
  blocks := 0
  important := 0
  interface := 3
  paid := 0
  bends := 0

theorem insert_dominated :
    1 ≤ constants.interface := by decide

theorem valueChange_dominated :
    3 * 1 ≤ constants.interface := by decide

/-- The one productive event has no paid or unimportant charge in this test. -/
theorem productiveEventBudget_fails :
    ¬ ProductiveEventBudget
      ([.valueChange element .increase] :
        List (Interface.Operation 1))
      0 0 := by
  norm_num [ProductiveEventBudget, productiveEvents,
    Interface.totalInserts, Interface.totalIncreases,
    Interface.Operation.insertCount,
    Interface.Operation.increaseCount]

/--
Trace validity, the height/value-bound relation, and coefficient dominance do
not imply `PotentialBudget`: the remaining productive event must still be
classified and paid.  This one-step finite counterexample makes that logical
obstruction kernel-checkable.
-/
theorem potentialBudget_fails :
    ¬ PotentialBudget constants 1 1
      (minimalParameters shape)
      ([.valueChange element .increase] :
        List (Interface.Operation 1))
      0 0 0 0 := by
  norm_num [PotentialBudget, constants, minimalParameters,
    gapBound, gapLog, Analysis.stabilizedLog,
    Analysis.contractedGap, Analysis.gapBucket,
    Interface.totalInserts, Interface.totalIncreases,
    Interface.Operation.insertCount,
    Interface.Operation.increaseCount]

end PotentialBudgetCounterexample

end Splay.Accounting
