import Splay.Accounting.SplayPairingTranscript
import Splay.Interface.BlockCount
import Splay.Interface.ConversionAccounting
import Splay.Interface.Potential

namespace Splay.Accounting

/--
Semantic constants with the one positivity fact needed to recover
`unimportant_le_activity` from the stronger local-charge inequality.

The original `SemanticConstants` permits a zero interface coefficient because
positivity is irrelevant to the arithmetic certificate once both inequalities
are supplied separately.  In the concrete translation, however, the
coefficient comes from a positive activity constant, so recording positivity
lets us remove one independent event law.
-/
structure TranslationConstants where
  semantic : SemanticConstants
  interface_pos : 0 < semantic.interface

/--
The manuscript's local charge is strictly stronger than the bare statement
that every unimportant boundary pairing is charged to an internal pairing.

The factor `64`, positivity of the interface coefficient, and positivity of
`gapBound` and `gapLog` imply this without a second classification premise.
-/
theorem unimportant_le_activity_of_localCharge
    {interface height unimportant activity : ℕ}
    (interface_pos : 0 < interface)
    (localCharge :
      (64 * interface) * gapBound height * gapLog height *
          unimportant ≤
        16 * activity) :
    unimportant ≤ activity := by
  have coefficient :
      16 ≤ (64 * interface) * gapBound height * gapLog height := by
    have interface_one : 1 ≤ interface := interface_pos
    have gap_one : 1 ≤ gapBound height := gapBound_pos height
    have log_one : 1 ≤ gapLog height := gapLog_pos height
    calc
      16 ≤ 64 := by omega
      _ = 64 * 1 * 1 * 1 := by norm_num
      _ ≤ 64 * interface * gapBound height * gapLog height :=
        Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul_left 64 interface_one)
            gap_one)
          log_one
  have scaled :
      16 * unimportant ≤ 16 * activity := by
    calc
      16 * unimportant ≤
          ((64 * interface) * gapBound height * gapLog height) *
            unimportant :=
        Nat.mul_le_mul_right unimportant coefficient
      _ ≤ 16 * activity := by
        simpa only [mul_assoc] using localCharge
  exact Nat.le_of_mul_le_mul_left scaled (by omega)

/--
Everything about an initialized interface trace that is already forced by
the checked block-count, conversion-accounting, and value-potential theorems.

None of these facts classifies a pairing as important/unimportant, paid, or a
zig-zig pairing.  Keeping them in a separate automatically constructible
record prevents the persistent block-list length from being confused with the
manuscript's independently classified count of lazy intervals.
-/
structure AutomaticTraceFacts
    {n : ℕ} {params : Interface.Parameters}
    {initial final : Interface.State n}
    {operations : List (Interface.Operation n)}
    (initialState : initial.Initial params)
    (trace : Interface.Trace params initial operations final) where
  blocks_length_eq :
    final.blocks.length =
      initial.blocks.length + Interface.totalBlockGrowth operations
  convertedMass : ℕ
  conversionHistory :
    Interface.ConversionHistory params
      initial operations final convertedMass
  convertedMass_le_entries :
    convertedMass ≤
      Interface.totalInserts operations +
        Interface.totalActivity operations
  valueChanges_le :
    Interface.totalValueChanges operations ≤
      2 * Interface.totalIncreases operations +
        (2 * n + 1) * params.valueBound

namespace AutomaticTraceFacts

/-- The automatic trace facts require no translation-specific premise. -/
noncomputable def ofTrace
    {n : ℕ} {params : Interface.Parameters}
    {initial final : Interface.State n}
    {operations : List (Interface.Operation n)}
    (initialState : initial.Initial params)
    (trace : Interface.Trace params initial operations final) :
    AutomaticTraceFacts initialState trace := by
  let existence :=
    trace.exists_conversionMass_le_entries initialState
  let convertedMass := Classical.choose existence
  let historyAndBound := Classical.choose_spec existence
  exact
    { blocks_length_eq := trace.blocks_length_eq
      convertedMass := convertedMass
      conversionHistory := historyAndBound.1
      convertedMass_le_entries := historyAndBound.2
      valueChanges_le :=
        trace.totalValueChanges_le initialState.1 }

end AutomaticTraceFacts

/--
A potential-reduced form of `SemanticCertificate.activity_budget`.

The checked value-potential theorem has already paid for all decreases.
Consequently a concrete translation only has to bound inserts, increases, and
the corrected initial potential `(2*n+1)*valueBound`; it does not need a
separate law about the total number of decreases.
-/
def PotentialBudget
    (constants : SemanticConstants)
    (insertConstant valueChangeConstant : ℕ)
    {n : ℕ} (params : Interface.Parameters)
    (operations : List (Interface.Operation n))
    (nearCost height paid unimportant : ℕ) : Prop :=
  insertConstant * params.valueBound *
        Interface.totalInserts operations +
      valueChangeConstant * Nat.clog 2 params.valueBound *
        (2 * Interface.totalIncreases operations +
          (2 * n + 1) * params.valueBound) ≤
    constants.interface *
      (paid * gapBound height * gapLog height +
        unimportant * gapBound height * gapLog height +
        (n + nearCost) * gapBound height * gapLog height ^ 2)

theorem activity_budget_of_potentialBudget
    {constants : SemanticConstants}
    {insertConstant valueChangeConstant : ℕ}
    {n : ℕ} {params : Interface.Parameters}
    {initial final : Interface.State n}
    {operations : List (Interface.Operation n)}
    {nearCost height paid unimportant : ℕ}
    (initialState : initial.Initial params)
    (trace : Interface.Trace params initial operations final)
    (budget :
      PotentialBudget constants insertConstant valueChangeConstant
        params operations nearCost height paid unimportant) :
    insertConstant * params.valueBound *
          Interface.totalInserts operations +
        valueChangeConstant * Nat.clog 2 params.valueBound *
          Interface.totalValueChanges operations ≤
      constants.interface *
        (paid * gapBound height * gapLog height +
          unimportant * gapBound height * gapLog height +
          (n + nearCost) * gapBound height * gapLog height ^ 2) := by
  calc
    insertConstant * params.valueBound *
          Interface.totalInserts operations +
        valueChangeConstant * Nat.clog 2 params.valueBound *
          Interface.totalValueChanges operations ≤
      insertConstant * params.valueBound *
          Interface.totalInserts operations +
        valueChangeConstant * Nat.clog 2 params.valueBound *
          (2 * Interface.totalIncreases operations +
            (2 * n + 1) * params.valueBound) := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_left _
          (trace.totalValueChanges_le initialState.1)) _
    _ ≤ constants.interface *
        (paid * gapBound height * gapLog height +
          unimportant * gapBound height * gapLog height +
          (n + nearCost) * gapBound height * gapLog height ^ 2) :=
      budget

/--
The original seven-field compatibility form for the concrete BST cost model.

The zig-zig and zig-zag counts are not arbitrary naturals: they are the
orientation counts of the chronological `concreteSplayTranscript`, indexed by
the concrete model's chosen `SplaySequence`.  Its cost decomposition is
therefore automatic.  The interface trace also makes the potential reduction
automatic, and `local_charge` makes
`unimportant_le_activity` automatic.  `EnvelopeReduction` later proves that
the seven fields below are propositionally equivalent to three combined
inequalities.

The four classified counts below are still numerical certificate data.  This
record does not manufacture the missing persistent-ID event map connecting
them and `trace` to the concrete `SplaySequence`; a future semantic
translation theorem must add that meaning rather than infer it from these
numbers.
-/
structure ConcreteTranslationCertificate
    (constants : TranslationConstants) (shape : Interface.Shape)
    (insertConstant valueChangeConstant : ℕ)
    (n nearCost height : ℕ)
    (initialTree : BST 0 n) (accesses : List (Fin n)) where
  params : Interface.Parameters
  initial : Interface.State n
  final : Interface.State n
  operations : List (Interface.Operation n)
  shape_eq : params.toShape = shape
  initialState : initial.Initial params
  trace : Interface.Trace params initial operations final

  blocks : ℕ
  paid : ℕ
  important : ℕ
  unimportant : ℕ

  blocks_le :
    blocks ≤ constants.semantic.blocks * (n + nearCost)
  important_le :
    important ≤
      constants.semantic.important * blocks * gapLog height
  paid_le :
    paid ≤
      unimportant +
        constants.semantic.paid * (n + nearCost) * gapLog height
  potential_budget :
    PotentialBudget constants.semantic
      insertConstant valueChangeConstant params operations
      nearCost height paid unimportant
  local_charge :
    (64 * constants.semantic.interface) *
        gapBound height * gapLog height * unimportant ≤
      16 * Interface.totalActivity operations
  zigZig_pairings :
    2 * (concreteSplayTranscript initialTree accesses).zigZig ≤
      important + unimportant +
        Interface.totalActivity operations
  zigZag_bends :
    (concreteSplayTranscript initialTree accesses).zigZag ≤
      (concreteSplayTranscript initialTree accesses).zigZig +
        constants.semantic.bends * (n + nearCost)

namespace ConcreteTranslationCertificate

/-- All generic trace accounting can be recovered from a concrete residue. -/
noncomputable def automaticTraceFacts
    {constants : TranslationConstants} {shape : Interface.Shape}
    {insertConstant valueChangeConstant n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)}
    (certificate :
      ConcreteTranslationCertificate constants shape
        insertConstant valueChangeConstant n nearCost height
        initialTree accesses) :
    AutomaticTraceFacts certificate.initialState certificate.trace :=
  AutomaticTraceFacts.ofTrace
    certificate.initialState certificate.trace

/--
The seven-law concrete residue constructs the earlier semantic certificate.
Every omitted field is discharged by a named checked theorem:

* value decreases by `Trace.totalValueChanges_le`;
* unimportant-to-internal charging by
  `unimportant_le_activity_of_localCharge`; and
* concrete splay cost by
  `concreteSplayTranscript_cost_decomposition`.
-/
noncomputable def toSemanticCertificate
    {constants : TranslationConstants} {shape : Interface.Shape}
    {insertConstant valueChangeConstant n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)}
    (certificate :
      ConcreteTranslationCertificate constants shape
        insertConstant valueChangeConstant n nearCost height
        initialTree accesses) :
    SemanticCertificate constants.semantic shape
      insertConstant valueChangeConstant
      n nearCost height
      (concreteSplayCost initialTree accesses)
      accesses.length := by
  refine
    { carrierSize := n
      params := certificate.params
      initial := certificate.initial
      final := certificate.final
      operations := certificate.operations
      shape_eq := certificate.shape_eq
      initialState := certificate.initialState
      trace := certificate.trace
      blocks := certificate.blocks
      paid := certificate.paid
      important := certificate.important
      unimportant := certificate.unimportant
      zigZig :=
        (concreteSplayTranscript initialTree accesses).zigZig
      zigZag :=
        (concreteSplayTranscript initialTree accesses).zigZag
      blocks_le := certificate.blocks_le
      important_le := certificate.important_le
      paid_le := certificate.paid_le
      activity_budget := ?_
      local_charge := certificate.local_charge
      unimportant_le_activity := ?_
      zigZig_pairings := certificate.zigZig_pairings
      zigZag_bends := certificate.zigZag_bends
      cost_decomposition := ?_ }
  · exact activity_budget_of_potentialBudget
      certificate.initialState certificate.trace
      certificate.potential_budget
  · exact unimportant_le_activity_of_localCharge
      constants.interface_pos certificate.local_charge
  · exact
      concreteSplayTranscript_cost_decomposition initialTree accesses

end ConcreteTranslationCertificate

/--
Uniform original seven-field residue for the concrete BST splay-cost model.
`EnvelopeReduction` provides the equivalent three-law API.
-/
def ConcreteTranslationHypothesis
    (comparison : ComparisonProfile) (shape : Interface.Shape) : Prop :=
  ∀ (insertConstant valueChangeConstant : ℕ),
    0 < insertConstant →
    0 < valueChangeConstant →
    ∃ constants : TranslationConstants,
      ∀ (n : ℕ), 0 < n →
        ∀ (initial : BST 0 n) (accesses : List (Fin n)),
          Nonempty
            (ConcreteTranslationCertificate constants shape
              insertConstant valueChangeConstant
              n
              (comparison.cost accesses)
              (comparison.maxHeight accesses)
              initial accesses)

/--
The concrete seven-law residue implies the generic semantic residue consumed
by `hypothesis_of_semanticReduction`.
-/
theorem semanticHypothesis_of_concreteTranslation
    (optCost : {n : ℕ} → List (Fin n) → ℕ)
    {comparison : ComparisonProfile} {shape : Interface.Shape}
    (translation :
      ConcreteTranslationHypothesis comparison shape) :
    SemanticHypothesis
      (concreteSplayCostModel optCost) comparison shape := by
  intro insertConstant valueChangeConstant
    insertPositive valueChangePositive
  obtain ⟨constants, certificates⟩ :=
    translation insertConstant valueChangeConstant
      insertPositive valueChangePositive
  refine ⟨constants.semantic, ?_⟩
  intro n hN initial accesses
  obtain ⟨certificate⟩ := certificates n hN initial accesses
  exact ⟨certificate.toSemanticCertificate⟩

/--
Direct proposition map from the original seven-field compatibility form to
`Accounting.Hypothesis` for the concrete BST cost model.
-/
theorem hypothesis_of_concreteTranslation
    (optCost : {n : ℕ} → List (Fin n) → ℕ)
    {comparison : ComparisonProfile}
    (shape : Interface.Shape)
    (requests : RequestCostDominates comparison)
    (translation :
      ConcreteTranslationHypothesis comparison shape) :
    Hypothesis (concreteSplayCostModel optCost) comparison :=
  hypothesis_of_semanticReduction shape requests
    (semanticHypothesis_of_concreteTranslation optCost translation)

/--
For a realized normal form, request-cost dominance is automatic.  Thus this
compatibility endpoint needs only the concrete translation family as its
accounting input; `EnvelopeReduction` shows that family's seven fields are
equivalent to three combined laws.
-/
theorem hypothesis_of_normalFormConcreteTranslation
    (optCost : {n : ℕ} → List (Fin n) → ℕ)
    (realization :
      Assumptions.NormalForm.Realization
        (concreteSplayCostModel optCost))
    (shape : Interface.Shape)
    (translation :
      ConcreteTranslationHypothesis
        realization.comparisonProfile shape) :
    Hypothesis
      (concreteSplayCostModel optCost)
      realization.comparisonProfile :=
  hypothesis_of_concreteTranslation optCost shape
    (requestCostDominates_of_normalFormRealization realization)
    translation

/--
Generic conditional endpoint for the concrete indexed-BST splay cost and an
arbitrary supplied optimum function.  `OfflineEndpoint` later specializes the
optimum to the attained root-based minimum, while `EnvelopeReduction` and
`PairingClassification` expose the equivalent reduced translation APIs.
-/
theorem targetBound_of_normalForm_and_concreteTranslation
    (optCost : {n : ℕ} → List (Fin n) → ℕ)
    (normalForm :
      Assumptions.NormalForm.Hypothesis
        (concreteSplayCostModel optCost))
    (shape : Interface.Shape)
    (translation :
      ConcreteTranslationHypothesis
        normalForm.realize.comparisonProfile shape) :
    TargetBound (concreteSplayCostModel optCost) :=
  targetBound_of_normalForm_and_semanticReduction
    (concreteSplayCostModel optCost) normalForm shape
    (semanticHypothesis_of_concreteTranslation optCost translation)

end Splay.Accounting
