import Splay.Accounting.TranslationReduction

namespace Splay.Accounting

/--
The largest block count permitted by the concrete translation certificate.

`blocks` is an existential intermediate count: after it has served to bound
`important`, no later theorem observes its exact value.  This envelope makes
that existential elimination explicit.
-/
def blockEnvelope
    (constants : TranslationConstants) (n nearCost : ℕ) : ℕ :=
  constants.semantic.blocks * (n + nearCost)

/--
The largest important-pairing count permitted after eliminating `blocks`.
-/
def importantEnvelope
    (constants : TranslationConstants)
    (n nearCost height : ℕ) : ℕ :=
  constants.semantic.important *
    blockEnvelope constants n nearCost * gapLog height

/--
The largest paid count permitted by `paid_le`.

Only this upper envelope is used by the potential budget, so the exact
existential paid count can likewise be eliminated.
-/
def paidEnvelope
    (constants : TranslationConstants)
    (n nearCost height unimportant : ℕ) : ℕ :=
  unimportant +
    constants.semantic.paid * (n + nearCost) * gapLog height

/--
The four-law envelope form of `ConcreteTranslationCertificate`.

This is not a semantic shortcut: the conversions below prove pointwise
equivalence (under `Nonempty`) with the seven-field certificate.  It merely
substitutes the three existential intermediate counts `blocks`, `important`,
and `paid` by the largest values allowed by their upper bounds.  The actual
remaining work is therefore:

* the visible-work/potential budget at the paid envelope;
* the local charge for unimportant pairings;
* the zig-zig inequality at the important envelope; and
* the zig-zag bend inequality.
-/
structure EnvelopeTranslationCertificate
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

  unimportant : ℕ

  potential_budget :
    PotentialBudget constants.semantic
      insertConstant valueChangeConstant params operations
      nearCost height
      (paidEnvelope constants n nearCost height unimportant)
      unimportant
  local_charge :
    (64 * constants.semantic.interface) *
        gapBound height * gapLog height * unimportant ≤
      16 * Interface.totalActivity operations
  zigZig_pairings :
    2 * (concreteSplayTranscript initialTree accesses).zigZig ≤
      importantEnvelope constants n nearCost height +
        unimportant + Interface.totalActivity operations
  zigZag_bends :
    (concreteSplayTranscript initialTree accesses).zigZag ≤
      (concreteSplayTranscript initialTree accesses).zigZig +
        constants.semantic.bends * (n + nearCost)

namespace EnvelopeTranslationCertificate

/--
Expanding the three envelopes recovers the original seven-field concrete
certificate.  Its three classification upper bounds hold by reflexivity.
-/
noncomputable def toConcrete
    {constants : TranslationConstants} {shape : Interface.Shape}
    {insertConstant valueChangeConstant n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)}
    (certificate :
      EnvelopeTranslationCertificate constants shape
        insertConstant valueChangeConstant n nearCost height
        initialTree accesses) :
    ConcreteTranslationCertificate constants shape
      insertConstant valueChangeConstant n nearCost height
      initialTree accesses where
  params := certificate.params
  initial := certificate.initial
  final := certificate.final
  operations := certificate.operations
  shape_eq := certificate.shape_eq
  initialState := certificate.initialState
  trace := certificate.trace
  blocks := blockEnvelope constants n nearCost
  paid :=
    paidEnvelope constants n nearCost height certificate.unimportant
  important := importantEnvelope constants n nearCost height
  unimportant := certificate.unimportant
  blocks_le := le_rfl
  important_le := le_rfl
  paid_le := le_rfl
  potential_budget := certificate.potential_budget
  local_charge := certificate.local_charge
  zigZig_pairings := certificate.zigZig_pairings
  zigZag_bends := certificate.zigZag_bends

/--
The two chained classification bounds imply the important envelope bound.
-/
theorem important_le_envelope
    {constants : TranslationConstants} {shape : Interface.Shape}
    {insertConstant valueChangeConstant n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)}
    (certificate :
      ConcreteTranslationCertificate constants shape
        insertConstant valueChangeConstant n nearCost height
        initialTree accesses) :
    certificate.important ≤
      importantEnvelope constants n nearCost height := by
  calc
    certificate.important ≤
        constants.semantic.important * certificate.blocks *
          gapLog height :=
      certificate.important_le
    _ ≤ constants.semantic.important *
          blockEnvelope constants n nearCost * gapLog height := by
      exact Nat.mul_le_mul_right _
        (Nat.mul_le_mul_left _ certificate.blocks_le)
    _ = importantEnvelope constants n nearCost height := rfl

/--
The paid classification bound implies the paid envelope bound.
-/
theorem paid_le_envelope
    {constants : TranslationConstants} {shape : Interface.Shape}
    {insertConstant valueChangeConstant n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)}
    (certificate :
      ConcreteTranslationCertificate constants shape
        insertConstant valueChangeConstant n nearCost height
        initialTree accesses) :
    certificate.paid ≤
      paidEnvelope constants n nearCost height
        certificate.unimportant :=
  certificate.paid_le

/--
Compressing an original certificate into envelope form.  Monotonicity of the
potential right-hand side and of the zig-zig right-hand side is the only
arithmetic involved.
-/
noncomputable def ofConcrete
    {constants : TranslationConstants} {shape : Interface.Shape}
    {insertConstant valueChangeConstant n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)}
    (certificate :
      ConcreteTranslationCertificate constants shape
        insertConstant valueChangeConstant n nearCost height
        initialTree accesses) :
    EnvelopeTranslationCertificate constants shape
      insertConstant valueChangeConstant n nearCost height
      initialTree accesses := by
  refine
    { params := certificate.params
      initial := certificate.initial
      final := certificate.final
      operations := certificate.operations
      shape_eq := certificate.shape_eq
      initialState := certificate.initialState
      trace := certificate.trace
      unimportant := certificate.unimportant
      potential_budget := ?_
      local_charge := certificate.local_charge
      zigZig_pairings := ?_
      zigZag_bends := certificate.zigZag_bends }
  · apply certificate.potential_budget.trans
    apply Nat.mul_le_mul_left constants.semantic.interface
    apply Nat.add_le_add_right
    apply Nat.add_le_add_right
    exact Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _
        certificate.paid_le)
  · apply certificate.zigZig_pairings.trans
    exact Nat.add_le_add_right
      (Nat.add_le_add_right
        (important_le_envelope certificate) _)
      _

end EnvelopeTranslationCertificate

/--
Pointwise equivalence of the seven-field and four-law certificate forms.
-/
theorem nonempty_envelopeTranslationCertificate_iff
    {constants : TranslationConstants} {shape : Interface.Shape}
    {insertConstant valueChangeConstant n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)} :
    Nonempty
        (EnvelopeTranslationCertificate constants shape
          insertConstant valueChangeConstant n nearCost height
          initialTree accesses) ↔
      Nonempty
        (ConcreteTranslationCertificate constants shape
          insertConstant valueChangeConstant n nearCost height
          initialTree accesses) := by
  constructor
  · rintro ⟨certificate⟩
    exact ⟨certificate.toConcrete⟩
  · rintro ⟨certificate⟩
    exact ⟨EnvelopeTranslationCertificate.ofConcrete certificate⟩

/--
Uniform four-law residue for the concrete BST splay-cost model.
-/
def EnvelopeTranslationHypothesis
    (comparison : ComparisonProfile) (shape : Interface.Shape) : Prop :=
  ∀ (insertConstant valueChangeConstant : ℕ),
    0 < insertConstant →
    0 < valueChangeConstant →
    ∃ constants : TranslationConstants,
      ∀ (n : ℕ), 0 < n →
        ∀ (initial : BST 0 n) (accesses : List (Fin n)),
          Nonempty
            (EnvelopeTranslationCertificate constants shape
              insertConstant valueChangeConstant
              n
              (comparison.cost accesses)
              (comparison.maxHeight accesses)
              initial accesses)

/--
The uniform envelope residue and the seven-field residue are propositionally
equivalent.
-/
theorem envelopeTranslationHypothesis_iff
    {comparison : ComparisonProfile} {shape : Interface.Shape} :
    EnvelopeTranslationHypothesis comparison shape ↔
      ConcreteTranslationHypothesis comparison shape := by
  constructor
  · intro envelope insertConstant valueChangeConstant
      insertPositive valueChangePositive
    obtain ⟨constants, certificates⟩ :=
      envelope insertConstant valueChangeConstant
        insertPositive valueChangePositive
    refine ⟨constants, ?_⟩
    intro n nPositive initial accesses
    rw [← nonempty_envelopeTranslationCertificate_iff]
    exact certificates n nPositive initial accesses
  · intro concrete insertConstant valueChangeConstant
      insertPositive valueChangePositive
    obtain ⟨constants, certificates⟩ :=
      concrete insertConstant valueChangeConstant
        insertPositive valueChangePositive
    refine ⟨constants, ?_⟩
    intro n nPositive initial accesses
    rw [nonempty_envelopeTranslationCertificate_iff]
    exact certificates n nPositive initial accesses

/--
Direct `Accounting.Hypothesis` endpoint from the four-law envelope residue.
-/
theorem hypothesis_of_envelopeTranslation
    (optCost : {n : ℕ} → List (Fin n) → ℕ)
    {comparison : ComparisonProfile}
    (shape : Interface.Shape)
    (requests : RequestCostDominates comparison)
    (translation :
      EnvelopeTranslationHypothesis comparison shape) :
    Hypothesis (concreteSplayCostModel optCost) comparison :=
  hypothesis_of_concreteTranslation optCost shape requests
    (envelopeTranslationHypothesis_iff.mp translation)

/--
The positive coefficient in the local unimportant-pairing charge.
-/
def unimportantChargeCoefficient
    (constants : TranslationConstants) (height : ℕ) : ℕ :=
  (64 * constants.semantic.interface) *
    gapBound height * gapLog height

theorem unimportantChargeCoefficient_pos
    (constants : TranslationConstants) (height : ℕ) :
    0 < unimportantChargeCoefficient constants height := by
  unfold unimportantChargeCoefficient
  exact Nat.mul_pos
    (Nat.mul_pos
      (Nat.mul_pos (by norm_num) constants.interface_pos)
      (gapBound_pos height))
    (gapLog_pos height)

/--
The largest unimportant count allowed by the local-charge inequality.
-/
def unimportantEnvelope
    (constants : TranslationConstants) (height activity : ℕ) : ℕ :=
  (16 * activity) /
    unimportantChargeCoefficient constants height

theorem unimportantEnvelope_local_charge
    (constants : TranslationConstants) (height activity : ℕ) :
    unimportantChargeCoefficient constants height *
        unimportantEnvelope constants height activity ≤
      16 * activity := by
  exact
    Nat.mul_div_le (16 * activity)
      (unimportantChargeCoefficient constants height)

theorem le_unimportantEnvelope_of_local_charge
    {constants : TranslationConstants} {height activity unimportant : ℕ}
    (localCharge :
      unimportantChargeCoefficient constants height * unimportant ≤
        16 * activity) :
    unimportant ≤
      unimportantEnvelope constants height activity := by
  apply
    (Nat.le_div_iff_mul_le
      (unimportantChargeCoefficient_pos constants height)).2
  simpa only [mul_comm] using localCharge

/--
The final three-law residue.

The remaining `unimportant` existential is replaced by the largest natural
number satisfying its local-charge inequality.  Increasing this count only
weakens the potential and zig-zig obligations, while local charge at the
quotient envelope follows from `Nat.mul_div_le`.  Together with the earlier
block/important/paid elimination, only three combined inequalities remain.
-/
structure ThreeLawTranslationCertificate
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

  potential_budget :
    PotentialBudget constants.semantic
      insertConstant valueChangeConstant params operations
      nearCost height
      (paidEnvelope constants n nearCost height
        (unimportantEnvelope constants height
          (Interface.totalActivity operations)))
      (unimportantEnvelope constants height
        (Interface.totalActivity operations))
  zigZig_pairings :
    2 * (concreteSplayTranscript initialTree accesses).zigZig ≤
      importantEnvelope constants n nearCost height +
        unimportantEnvelope constants height
          (Interface.totalActivity operations) +
        Interface.totalActivity operations
  zigZag_bends :
    (concreteSplayTranscript initialTree accesses).zigZag ≤
      (concreteSplayTranscript initialTree accesses).zigZig +
        constants.semantic.bends * (n + nearCost)

namespace ThreeLawTranslationCertificate

/--
The quotient envelope automatically reconstructs the four-law form.
-/
noncomputable def toEnvelope
    {constants : TranslationConstants} {shape : Interface.Shape}
    {insertConstant valueChangeConstant n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)}
    (certificate :
      ThreeLawTranslationCertificate constants shape
        insertConstant valueChangeConstant n nearCost height
        initialTree accesses) :
    EnvelopeTranslationCertificate constants shape
      insertConstant valueChangeConstant n nearCost height
      initialTree accesses where
  params := certificate.params
  initial := certificate.initial
  final := certificate.final
  operations := certificate.operations
  shape_eq := certificate.shape_eq
  initialState := certificate.initialState
  trace := certificate.trace
  unimportant :=
    unimportantEnvelope constants height
      (Interface.totalActivity certificate.operations)
  potential_budget := certificate.potential_budget
  local_charge := by
    simpa only [unimportantChargeCoefficient] using
      unimportantEnvelope_local_charge constants height
        (Interface.totalActivity certificate.operations)
  zigZig_pairings := certificate.zigZig_pairings
  zigZag_bends := certificate.zigZag_bends

/--
Every four-law certificate's unimportant count lies below the quotient
envelope forced by its local charge.
-/
theorem unimportant_le_envelope
    {constants : TranslationConstants} {shape : Interface.Shape}
    {insertConstant valueChangeConstant n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)}
    (certificate :
      EnvelopeTranslationCertificate constants shape
        insertConstant valueChangeConstant n nearCost height
        initialTree accesses) :
    certificate.unimportant ≤
      unimportantEnvelope constants height
        (Interface.totalActivity certificate.operations) := by
  apply le_unimportantEnvelope_of_local_charge
  simpa only [unimportantChargeCoefficient] using
    certificate.local_charge

/--
Compressing the four-law form into the three-law quotient envelope.
-/
noncomputable def ofEnvelope
    {constants : TranslationConstants} {shape : Interface.Shape}
    {insertConstant valueChangeConstant n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)}
    (certificate :
      EnvelopeTranslationCertificate constants shape
        insertConstant valueChangeConstant n nearCost height
        initialTree accesses) :
    ThreeLawTranslationCertificate constants shape
      insertConstant valueChangeConstant n nearCost height
      initialTree accesses := by
  let unimportantMax :=
    unimportantEnvelope constants height
      (Interface.totalActivity certificate.operations)
  have unimportantLe :
      certificate.unimportant ≤ unimportantMax := by
    exact unimportant_le_envelope certificate
  have paidLe :
      paidEnvelope constants n nearCost height
          certificate.unimportant ≤
        paidEnvelope constants n nearCost height unimportantMax := by
    unfold paidEnvelope
    exact Nat.add_le_add_right unimportantLe _
  refine
    { params := certificate.params
      initial := certificate.initial
      final := certificate.final
      operations := certificate.operations
      shape_eq := certificate.shape_eq
      initialState := certificate.initialState
      trace := certificate.trace
      potential_budget := ?_
      zigZig_pairings := ?_
      zigZag_bends := certificate.zigZag_bends }
  · apply certificate.potential_budget.trans
    apply Nat.mul_le_mul_left constants.semantic.interface
    apply Nat.add_le_add_right
    exact Nat.add_le_add
      (Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right _ paidLe))
      (Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right _ unimportantLe))
  · apply certificate.zigZig_pairings.trans
    exact Nat.add_le_add_right
      (Nat.add_le_add_left unimportantLe _)
      _

end ThreeLawTranslationCertificate

/--
Pointwise equivalence of the four-law and three-law certificate forms.
-/
theorem nonempty_threeLawTranslationCertificate_iff
    {constants : TranslationConstants} {shape : Interface.Shape}
    {insertConstant valueChangeConstant n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)} :
    Nonempty
        (ThreeLawTranslationCertificate constants shape
          insertConstant valueChangeConstant n nearCost height
          initialTree accesses) ↔
      Nonempty
        (EnvelopeTranslationCertificate constants shape
          insertConstant valueChangeConstant n nearCost height
          initialTree accesses) := by
  constructor
  · rintro ⟨certificate⟩
    exact ⟨certificate.toEnvelope⟩
  · rintro ⟨certificate⟩
    exact ⟨ThreeLawTranslationCertificate.ofEnvelope certificate⟩

/--
Pointwise equivalence with the original seven-field concrete certificate.
-/
theorem nonempty_threeLawTranslationCertificate_iff_concrete
    {constants : TranslationConstants} {shape : Interface.Shape}
    {insertConstant valueChangeConstant n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)} :
    Nonempty
        (ThreeLawTranslationCertificate constants shape
          insertConstant valueChangeConstant n nearCost height
          initialTree accesses) ↔
      Nonempty
        (ConcreteTranslationCertificate constants shape
          insertConstant valueChangeConstant n nearCost height
          initialTree accesses) :=
  nonempty_threeLawTranslationCertificate_iff.trans
    nonempty_envelopeTranslationCertificate_iff

/--
Uniform three-law residue for the concrete BST splay-cost model.
-/
def ThreeLawTranslationHypothesis
    (comparison : ComparisonProfile) (shape : Interface.Shape) : Prop :=
  ∀ (insertConstant valueChangeConstant : ℕ),
    0 < insertConstant →
    0 < valueChangeConstant →
    ∃ constants : TranslationConstants,
      ∀ (n : ℕ), 0 < n →
        ∀ (initial : BST 0 n) (accesses : List (Fin n)),
          Nonempty
            (ThreeLawTranslationCertificate constants shape
              insertConstant valueChangeConstant
              n
              (comparison.cost accesses)
              (comparison.maxHeight accesses)
              initial accesses)

/--
The final three-law residue and the original seven-field residue are
propositionally equivalent.
-/
theorem threeLawTranslationHypothesis_iff
    {comparison : ComparisonProfile} {shape : Interface.Shape} :
    ThreeLawTranslationHypothesis comparison shape ↔
      ConcreteTranslationHypothesis comparison shape := by
  constructor
  · intro reduced insertConstant valueChangeConstant
      insertPositive valueChangePositive
    obtain ⟨constants, certificates⟩ :=
      reduced insertConstant valueChangeConstant
        insertPositive valueChangePositive
    refine ⟨constants, ?_⟩
    intro n nPositive initial accesses
    rw [← nonempty_threeLawTranslationCertificate_iff_concrete]
    exact certificates n nPositive initial accesses
  · intro concrete insertConstant valueChangeConstant
      insertPositive valueChangePositive
    obtain ⟨constants, certificates⟩ :=
      concrete insertConstant valueChangeConstant
        insertPositive valueChangePositive
    refine ⟨constants, ?_⟩
    intro n nPositive initial accesses
    rw [nonempty_threeLawTranslationCertificate_iff_concrete]
    exact certificates n nPositive initial accesses

/--
Direct `Accounting.Hypothesis` endpoint from the three combined laws.
-/
theorem hypothesis_of_threeLawTranslation
    (optCost : {n : ℕ} → List (Fin n) → ℕ)
    {comparison : ComparisonProfile}
    (shape : Interface.Shape)
    (requests : RequestCostDominates comparison)
    (translation :
      ThreeLawTranslationHypothesis comparison shape) :
    Hypothesis (concreteSplayCostModel optCost) comparison :=
  hypothesis_of_concreteTranslation optCost shape requests
    (threeLawTranslationHypothesis_iff.mp translation)

/--
A realized normal form supplies request-cost dominance automatically, leaving
only the three combined translation laws.
-/
theorem hypothesis_of_normalFormThreeLawTranslation
    (optCost : {n : ℕ} → List (Fin n) → ℕ)
    (realization :
      Assumptions.NormalForm.Realization
        (concreteSplayCostModel optCost))
    (shape : Interface.Shape)
    (translation :
      ThreeLawTranslationHypothesis
        realization.comparisonProfile shape) :
    Hypothesis
      (concreteSplayCostModel optCost)
      realization.comparisonProfile :=
  hypothesis_of_threeLawTranslation optCost shape
    (requestCostDominates_of_normalFormRealization realization)
    translation

/--
Direct endpoint when the chosen normal-form realization is already available
as reusable data.
-/
theorem targetBound_of_normalFormRealization_and_threeLawTranslation
    (optCost : {n : ℕ} → List (Fin n) → ℕ)
    (realization :
      Assumptions.NormalForm.Realization
        (concreteSplayCostModel optCost))
    (shape : Interface.Shape)
    (translation :
      ThreeLawTranslationHypothesis
        realization.comparisonProfile shape) :
    TargetBound (concreteSplayCostModel optCost) :=
  Assumptions.NormalForm.targetBound_of_normalForm_and_core
    (concreteSplayCostModel optCost) realization
    (hypothesis_of_normalFormThreeLawTranslation
      optCost realization shape translation).hasCoreAnalysisBound

/--
Direct conditional endpoint analogous to
`targetBound_of_normalForm_and_concreteTranslation`, with the propositionally
equivalent three-law residue in place of the original seven fields.
-/
theorem targetBound_of_normalForm_and_threeLawTranslation
    (optCost : {n : ℕ} → List (Fin n) → ℕ)
    (normalForm :
      Assumptions.NormalForm.Hypothesis
        (concreteSplayCostModel optCost))
    (shape : Interface.Shape)
    (translation :
      ThreeLawTranslationHypothesis
        normalForm.realize.comparisonProfile shape) :
    TargetBound (concreteSplayCostModel optCost) :=
  targetBound_of_normalFormRealization_and_threeLawTranslation
    optCost normalForm.realize shape translation

end Splay.Accounting
