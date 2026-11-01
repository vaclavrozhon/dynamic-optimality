import Splay.Accounting.Bridge
import Splay.Interface.InitialColumnIncidenceAssembly

namespace Splay.Accounting

/--
The comparison profile pays for serving the requests themselves.

This is automatic for a realized normal-form trace because its cost is the
number of requests plus the number of comparison-tree rotations.
-/
def RequestCostDominates (comparison : ComparisonProfile) : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ accesses : List (Fin n),
      accesses.length ≤ comparison.cost accesses

theorem requestCostDominates_of_normalFormRealization
    {model : CostModel}
    (realization : Assumptions.NormalForm.Realization model) :
    RequestCostDominates realization.comparisonProfile := by
  intro n hN accesses
  simp [Assumptions.NormalForm.Realization.comparisonProfile,
    Assumptions.NormalForm.ComparisonTrace.cost, hN]

/--
Uniform semantic constants still required from the concrete translation.

The absorption threshold is omitted: it is chosen canonically as
`64 * interface`, so the arithmetic side condition in `Constants` is proved
by reflexivity rather than assumed.
-/
structure SemanticConstants where
  blocks : ℕ
  important : ℕ
  interface : ℕ
  paid : ℕ
  bends : ℕ

namespace SemanticConstants

def toConstants (constants : SemanticConstants) : Constants where
  blocks := constants.blocks
  important := constants.important
  interface := constants.interface
  paid := constants.paid
  unimportantThreshold := 64 * constants.interface
  bends := constants.bends
  threshold_large := le_rfl

@[simp]
theorem toConstants_blocks (constants : SemanticConstants) :
    constants.toConstants.blocks = constants.blocks :=
  rfl

@[simp]
theorem toConstants_important (constants : SemanticConstants) :
    constants.toConstants.important = constants.important :=
  rfl

@[simp]
theorem toConstants_interface (constants : SemanticConstants) :
    constants.toConstants.interface = constants.interface :=
  rfl

@[simp]
theorem toConstants_paid (constants : SemanticConstants) :
    constants.toConstants.paid = constants.paid :=
  rfl

@[simp]
theorem toConstants_unimportantThreshold
    (constants : SemanticConstants) :
    constants.toConstants.unimportantThreshold =
      64 * constants.interface :=
  rfl

@[simp]
theorem toConstants_bends (constants : SemanticConstants) :
    constants.toConstants.bends = constants.bends :=
  rfl

end SemanticConstants

/--
The exact semantic residue needed for one accounting certificate.

`internal` is not supplied as an unconstrained count: it is definitionally
the total pass activity of a genuine interface trace.  Likewise `accesses`
and `zig` will both be instantiated by `requestCount`.  The interface
activity theorem and the comparison-cost lower bound therefore discharge
three fields of `Certificate`; the remaining fields below are precisely the
translation-specific event classifications and charging laws.
-/
structure SemanticCertificate
    (constants : SemanticConstants) (shape : Interface.Shape)
    (insertConstant valueChangeConstant : ℕ)
    (n nearCost height splayCost requestCount : ℕ) where
  carrierSize : ℕ
  params : Interface.Parameters
  initial : Interface.State carrierSize
  final : Interface.State carrierSize
  operations : List (Interface.Operation carrierSize)
  shape_eq : params.toShape = shape
  initialState : initial.Initial params
  trace : Interface.Trace params initial operations final

  blocks : ℕ
  paid : ℕ
  important : ℕ
  unimportant : ℕ
  zigZig : ℕ
  zigZag : ℕ

  blocks_le :
    blocks ≤ constants.blocks * (n + nearCost)
  important_le :
    important ≤
      constants.important * blocks * gapLog height
  paid_le :
    paid ≤
      unimportant +
        constants.paid * (n + nearCost) * gapLog height

  /--
  The remaining translation budget after applying `Interface.activityBound`.
  It relates visible insert/value-change work of the rich implementation to
  the paper's paid/unimportant/base categories.
  -/
  activity_budget :
    insertConstant * params.valueBound *
          Interface.totalInserts operations +
        valueChangeConstant * Nat.clog 2 params.valueBound *
          Interface.totalValueChanges operations ≤
      constants.interface *
        (paid * gapBound height * gapLog height +
          unimportant * gapBound height * gapLog height +
          (n + nearCost) * gapBound height * gapLog height ^ 2)

  local_charge :
    (64 * constants.interface) * gapBound height * gapLog height *
        unimportant ≤
      16 * Interface.totalActivity operations
  unimportant_le_activity :
    unimportant ≤ Interface.totalActivity operations
  zigZig_pairings :
    2 * zigZig ≤
      important + unimportant +
        Interface.totalActivity operations
  zigZag_bends :
    zigZag ≤
      zigZig + constants.bends * (n + nearCost)

  /--
  The essential `CostModel` semantic law for this instance.  The abstract
  structure itself imposes no relationship between `splayCost` and the
  structural splay execution, so this inequality cannot be derived from a
  normal-form schedule alone.
  -/
  cost_decomposition :
    splayCost ≤
      requestCount + requestCount + 2 * zigZig + 2 * zigZag

namespace SemanticCertificate

/--
Interface activity and request-cost dominance turn one semantic residue into
the existing numerical `Certificate`.
-/
def toCertificate
    {constants : SemanticConstants} {shape : Interface.Shape}
    {insertConstant valueChangeConstant : ℕ}
    {n nearCost height splayCost requestCount : ℕ}
    (semantic :
      SemanticCertificate constants shape
        insertConstant valueChangeConstant
        n nearCost height splayCost requestCount)
    (activity :
      ∀ (params : Interface.Parameters), params.toShape = shape →
        ∀ {carrierSize : ℕ}
          {initial final : Interface.State carrierSize}
          {operations : List (Interface.Operation carrierSize)},
          initial.Initial params →
          Interface.Trace params initial operations final →
          Interface.totalActivity operations ≤
            insertConstant * params.valueBound *
                Interface.totalInserts operations +
              valueChangeConstant * Nat.clog 2 params.valueBound *
                Interface.totalValueChanges operations)
    (requests_le : requestCount ≤ nearCost) :
    Certificate constants.toConstants
      n nearCost height splayCost := by
  refine
    { blocks := semantic.blocks
      paid := semantic.paid
      important := semantic.important
      unimportant := semantic.unimportant
      internal := Interface.totalActivity semantic.operations
      accesses := requestCount
      zig := requestCount
      zigZig := semantic.zigZig
      zigZag := semantic.zigZag
      blocks_le := ?_
      important_le := ?_
      paid_le := ?_
      internal_preabsorb := ?_
      local_charge := ?_
      unimportant_le_internal := semantic.unimportant_le_activity
      zigZig_pairings := semantic.zigZig_pairings
      zigZag_bends := ?_
      accesses_le := requests_le
      zig_le := le_rfl
      cost_le := semantic.cost_decomposition }
  · simpa using semantic.blocks_le
  · simpa using semantic.important_le
  · simpa using semantic.paid_le
  · exact
      (activity semantic.params semantic.shape_eq
        semantic.initialState semantic.trace).trans
        (by simpa using semantic.activity_budget)
  · simpa using semantic.local_charge
  · simpa using semantic.zigZag_bends

end SemanticCertificate

/--
Uniform semantic residue for a model and comparison profile.

The quantification over the two positive activity constants lets the proved
`Interface.activityBound` choose its own witnesses.  The concrete
translation may then choose uniform semantic constants large enough for
those witnesses.
-/
def SemanticHypothesis
    (model : CostModel) (comparison : ComparisonProfile)
    (shape : Interface.Shape) : Prop :=
  ∀ (insertConstant valueChangeConstant : ℕ),
    0 < insertConstant →
    0 < valueChangeConstant →
    ∃ constants : SemanticConstants,
      ∀ (n : ℕ), 0 < n →
        ∀ (initial : model.Initial n) (accesses : List (Fin n)),
          Nonempty
            (SemanticCertificate constants shape
              insertConstant valueChangeConstant
              n
              (comparison.cost accesses)
              (comparison.maxHeight accesses)
              (model.splayCost initial accesses)
              accesses.length)

/--
Exact reduction of the old monolithic accounting hypothesis.

The unconditional interface activity theorem supplies the internal-pairing
bound; `RequestCostDominates` supplies the access count.  What remains in
`SemanticHypothesis` is only the concrete translation/event semantics.
-/
theorem hypothesis_of_semanticReduction
    {model : CostModel} {comparison : ComparisonProfile}
    (shape : Interface.Shape)
    (requests : RequestCostDominates comparison)
    (semantics : SemanticHypothesis model comparison shape) :
    Hypothesis model comparison := by
  obtain
      ⟨insertConstant, valueChangeConstant,
        insertPositive, valueChangePositive, activity⟩ :=
    Interface.activityBound shape
  obtain ⟨constants, semanticCertificates⟩ :=
    semantics insertConstant valueChangeConstant
      insertPositive valueChangePositive
  refine ⟨constants.toConstants, ?_⟩
  intro n hN initial accesses
  obtain ⟨semantic⟩ :=
    semanticCertificates n hN initial accesses
  exact
    ⟨semantic.toCertificate activity
      (requests n hN accesses)⟩

/--
For a realized normal form, request-cost dominance is automatic.  Hence the
semantic residue is sufficient for the exact `Accounting.Hypothesis` consumed
by the final conditional theorem.
-/
theorem hypothesis_of_normalFormSemanticReduction
    {model : CostModel}
    (realization : Assumptions.NormalForm.Realization model)
    (shape : Interface.Shape)
    (semantics :
      SemanticHypothesis model
        realization.comparisonProfile shape) :
    Hypothesis model realization.comparisonProfile :=
  hypothesis_of_semanticReduction shape
    (requestCostDominates_of_normalFormRealization realization)
    semantics

/--
Direct conditional endpoint after replacing the monolithic accounting
certificate assumption by the smaller semantic translation residue.
-/
theorem targetBound_of_normalForm_and_semanticReduction
    (model : CostModel)
    (normalForm : Assumptions.NormalForm.Hypothesis model)
    (shape : Interface.Shape)
    (semantics :
      SemanticHypothesis model
        normalForm.realize.comparisonProfile shape) :
    TargetBound model :=
  targetBound_of_normalForm_and_accounting model normalForm
    (hypothesis_of_normalFormSemanticReduction
      normalForm.realize shape semantics)

end Splay.Accounting
