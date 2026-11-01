import Splay.Accounting.PotentialBudgetReduction
import Splay.Lazy.VisibleTraceOccurrence

namespace Splay.Accounting

namespace Interface.Operation

/-- Exactly the two visible operation kinds left by the potential reduction. -/
def isProductive {n : ℕ} : Interface.Operation n → Bool
  | .insert _ _ => true
  | .valueChange _ .increase => true
  | _ => false

/-- Semantic form of `isProductive`. -/
def Productive {n : ℕ} : Interface.Operation n → Prop
  | .insert _ _ => True
  | .valueChange _ .increase => True
  | _ => False

@[simp]
theorem isProductive_iff {n : ℕ}
    (operation : Interface.Operation n) :
    isProductive operation ↔ Productive operation := by
  cases operation with
  | valueChange element delta =>
      cases delta <;> simp [isProductive, Productive]
  | _ =>
      simp [isProductive, Productive]

end Interface.Operation

/-- Chronological indices of all inserts and value increases. -/
def productiveOperationIndices {n : ℕ}
    (operations : List (Interface.Operation n)) : List ℕ :=
  operations.findIdxs Interface.Operation.isProductive

/-- The canonical productive indices are never duplicated. -/
theorem productiveOperationIndices_nodup {n : ℕ}
    (operations : List (Interface.Operation n)) :
    (productiveOperationIndices operations).Nodup :=
  List.nodup_findIdxs

/--
Counting the canonical productive indices recovers exactly inserts plus
increases.
-/
@[simp]
theorem length_productiveOperationIndices {n : ℕ}
    (operations : List (Interface.Operation n)) :
    (productiveOperationIndices operations).length =
      productiveEvents operations := by
  unfold productiveOperationIndices productiveEvents
  rw [List.length_findIdxs]
  induction operations with
  | nil =>
      rfl
  | cons operation operations ih =>
      cases operation with
      | valueChange element delta =>
          cases delta with
          | decrease =>
              simpa [Interface.Operation.isProductive,
                Interface.totalInserts, Interface.totalIncreases,
                Interface.Operation.insertCount,
                Interface.Operation.increaseCount] using ih
          | increase =>
              simp [Interface.Operation.isProductive,
                Interface.totalInserts, Interface.totalIncreases, ih,
                Interface.Operation.insertCount,
                Interface.Operation.increaseCount]
              omega
      | convert block =>
          simpa [Interface.Operation.isProductive,
            Interface.totalInserts, Interface.totalIncreases,
            Interface.Operation.insertCount,
            Interface.Operation.increaseCount] using ih
      | create creator =>
          simpa [Interface.Operation.isProductive,
            Interface.totalInserts, Interface.totalIncreases,
            Interface.Operation.insertCount,
            Interface.Operation.increaseCount] using ih
      | insert block element =>
          simp [Interface.Operation.isProductive,
            Interface.totalInserts, Interface.totalIncreases, ih,
            Interface.Operation.insertCount,
            Interface.Operation.increaseCount]
          omega
      | delete block element =>
          simpa [Interface.Operation.isProductive,
            Interface.totalInserts, Interface.totalIncreases,
            Interface.Operation.insertCount,
            Interface.Operation.increaseCount] using ih
      | pass block matching =>
          simpa [Interface.Operation.isProductive,
            Interface.totalInserts, Interface.totalIncreases,
            Interface.Operation.insertCount,
            Interface.Operation.increaseCount] using ih
      | split block prefixLength =>
          simpa [Interface.Operation.isProductive,
            Interface.totalInserts, Interface.totalIncreases,
            Interface.Operation.insertCount,
            Interface.Operation.increaseCount] using ih

/--
Membership in the canonical index list exposes an actual productive operation.
-/
theorem productive_operation_at
    {n : ℕ} {operations : List (Interface.Operation n)}
    {index : ℕ}
    (member : index ∈ productiveOperationIndices operations) :
    ∃ inBounds : index < operations.length,
      Interface.Operation.Productive
        (operations.get ⟨index, inBounds⟩) := by
  obtain ⟨inBounds, productive⟩ :=
    List.mem_findIdxs_iff_exists_getElem_pos.mp member
  exact
    ⟨inBounds,
      (Interface.Operation.isProductive_iff _).mp productive⟩

/--
A checked partition of every actual productive operation into paid and
unimportant charge classes.

The class labels still need their manuscript semantics, but unlike a bare
count this record cannot omit, duplicate, or invent productive operations.
-/
structure ProductiveEventClassification
    {n : ℕ} (operations : List (Interface.Operation n)) where
  paidSlots : List ℕ
  unimportantSlots : List ℕ
  partition :
    (paidSlots ++ unimportantSlots).Perm
      (productiveOperationIndices operations)

namespace ProductiveEventClassification

/-- Every productive operation is covered exactly once by the two classes. -/
theorem counts_eq
    {n : ℕ} {operations : List (Interface.Operation n)}
    (classification : ProductiveEventClassification operations) :
    classification.paidSlots.length +
        classification.unimportantSlots.length =
      productiveEvents operations := by
  have lengthEq := classification.partition.length_eq
  simpa only [List.length_append,
    length_productiveOperationIndices] using lengthEq

/-- The checked partition contains no repeated chronological operation. -/
theorem slots_nodup
    {n : ℕ} {operations : List (Interface.Operation n)}
    (classification : ProductiveEventClassification operations) :
    (classification.paidSlots ++
      classification.unimportantSlots).Nodup :=
  classification.partition.symm.nodup
    (productiveOperationIndices_nodup operations)

end ProductiveEventClassification

/--
The productive-operation classification with exactly the two envelope bounds
needed by the potential reduction.
-/
structure EnvelopeProductiveEventClassification
    (constants : TranslationConstants)
    {n : ℕ} (operations : List (Interface.Operation n))
    (nearCost height : ℕ) where
  classification : ProductiveEventClassification operations
  paid_le :
    classification.paidSlots.length ≤
      paidEnvelope constants n nearCost height
        (unimportantEnvelope constants height
          (Interface.totalActivity operations))
  unimportant_le :
    classification.unimportantSlots.length ≤
      unimportantEnvelope constants height
        (Interface.totalActivity operations)

namespace EnvelopeProductiveEventClassification

/-- The checked operation partition implies the former count-only residue. -/
theorem toBudget
    {constants : TranslationConstants}
    {n : ℕ} {operations : List (Interface.Operation n)}
    {nearCost height : ℕ}
    (classification :
      EnvelopeProductiveEventClassification constants operations
        nearCost height) :
    EnvelopeProductiveEventBudget constants operations nearCost height := by
  unfold EnvelopeProductiveEventBudget ProductiveEventBudget
  rw [← classification.classification.counts_eq]
  exact
    Nat.add_le_add classification.paid_le
      classification.unimportant_le

end EnvelopeProductiveEventClassification

/--
Strong operation-level replacement for `EnvelopePotentialResidue`.
-/
structure WitnessedEnvelopePotentialResidue
    (constants : TranslationConstants)
    {n : ℕ} (params : Interface.Parameters)
    (operations : List (Interface.Operation n))
    (nearCost height : ℕ) where
  valueBound_le :
    params.valueBound ≤ gapBound height
  productiveClassification :
    EnvelopeProductiveEventClassification
      constants operations nearCost height

namespace WitnessedEnvelopePotentialResidue

/-- Forgetting operation identities recovers the reduced potential residue. -/
theorem toEnvelopePotentialResidue
    {constants : TranslationConstants}
    {n : ℕ} {params : Interface.Parameters}
    {operations : List (Interface.Operation n)}
    {nearCost height : ℕ}
    (residue :
      WitnessedEnvelopePotentialResidue constants params operations
        nearCost height) :
    EnvelopePotentialResidue constants params operations nearCost height where
  valueBound_le := residue.valueBound_le
  productive_events := residue.productiveClassification.toBudget

end WitnessedEnvelopePotentialResidue

/--
A classified productive index in an erased rich trace exposes the actual rich
event and its actual pre/post states.
-/
theorem exists_richProductiveStep
    {n : ℕ} {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}
    (trace : Lazy.Trace params initial events final)
    {index : ℕ}
    (member :
      index ∈ productiveOperationIndices
        (Lazy.eraseOperations events)) :
    ∃ eventIndex before operation after,
      Lazy.Trace.VisibleStepAt trace index eventIndex
        before operation after ∧
      Interface.Operation.Productive operation := by
  obtain ⟨inBounds, productive⟩ :=
    productive_operation_at member
  obtain ⟨eventIndex, before, operation, after, occurrence⟩ :=
    trace.exists_visibleStepAt ⟨index, inBounds⟩
  have selected :
      (Lazy.eraseOperations events).get
          ⟨index, occurrence.operationIndex_lt⟩ =
        operation :=
    occurrence.operation_eq_get
  have boundProofEq :
      (⟨index, occurrence.operationIndex_lt⟩ :
          Fin (Lazy.eraseOperations events).length) =
        ⟨index, inBounds⟩ :=
    Fin.ext rfl
  rw [boundProofEq, selected] at productive
  exact
    ⟨eventIndex, before, operation, after, occurrence, productive⟩

end Splay.Accounting
