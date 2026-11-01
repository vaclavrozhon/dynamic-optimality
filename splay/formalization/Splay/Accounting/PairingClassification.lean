import Splay.Accounting.SplayPairingTranscript
import Splay.Accounting.EnvelopeReduction
import Splay.Interface.Activity

namespace Splay.Accounting

open Splay.Tree.BST

/--
The concatenated first/second transcript slots are genuine distinct
occurrences: phases distinguish the two slots belonging to one zig-zig, and
chronological step indices distinguish slots within either phase.
-/
theorem allPairingSlots_nodup (kinds : List SplayStepKind) :
    (firstPairings kinds ++ secondPairings kinds).Nodup :=
  (firstPairings_nodup kinds).append
    (secondPairings_nodup kinds)
    (firstPairings_disjoint_secondPairings kinds)

/--
A checked classification of the two pairing slots contributed by every
zig-zig in one concrete chronological splay transcript.

The important and unimportant classes retain the actual transcript slots.
Every internal slot is paired with a proof-indexed position in the
deterministic activity history of the supplied interface trace.  Positions,
rather than occurrence values, distinguish two chronologically different
units of activity that happen to have equal annotations.
`internalActivitySlots_nodup` is precisely the injectivity of that charge.

Thus this record contains no independent numerical pairing counts: all three
cardinalities are lengths of checked finite lists.
-/
structure PairingClassification
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    (params : Interface.Parameters)
    (initial final : Interface.State n)
    (operations : List (Interface.Operation n)) where
  initialState : initial.Initial params
  trace : Interface.Trace params initial operations final

  finalLabels : Interface.RootLabels
  activityOccurrences : List (Interface.ActivityOccurrence n)
  activityHistory :
    Interface.ActivityHistory params initial [] operations
      activityOccurrences final finalLabels

  importantSlots : List PairingSlot
  unimportantSlots : List PairingSlot
  internalCharges :
    List (PairingSlot × Fin activityOccurrences.length)

  /--
  Every first/second slot occurs in exactly one of the three classes, with
  multiplicity preserved.  The transcript later proves that this right-hand
  list has exactly `2 * zigZig` entries.
  -/
  slots_partition :
    (importantSlots ++ unimportantSlots ++
        internalCharges.map Prod.fst).Perm
      (firstPairings kinds ++ secondPairings kinds)

  /--
  No proof-indexed activity slot pays twice.  Since its type is
  `Fin activityOccurrences.length`, every target is automatically a concrete
  position in this exact history, even when occurrence values repeat.
  -/
  internalActivitySlots_nodup :
    (internalCharges.map Prod.snd).Nodup

namespace PairingClassification

variable
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {params : Interface.Parameters}
    {initial final : Interface.State n}
    {operations : List (Interface.Operation n)}

/-- Important count, definitionally the length of the checked slot list. -/
def importantCount
    (classification :
      PairingClassification transcript params initial final operations) :
    ℕ :=
  classification.importantSlots.length

/-- Unimportant count, definitionally the length of the checked slot list. -/
def unimportantCount
    (classification :
      PairingClassification transcript params initial final operations) :
    ℕ :=
  classification.unimportantSlots.length

/-- Internal count, definitionally the length of the checked charge list. -/
def internalCount
    (classification :
      PairingClassification transcript params initial final operations) :
    ℕ :=
  classification.internalCharges.length

/--
The checked partition inherits distinctness from the actual transcript
slots.  In particular a slot cannot silently occur in two classification
categories.
-/
theorem classifiedSlots_nodup
    (classification :
      PairingClassification transcript params initial final operations) :
    (classification.importantSlots ++ classification.unimportantSlots ++
        classification.internalCharges.map Prod.fst).Nodup :=
  classification.slots_partition.symm.nodup
    (allPairingSlots_nodup kinds)

/--
The internal charge list is no longer than the actual activity-occurrence
list.  This is the finite injection into proof-indexed chronological slots,
not an accidental uniqueness claim about occurrence values.
-/
theorem internalCount_le_activityOccurrences
    (classification :
      PairingClassification transcript params initial final operations) :
    classification.internalCount ≤
      classification.activityOccurrences.length := by
  have bound :=
    classification.internalActivitySlots_nodup.length_le_card
  simpa only [internalCount, List.length_map, Fintype.card_fin] using bound

/--
The checked activity history identifies its occurrence-list length with
exactly `Interface.totalActivity operations`.
-/
theorem activityOccurrences_length
    (classification :
      PairingClassification transcript params initial final operations) :
    classification.activityOccurrences.length =
      Interface.totalActivity operations :=
  classification.activityHistory.occurrences_length

/--
The three checked classes contain exactly the two slots of every genuine
zig-zig, with no numerical slack.
-/
theorem classifiedCounts_eq
    (classification :
      PairingClassification transcript params initial final operations) :
    classification.importantCount +
        classification.unimportantCount +
        classification.internalCount =
      2 * zigZig := by
  have partitionLength := classification.slots_partition.length_eq
  have slotsLength := total_pairingSlots transcript
  simp only [List.length_append, List.length_map] at partitionLength
  unfold importantCount unimportantCount internalCount
  omega

/--
The transcript partition and injective internal charge automatically imply
the formerly numerical `zigZig_pairings` inequality.
-/
theorem zigZig_pairings
    (classification :
      PairingClassification transcript params initial final operations) :
    2 * zigZig ≤
      classification.importantCount +
        classification.unimportantCount +
        Interface.totalActivity operations := by
  have internalBound :=
    classification.internalCount_le_activityOccurrences
  have activityLength := classification.activityOccurrences_length
  have counts := classification.classifiedCounts_eq
  omega

end PairingClassification

/--
The occurrence list needed by a pairing classification is automatic for
every initialized interface trace.  This is the exact source used in
`PairingClassification.activityHistory`; the remaining input is only the
slot partition and its injective internal charge.
-/
theorem exists_activityGrouping_for_pairingClassification
    {n : ℕ} {params : Interface.Parameters}
    {initial final : Interface.State n}
    {operations : List (Interface.Operation n)}
    (initialState : initial.Initial params)
    (trace : Interface.Trace params initial operations final) :
    ∃ (finalLabels : Interface.RootLabels)
        (occurrences : List (Interface.ActivityOccurrence n)),
      Interface.ActivityHistory params initial [] operations
          occurrences final finalLabels ∧
        occurrences.length = Interface.totalActivity operations := by
  obtain
      ⟨finalLabels, occurrences, history, _labelsAligned,
        _rootsTracked, _grouped⟩ :=
    trace.existsActivityGrouping initialState
  exact
    ⟨finalLabels, occurrences, history,
      history.occurrences_length⟩

/--
The value annotation stored at an internally charged, proof-indexed activity
slot.  Keeping the index in the certificate is what makes two equal-valued
occurrences at different chronological positions distinct accounting units.
-/
def PairingClassification.internalActivityOccurrences
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {params : Interface.Parameters}
    {initial final : Interface.State n}
    {operations : List (Interface.Operation n)}
    (classification :
      PairingClassification transcript params initial final operations) :
    List (PairingSlot × Interface.ActivityOccurrence n) :=
  classification.internalCharges.map fun charge =>
    (charge.1, classification.activityOccurrences.get charge.2)

private structure BoundedThreeWayPartition
    {α : Type} (slots : List α)
    (firstBound secondBound thirdBound : ℕ) where
  first : List α
  second : List α
  third : List α
  cover : first ++ second ++ third = slots
  first_le : first.length ≤ firstBound
  second_le : second.length ≤ secondBound
  third_le : third.length ≤ thirdBound

/--
Every list whose length is bounded by three capacities admits the canonical
take/drop partition respecting those capacities.
-/
private def boundedThreeWayPartition
    {α : Type} (slots : List α)
    (firstBound secondBound thirdBound : ℕ)
    (total_le :
      slots.length ≤ firstBound + secondBound + thirdBound) :
    BoundedThreeWayPartition slots
      firstBound secondBound thirdBound := by
  let first := slots.take firstBound
  let remainder := slots.drop firstBound
  let second := remainder.take secondBound
  let third := remainder.drop secondBound
  refine
    { first := first
      second := second
      third := third
      cover := ?_
      first_le := ?_
      second_le := ?_
      third_le := ?_ }
  · dsimp only [first, second, third, remainder]
    rw [List.append_assoc, List.take_append_drop,
      List.take_append_drop]
  · simp only [first, List.length_take]
    exact Nat.min_le_left _ _
  · simp only [second, List.length_take]
    exact Nat.min_le_left _ _
  · simp only [third, remainder, List.length_drop]
    omega

/--
Pair each list entry with its own index, embedded into any sufficiently large
finite activity-slot type.
-/
private def indexedCharges
    (slots : List PairingSlot) {activityCount : ℕ}
    (length_le : slots.length ≤ activityCount) :
    List (PairingSlot × Fin activityCount) :=
  (List.finRange slots.length).map fun index =>
    (slots.get index,
      ⟨index.val, index.isLt.trans_le length_le⟩)

private theorem indexedCharges_slots
    (slots : List PairingSlot) {activityCount : ℕ}
    (length_le : slots.length ≤ activityCount) :
    (indexedCharges slots length_le).map Prod.fst = slots := by
  simp only [indexedCharges, List.map_map]
  exact List.map_get_finRange slots

private theorem indexedCharges_activitySlots_nodup
    (slots : List PairingSlot) {activityCount : ℕ}
    (length_le : slots.length ≤ activityCount) :
    ((indexedCharges slots length_le).map Prod.snd).Nodup := by
  simp only [indexedCharges, List.map_map]
  apply List.Nodup.map
  · intro first second equal
    simp only [Function.comp_apply] at equal
    apply Fin.ext
    exact
      congrArg (fun index : Fin activityCount => index.val) equal
  · exact List.nodup_finRange slots.length

/--
Specialization of the checked classification to the concrete cost model's
chosen splay sequence and its proof-relevant chronological transcript.
-/
abbrev ConcretePairingClassification
    {n : ℕ} (initialTree : BST 0 n) (accesses : List (Fin n))
    (params : Interface.Parameters)
    (initial final : Interface.State n)
    (operations : List (Interface.Operation n)) :=
  PairingClassification
    (concreteSplayTranscript initialTree accesses).transcript
    params initial final operations

namespace ConcretePairingClassification

/--
Concrete transcript form of the automatic zig-zig pairing inequality.
-/
theorem zigZig_pairings
    {n : ℕ} {initialTree : BST 0 n} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initial final : Interface.State n}
    {operations : List (Interface.Operation n)}
    (classification :
      ConcretePairingClassification initialTree accesses
        params initial final operations) :
    2 * (concreteSplayTranscript initialTree accesses).zigZig ≤
      classification.importantCount +
        classification.unimportantCount +
        Interface.totalActivity operations :=
  PairingClassification.zigZig_pairings classification

end ConcretePairingClassification

/--
The three-law residue with its numerical zig-zig inequality replaced by an
actual transcript-slot classification and an injective charge into the
proof-indexed positions of the interface trace's activity history.

The two remaining classification bounds compare the lengths of the checked
important and unimportant slot lists with the canonical envelopes already
used by `ThreeLawTranslationCertificate`.  The converse construction below
shows that this is a proof-relevant presentation of the numerical law, not yet
the manuscript's endpoint/adjacency semantics.
-/
structure ClassifiedThreeLawTranslationCertificate
    (constants : TranslationConstants) (shape : Interface.Shape)
    (insertConstant valueChangeConstant : ℕ)
    (n nearCost height : ℕ)
    (initialTree : BST 0 n) (accesses : List (Fin n)) where
  params : Interface.Parameters
  initial : Interface.State n
  final : Interface.State n
  operations : List (Interface.Operation n)
  shape_eq : params.toShape = shape

  classification :
    ConcretePairingClassification initialTree accesses
      params initial final operations

  important_le :
    classification.importantCount ≤
      importantEnvelope constants n nearCost height
  unimportant_le :
    classification.unimportantCount ≤
      unimportantEnvelope constants height
        (Interface.totalActivity operations)

  potential_budget :
    PotentialBudget constants.semantic
      insertConstant valueChangeConstant params operations
      nearCost height
      (paidEnvelope constants n nearCost height
        (unimportantEnvelope constants height
          (Interface.totalActivity operations)))
      (unimportantEnvelope constants height
        (Interface.totalActivity operations))
  zigZag_bends :
    (concreteSplayTranscript initialTree accesses).zigZag ≤
      (concreteSplayTranscript initialTree accesses).zigZig +
        constants.semantic.bends * (n + nearCost)

namespace ClassifiedThreeLawTranslationCertificate

/--
The checked partition and injective internal charge discharge the three-law
certificate's zig-zig field automatically.
-/
noncomputable def toThreeLaw
    {constants : TranslationConstants} {shape : Interface.Shape}
    {insertConstant valueChangeConstant n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)}
    (certificate :
      ClassifiedThreeLawTranslationCertificate constants shape
        insertConstant valueChangeConstant n nearCost height
        initialTree accesses) :
    ThreeLawTranslationCertificate constants shape
      insertConstant valueChangeConstant n nearCost height
      initialTree accesses := by
  refine
    { params := certificate.params
      initial := certificate.initial
      final := certificate.final
      operations := certificate.operations
      shape_eq := certificate.shape_eq
      initialState := certificate.classification.initialState
      trace := certificate.classification.trace
      potential_budget := certificate.potential_budget
      zigZig_pairings := ?_
      zigZag_bends := certificate.zigZag_bends }
  exact
    certificate.classification.zigZig_pairings.trans
      (Nat.add_le_add_right
        (Nat.add_le_add certificate.important_le
          certificate.unimportant_le)
        _)

/--
Conversely, every numerical three-law certificate admits a canonical checked
slot classification.

The construction greedily fills the important and unimportant envelopes and
then charges the remaining slots to distinct proof-indexed positions in the
actual activity history.  This theorem is intentionally combinatorial: it
does not claim that these labels are the manuscript's time-fixed
heap-child/lazy-interval classification.
-/
noncomputable def ofThreeLaw
    {constants : TranslationConstants} {shape : Interface.Shape}
    {insertConstant valueChangeConstant n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)}
    (certificate :
      ThreeLawTranslationCertificate constants shape
        insertConstant valueChangeConstant n nearCost height
        initialTree accesses) :
    ClassifiedThreeLawTranslationCertificate constants shape
      insertConstant valueChangeConstant n nearCost height
      initialTree accesses := by
  let transcript := concreteSplayTranscript initialTree accesses
  let slots :=
    firstPairings transcript.kinds ++ secondPairings transcript.kinds
  let grouping :=
    exists_activityGrouping_for_pairingClassification
      certificate.initialState certificate.trace
  let finalLabels := Classical.choose grouping
  let occurrences :=
    Classical.choose (Classical.choose_spec grouping)
  have groupingSpec :=
    Classical.choose_spec (Classical.choose_spec grouping)
  have activityHistory :
      Interface.ActivityHistory certificate.params certificate.initial []
        certificate.operations occurrences certificate.final finalLabels :=
    groupingSpec.1
  have occurrencesLength :
      occurrences.length =
        Interface.totalActivity certificate.operations :=
    groupingSpec.2
  have slotsLength :
      slots.length = 2 * transcript.zigZig := by
    dsimp only [slots]
    simp only [List.length_append]
    exact total_pairingSlots transcript.transcript
  let importantBound :=
    importantEnvelope constants n nearCost height
  let unimportantBound :=
    unimportantEnvelope constants height
      (Interface.totalActivity certificate.operations)
  have total_le :
      slots.length ≤
        importantBound + unimportantBound + occurrences.length := by
    rw [slotsLength, occurrencesLength]
    exact certificate.zigZig_pairings
  let partition :=
    boundedThreeWayPartition slots
      importantBound unimportantBound occurrences.length total_le
  let charges :=
    indexedCharges partition.third partition.third_le
  let classification :
      ConcretePairingClassification initialTree accesses
        certificate.params certificate.initial certificate.final
        certificate.operations :=
    { initialState := certificate.initialState
      trace := certificate.trace
      finalLabels := finalLabels
      activityOccurrences := occurrences
      activityHistory := activityHistory
      importantSlots := partition.first
      unimportantSlots := partition.second
      internalCharges := charges
      slots_partition := by
        apply List.Perm.of_eq
        rw [indexedCharges_slots]
        exact partition.cover
      internalActivitySlots_nodup :=
        indexedCharges_activitySlots_nodup
          partition.third partition.third_le }
  refine
    { params := certificate.params
      initial := certificate.initial
      final := certificate.final
      operations := certificate.operations
      shape_eq := certificate.shape_eq
      classification := classification
      important_le := ?_
      unimportant_le := ?_
      potential_budget := certificate.potential_budget
      zigZag_bends := certificate.zigZag_bends }
  · simpa only [PairingClassification.importantCount,
      classification, importantBound] using partition.first_le
  · simpa only [PairingClassification.unimportantCount,
      classification, unimportantBound] using partition.second_le

end ClassifiedThreeLawTranslationCertificate

/--
The checked list-level classification is propositionally equivalent to the
three numerical laws.  Its value is proof relevance and auditability; the
future manuscript-specific endpoint/adjacency semantics must be added as
extra fields rather than inferred from this equivalence.
-/
theorem nonempty_classifiedThreeLawTranslationCertificate_iff
    {constants : TranslationConstants} {shape : Interface.Shape}
    {insertConstant valueChangeConstant n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)} :
    Nonempty
        (ClassifiedThreeLawTranslationCertificate constants shape
          insertConstant valueChangeConstant n nearCost height
          initialTree accesses) ↔
      Nonempty
        (ThreeLawTranslationCertificate constants shape
          insertConstant valueChangeConstant n nearCost height
          initialTree accesses) := by
  constructor
  · rintro ⟨certificate⟩
    exact ⟨certificate.toThreeLaw⟩
  · rintro ⟨certificate⟩
    exact
      ⟨ClassifiedThreeLawTranslationCertificate.ofThreeLaw certificate⟩

/--
Pointwise equivalence all the way back to the original seven-field
compatibility certificate.
-/
theorem nonempty_classifiedThreeLawTranslationCertificate_iff_concrete
    {constants : TranslationConstants} {shape : Interface.Shape}
    {insertConstant valueChangeConstant n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)} :
    Nonempty
        (ClassifiedThreeLawTranslationCertificate constants shape
          insertConstant valueChangeConstant n nearCost height
          initialTree accesses) ↔
      Nonempty
        (ConcreteTranslationCertificate constants shape
          insertConstant valueChangeConstant n nearCost height
          initialTree accesses) :=
  nonempty_classifiedThreeLawTranslationCertificate_iff.trans
    nonempty_threeLawTranslationCertificate_iff_concrete

/--
Uniform classified residue for the concrete BST splay-cost model.
-/
def ClassifiedThreeLawTranslationHypothesis
    (comparison : ComparisonProfile) (shape : Interface.Shape) : Prop :=
  ∀ (insertConstant valueChangeConstant : ℕ),
    0 < insertConstant →
    0 < valueChangeConstant →
    ∃ constants : TranslationConstants,
      ∀ (n : ℕ), 0 < n →
        ∀ (initial : BST 0 n) (accesses : List (Fin n)),
          Nonempty
            (ClassifiedThreeLawTranslationCertificate constants shape
              insertConstant valueChangeConstant
              n
              (comparison.cost accesses)
              (comparison.maxHeight accesses)
              initial accesses)

/--
Forgetting the explicit slot classification recovers the numerical
three-law residue.
-/
theorem threeLawTranslationHypothesis_of_classified
    {comparison : ComparisonProfile} {shape : Interface.Shape}
    (classified :
      ClassifiedThreeLawTranslationHypothesis comparison shape) :
    ThreeLawTranslationHypothesis comparison shape := by
  intro insertConstant valueChangeConstant
    insertPositive valueChangePositive
  obtain ⟨constants, certificates⟩ :=
    classified insertConstant valueChangeConstant
      insertPositive valueChangePositive
  refine ⟨constants, ?_⟩
  intro n nPositive initial accesses
  obtain ⟨certificate⟩ :=
    certificates n nPositive initial accesses
  exact ⟨certificate.toThreeLaw⟩

/--
The canonical take/drop construction lifts every uniform three-law family to
the checked list-level classification family.
-/
theorem classifiedThreeLawTranslationHypothesis_of_threeLaw
    {comparison : ComparisonProfile} {shape : Interface.Shape}
    (threeLaw :
      ThreeLawTranslationHypothesis comparison shape) :
    ClassifiedThreeLawTranslationHypothesis comparison shape := by
  intro insertConstant valueChangeConstant
    insertPositive valueChangePositive
  obtain ⟨constants, certificates⟩ :=
    threeLaw insertConstant valueChangeConstant
      insertPositive valueChangePositive
  refine ⟨constants, ?_⟩
  intro n nPositive initial accesses
  rw [nonempty_classifiedThreeLawTranslationCertificate_iff]
  exact certificates n nPositive initial accesses

/--
At the current list-token abstraction, classified and numerical three-law
hypotheses are propositionally equivalent.
-/
theorem classifiedThreeLawTranslationHypothesis_iff
    {comparison : ComparisonProfile} {shape : Interface.Shape} :
    ClassifiedThreeLawTranslationHypothesis comparison shape ↔
      ThreeLawTranslationHypothesis comparison shape :=
  ⟨threeLawTranslationHypothesis_of_classified,
    classifiedThreeLawTranslationHypothesis_of_threeLaw⟩

/--
The proof-relevant classified family is also equivalent to the original
seven-field translation family.
-/
theorem classifiedThreeLawTranslationHypothesis_iff_concrete
    {comparison : ComparisonProfile} {shape : Interface.Shape} :
    ClassifiedThreeLawTranslationHypothesis comparison shape ↔
      ConcreteTranslationHypothesis comparison shape :=
  classifiedThreeLawTranslationHypothesis_iff.trans
    threeLawTranslationHypothesis_iff

/--
Direct `Accounting.Hypothesis` endpoint from the checked pairing
classification residue.
-/
theorem hypothesis_of_classifiedThreeLawTranslation
    (optCost : {n : ℕ} → List (Fin n) → ℕ)
    {comparison : ComparisonProfile}
    (shape : Interface.Shape)
    (requests : RequestCostDominates comparison)
    (translation :
      ClassifiedThreeLawTranslationHypothesis comparison shape) :
    Hypothesis (concreteSplayCostModel optCost) comparison :=
  hypothesis_of_threeLawTranslation optCost shape requests
    (threeLawTranslationHypothesis_of_classified translation)

/--
A chosen normal-form realization supplies request-cost dominance
automatically.
-/
theorem hypothesis_of_normalFormClassifiedThreeLawTranslation
    (optCost : {n : ℕ} → List (Fin n) → ℕ)
    (realization :
      Assumptions.NormalForm.Realization
        (concreteSplayCostModel optCost))
    (shape : Interface.Shape)
    (translation :
      ClassifiedThreeLawTranslationHypothesis
        realization.comparisonProfile shape) :
    Hypothesis
      (concreteSplayCostModel optCost)
      realization.comparisonProfile :=
  hypothesis_of_classifiedThreeLawTranslation optCost shape
    (requestCostDominates_of_normalFormRealization realization)
    translation

/--
Direct target endpoint from reusable normal-form data and the checked pairing
classification residue.
-/
theorem targetBound_of_normalFormRealization_and_classifiedTranslation
    (optCost : {n : ℕ} → List (Fin n) → ℕ)
    (realization :
      Assumptions.NormalForm.Realization
        (concreteSplayCostModel optCost))
    (shape : Interface.Shape)
    (translation :
      ClassifiedThreeLawTranslationHypothesis
        realization.comparisonProfile shape) :
    TargetBound (concreteSplayCostModel optCost) :=
  Assumptions.NormalForm.targetBound_of_normalForm_and_core
    (concreteSplayCostModel optCost) realization
    (hypothesis_of_normalFormClassifiedThreeLawTranslation
      optCost realization shape translation).hasCoreAnalysisBound

/--
Direct conditional endpoint from the normal-form hypothesis and the checked
pairing classification residue.
-/
theorem targetBound_of_normalForm_and_classifiedTranslation
    (optCost : {n : ℕ} → List (Fin n) → ℕ)
    (normalForm :
      Assumptions.NormalForm.Hypothesis
        (concreteSplayCostModel optCost))
    (shape : Interface.Shape)
    (translation :
      ClassifiedThreeLawTranslationHypothesis
        normalForm.realize.comparisonProfile shape) :
    TargetBound (concreteSplayCostModel optCost) :=
  targetBound_of_normalFormRealization_and_classifiedTranslation
    optCost normalForm.realize shape translation

end Splay.Accounting
