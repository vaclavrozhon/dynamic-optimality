import Splay.Accounting.PairingClassification
import Splay.Interface.ActivitySlot

namespace Splay.Accounting

open Splay.Tree.BST

/--
A pairing classification whose internal charges point to actual pass tuples.

Compared with `PairingClassification`, an internal target is no longer merely
a position in an activity annotation of the right length.  It names:

* the chronological operation position;
* the exact `pass` source and matching at that position; and
* the exact tuple position inside that matching.

Its flattened ordinal is definitionally tied to those two positions by
`Interface.ActivitySlot.activityOrdinal_eq`.  Important and unimportant
boundary slots are intentionally unchanged here; connecting those slots to
delete/insert endpoints is the separate geometric translation obligation.
-/
structure PassPairingClassification
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
    List (PairingSlot × Interface.ActivitySlot operations)

  slots_partition :
    (importantSlots ++ unimportantSlots ++
        internalCharges.map Prod.fst).Perm
      (firstPairings kinds ++ secondPairings kinds)

  /--
  No concrete pass tuple pays twice.  The canonical flattened ordinals range
  over exactly `Interface.totalActivity operations`.
  -/
  internalActivityOrdinals_nodup :
    (internalCharges.map fun charge =>
      charge.2.activityOrdinal).Nodup

namespace PassPairingClassification

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

/-- The actual pass tuple targeted by every internal transcript slot. -/
def internalPairings
    (classification :
      PassPairingClassification transcript params
        initial final operations) :
    List (PairingSlot × Interface.Pairing n) :=
  classification.internalCharges.map fun charge =>
    (charge.1, charge.2.pairing)

/--
Every internal charge names a tuple that satisfies `PairingValid` in the
actual pre-state of its pass in the classification trace.
-/
theorem internalCharge_pairingValid
    (classification :
      PassPairingClassification transcript params
        initial final operations)
    (charge : PairingSlot × Interface.ActivitySlot operations)
    (_member : charge ∈ classification.internalCharges) :
    ∃ before after sourceBlock,
      Interface.Trace.StepAt classification.trace
          charge.2.operationIndex.val before
          (.pass charge.2.source charge.2.matching) after ∧
        before.block? charge.2.source = some sourceBlock ∧
        Interface.PairingValid before charge.2.source sourceBlock
          charge.2.pairing := by
  exact charge.2.exists_pairingValid classification.trace

/--
Every actual internal charge is bounded by exact pass activity, independently
of the auxiliary activity-history annotation.
-/
theorem internalCount_le_totalActivity
    (classification :
      PassPairingClassification transcript params
        initial final operations) :
    classification.internalCharges.length ≤
      Interface.totalActivity operations := by
  have bound :=
    Interface.ActivitySlot.length_le_totalActivity_of_ordinals_nodup
      (classification.internalCharges.map Prod.snd)
      (by
        simpa only [List.map_map, Function.comp_def] using
          classification.internalActivityOrdinals_nodup)
  simpa only [List.length_map] using bound

/--
The partition into important, unimportant, and actual-pass charges still
contains exactly the two slots of every concrete zig-zig.
-/
theorem classifiedCounts_eq
    (classification :
      PassPairingClassification transcript params
        initial final operations) :
    classification.importantSlots.length +
        classification.unimportantSlots.length +
        classification.internalCharges.length =
      2 * zigZig := by
  have partitionLength := classification.slots_partition.length_eq
  have slotsLength := total_pairingSlots transcript
  simp only [List.length_append, List.length_map] at partitionLength
  omega

/--
Actual pass-tuple charges imply the zig-zig pairing inequality directly.
-/
theorem zigZig_pairings
    (classification :
      PassPairingClassification transcript params
        initial final operations) :
    2 * zigZig ≤
      classification.importantSlots.length +
        classification.unimportantSlots.length +
        Interface.totalActivity operations := by
  have internalBound :=
    classification.internalCount_le_totalActivity
  have counts := classification.classifiedCounts_eq
  omega

/--
Forget exact pass-tuple coordinates and recover the older proof-indexed
activity-position classification.

The cast is justified by the checked activity-history identity
`activityOccurrences.length = totalActivity operations`; injectivity is
preserved because `Fin.cast` is injective.
-/
noncomputable def toPairingClassification
    (classification :
      PassPairingClassification transcript params
        initial final operations) :
    PairingClassification transcript params initial final operations := by
  let lengthEq :
      Interface.totalActivity operations =
        classification.activityOccurrences.length :=
    classification.activityHistory.occurrences_length.symm
  let occurrenceIndex :
      Interface.ActivitySlot operations →
        Fin classification.activityOccurrences.length :=
    fun slot => Fin.cast lengthEq slot.activityOrdinal
  refine
    { initialState := classification.initialState
      trace := classification.trace
      finalLabels := classification.finalLabels
      activityOccurrences := classification.activityOccurrences
      activityHistory := classification.activityHistory
      importantSlots := classification.importantSlots
      unimportantSlots := classification.unimportantSlots
      internalCharges :=
        classification.internalCharges.map fun charge =>
          (charge.1, occurrenceIndex charge.2)
      slots_partition := ?_
      internalActivitySlots_nodup := ?_ }
  · simpa only [List.map_map, Function.comp_def] using
      classification.slots_partition
  · have castNodup :=
      classification.internalActivityOrdinals_nodup.map
        (Fin.cast_injective lengthEq)
    simpa only [List.map_map, Function.comp_def, occurrenceIndex] using
      castNodup

end PassPairingClassification

end Splay.Accounting
