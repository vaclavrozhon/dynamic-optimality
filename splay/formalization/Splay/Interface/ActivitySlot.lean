import Splay.Interface.Activity
import Splay.Interface.TraceOccurrence
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.TakeDrop

namespace Splay.Interface

/-- Activity contributed strictly before one operation-list position. -/
def activityBefore {n : ℕ} (operations : List (Operation n))
    (index : Fin operations.length) : ℕ :=
  totalActivity (operations.take index.val)

/--
One proof-relevant pairing position in an exact interface operation list.

Besides the chronological operation and matching positions, the record stores
their canonical flattened activity ordinal.  The equality is important:
`activityOrdinal` is not a free accounting token that can be assigned to an
unrelated pass tuple.
-/
structure ActivitySlot {n : ℕ} (operations : List (Operation n)) where
  operationIndex : Fin operations.length
  source : BlockId
  matching : List (Pairing n)
  operation_eq :
    operations.get operationIndex = .pass source matching
  pairingIndex : Fin matching.length
  activityOrdinal : Fin (totalActivity operations)
  activityOrdinal_eq :
    activityOrdinal.val =
      activityBefore operations operationIndex + pairingIndex.val

namespace ActivitySlot

/--
At an actual pass position, the activity before the operation plus the size
of that matching fits inside total activity.
-/
theorem activityBefore_add_matching_le
    {n : ℕ} {operations : List (Operation n)}
    (operationIndex : Fin operations.length)
    (source : BlockId) (matching : List (Pairing n))
    (operation_eq :
      operations.get operationIndex = .pass source matching) :
    activityBefore operations operationIndex + matching.length ≤
      totalActivity operations := by
  have dropEq :
      operations.drop operationIndex.val =
        .pass source matching ::
          operations.drop (operationIndex.val + 1) := by
    rw [← operation_eq]
    exact List.cons_get_drop_succ.symm
  have dropActivity :
      matching.length ≤
        totalActivity (operations.drop operationIndex.val) := by
    rw [dropEq]
    simp [totalActivity, Operation.activity]
  have splitActivity :
      totalActivity operations =
        totalActivity (operations.take operationIndex.val) +
          totalActivity (operations.drop operationIndex.val) := by
    conv_lhs =>
      rw [← operations.take_append_drop operationIndex.val]
    simp [totalActivity]
  calc
    activityBefore operations operationIndex + matching.length =
        totalActivity (operations.take operationIndex.val) +
          matching.length := rfl
    _ ≤ totalActivity (operations.take operationIndex.val) +
          totalActivity (operations.drop operationIndex.val) :=
      Nat.add_le_add_left dropActivity _
    _ = totalActivity operations := splitActivity.symm

/-- Construct the canonical flattened activity slot from exact pass indices. -/
def ofPass
    {n : ℕ} {operations : List (Operation n)}
    (operationIndex : Fin operations.length)
    (source : BlockId) (matching : List (Pairing n))
    (operation_eq :
      operations.get operationIndex = .pass source matching)
    (pairingIndex : Fin matching.length) :
    ActivitySlot operations := by
  let ordinalValue :=
    activityBefore operations operationIndex + pairingIndex.val
  have ordinalBound :
      ordinalValue < totalActivity operations := by
    have matchingBound :=
      activityBefore_add_matching_le
        operationIndex source matching operation_eq
    dsimp only [ordinalValue]
    omega
  exact
    { operationIndex := operationIndex
      source := source
      matching := matching
      operation_eq := operation_eq
      pairingIndex := pairingIndex
      activityOrdinal := ⟨ordinalValue, ordinalBound⟩
      activityOrdinal_eq := rfl }

/-- The concrete pairing tuple carried by this unit of pass activity. -/
def pairing {n : ℕ} {operations : List (Operation n)}
    (slot : ActivitySlot operations) : Pairing n :=
  slot.matching.get slot.pairingIndex

/-- The selected tuple is genuinely a member of its exact pass matching. -/
theorem pairing_mem_matching {n : ℕ}
    {operations : List (Operation n)}
    (slot : ActivitySlot operations) :
    slot.pairing ∈ slot.matching :=
  List.get_mem slot.matching slot.pairingIndex

/--
The pass named by an activity slot occurs with actual endpoints in any trace
of the operation list.
-/
theorem exists_stepAt
    {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (slot : ActivitySlot operations)
    (trace : Trace params initial operations final) :
    ∃ before after,
      Trace.StepAt trace slot.operationIndex.val before
        (.pass slot.source slot.matching) after := by
  obtain ⟨before, operation, after, occurrence⟩ :=
    trace.exists_stepAt slot.operationIndex
  have indexEq :
      (⟨slot.operationIndex.val, occurrence.index_lt⟩ :
        Fin operations.length) =
        slot.operationIndex :=
    Fin.ext rfl
  have operationEq :
      operation = .pass slot.source slot.matching := by
    rw [← occurrence.operation_eq_get, indexEq]
    exact slot.operation_eq
  subst operation
  exact ⟨before, after, occurrence⟩

/--
An activity slot in a legal interface trace selects a genuinely valid pairing
tuple in the exact pre-state of its pass.

This is stronger than list membership: it recovers the source block looked up
by the pass effect and discharges all adjacency, value-order, distinct-block,
and growing-destination conditions bundled in `PairingValid`.
-/
theorem exists_pairingValid
    {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (slot : ActivitySlot operations)
    (trace : Trace params initial operations final) :
    ∃ before after sourceBlock,
      Trace.StepAt trace slot.operationIndex.val before
          (.pass slot.source slot.matching) after ∧
        before.block? slot.source = some sourceBlock ∧
        PairingValid before slot.source sourceBlock slot.pairing := by
  obtain ⟨before, after, occurrence⟩ := slot.exists_stepAt trace
  have legalStep := occurrence.step
  cases legalStep.2.1 with
  | pass sourceFound matchingValid _ _ =>
      refine
        ⟨before, after, _, occurrence, sourceFound, ?_⟩
      exact matchingValid.2.2.2.1
        slot.pairing slot.pairing_mem_matching

/--
Two semantic slots with equal flattened ordinals and equal operation
positions necessarily have equal positions inside the matching.
-/
theorem pairingIndex_val_eq_of_ordinal_eq
    {n : ℕ} {operations : List (Operation n)}
    {first second : ActivitySlot operations}
    (operationIndex_eq :
      first.operationIndex = second.operationIndex)
    (ordinal_eq :
      first.activityOrdinal = second.activityOrdinal) :
    first.pairingIndex.val = second.pairingIndex.val := by
  have values :=
    congrArg Fin.val ordinal_eq
  rw [first.activityOrdinal_eq, second.activityOrdinal_eq,
    operationIndex_eq] at values
  omega

/--
Distinct flattened activity ordinals are enough to charge actual pass tuples
injectively into `totalActivity operations`.
-/
theorem length_le_totalActivity_of_ordinals_nodup
    {n : ℕ} {operations : List (Operation n)}
    (slots : List (ActivitySlot operations))
    (nodup : (slots.map activityOrdinal).Nodup) :
    slots.length ≤ totalActivity operations := by
  have bound := nodup.length_le_card
  simpa only [List.length_map, Fintype.card_fin] using bound

end ActivitySlot

end Splay.Interface
