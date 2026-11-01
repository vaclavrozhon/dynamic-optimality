import Splay.Accounting.PairingHeapChildEndpoints
import Splay.Interface.BlockCount
import Splay.Interface.RootLineagePhase

namespace Splay.Accounting

open Splay.Lazy

/--
The deterministic root-label array immediately before one operation position.

Only visible interface operations advance the label array.  In particular,
when this definition is used with `Lazy.eraseOperations`, arbitrary silent
rich events do not affect the selected persistent lineage.
-/
def rootLabelsBefore {n : ℕ}
    (initialLabels : Interface.RootLabels)
    (operations : List (Interface.Operation n)) (operationIndex : ℕ) :
    Interface.RootLabels :=
  (operations.take operationIndex).foldl
    Interface.RootLabels.after initialLabels

@[simp]
theorem rootLabelsBefore_zero {n : ℕ}
    (initialLabels : Interface.RootLabels)
    (operations : List (Interface.Operation n)) :
    rootLabelsBefore initialLabels operations 0 = initialLabels :=
  rfl

@[simp]
theorem rootLabelsBefore_cons_succ {n : ℕ}
    (initialLabels : Interface.RootLabels)
    (head : Interface.Operation n)
    (tail : List (Interface.Operation n)) (operationIndex : ℕ) :
    rootLabelsBefore initialLabels (head :: tail) operationIndex.succ =
      rootLabelsBefore
        (Interface.RootLabels.after initialLabels head)
        tail operationIndex := by
  simp [rootLabelsBefore]

namespace RichVisibleStepAt

/--
The exact visible pre-state inherits aligned persistent-root labels and the
full root-lineage phase invariant from the rich trace's initial state.

The label array is not an existential annotation: it is the deterministic
fold over the actual erased-operation prefix selected by
`operationIndex`.  This is the time-fixing step needed by boundary-pairing
semantics.
-/
theorem rootLineagePhase_before
    {n : ℕ} {params : Interface.Parameters}
    {initial final before after : Lazy.State n}
    {events : List (Lazy.Event n)}
    {trace : Lazy.Trace params initial events final}
    {operationIndex eventIndex : ℕ}
    {operation : Interface.Operation n}
    (occurrence :
      Lazy.Trace.VisibleStepAt trace operationIndex eventIndex
        before operation after)
    (initialLabels : Interface.RootLabels)
    (initialAligned :
      initialLabels.length = initial.toInterface.blocks.length)
    (initialPhase :
      Interface.RootLineagePhase initial.toInterface initialLabels) :
    let labels :=
      rootLabelsBefore initialLabels
        (Lazy.eraseOperations events) operationIndex
    labels.length = before.toInterface.blocks.length ∧
      Interface.RootLineagePhase before.toInterface labels := by
  induction occurrence generalizing initialLabels with
  | head step tail =>
      exact ⟨initialAligned, initialPhase⟩
  | @visibleTail initial middle final headOperation events
      headStep tailTrace operationIndex eventIndex before after
      operation occurrence ih =>
      have interfaceStep :
          Interface.Step params initial.toInterface headOperation
            middle.toInterface :=
        headStep.interfaceStep_of_operation
      have middleAligned :
          (Interface.RootLabels.after initialLabels headOperation).length =
            middle.toInterface.blocks.length :=
        (Interface.HistoryStep.mk interfaceStep rfl).labels_length
          initialAligned
      have middlePhase :
          Interface.RootLineagePhase middle.toInterface
            (Interface.RootLabels.after initialLabels headOperation) :=
        initialPhase.after_step initialAligned interfaceStep
      simpa [Lazy.eraseOperations, Lazy.Event.operations] using
        ih (Interface.RootLabels.after initialLabels headOperation)
          middleAligned middlePhase
  | @silentTail initial middle final events headStep tailTrace
      operationIndex eventIndex before after operation occurrence ih =>
      have projectionEq :
          initial.toInterface = middle.toInterface :=
        headStep.projection_eq_of_silent
      have middleAligned :
          initialLabels.length = middle.toInterface.blocks.length := by
        rw [← projectionEq]
        exact initialAligned
      have middlePhase :
          Interface.RootLineagePhase middle.toInterface initialLabels := by
        rw [← projectionEq]
        exact initialPhase
      simpa [Lazy.eraseOperations, Lazy.Event.operations] using
        ih initialLabels middleAligned middlePhase

/--
For traces starting at the genuine empty interface state, no caller-supplied
labels or lineage invariant are required.
-/
theorem rootLineagePhase_before_of_initial
    {n : ℕ} {params : Interface.Parameters}
    {initial final before after : Lazy.State n}
    {events : List (Lazy.Event n)}
    {trace : Lazy.Trace params initial events final}
    {operationIndex eventIndex : ℕ}
    {operation : Interface.Operation n}
    (occurrence :
      Lazy.Trace.VisibleStepAt trace operationIndex eventIndex
        before operation after)
    (initialState : initial.toInterface.Initial params) :
    let labels :=
      rootLabelsBefore []
        (Lazy.eraseOperations events) operationIndex
    labels.length = before.toInterface.blocks.length ∧
      Interface.RootLineagePhase before.toInterface labels := by
  apply rootLineagePhase_before occurrence []
  · simp [initialState.2]
  · exact Interface.RootLineagePhase.initial initialState

/-- A visible pre-state cannot have more persistent block IDs than the final
state of the same rich trace. -/
theorem before_blocks_length_le_final
    {n : ℕ} {params : Interface.Parameters}
    {initial final before after : Lazy.State n}
    {events : List (Lazy.Event n)}
    {trace : Lazy.Trace params initial events final}
    {operationIndex eventIndex : ℕ}
    {operation : Interface.Operation n}
    (occurrence :
      Lazy.Trace.VisibleStepAt trace operationIndex eventIndex
        before operation after) :
    before.blocks.length ≤ final.blocks.length := by
  induction occurrence with
  | head step tail =>
      have count := (Lazy.Trace.cons step tail).toInterface.blocks_length_eq
      simp only [Lazy.State.toInterface, List.length_map] at count
      omega
  | visibleTail headStep tailTrace occurrence ih =>
      exact ih
  | silentTail headStep tailTrace occurrence ih =>
      exact ih

end RichVisibleStepAt

namespace BoundaryPairingMove

/--
The persistent source lineage frozen at the exact rich pre-state of a
boundary delete.

`root` is the stable ID introduced by the lineage's original `create`;
splitting the source only changes `source`, never `root`.  Both the current
source block and the original root block are looked up in the very same
time-fixed state.
-/
structure PersistentSourceAt
    {n : ℕ} {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}
    {trace : Lazy.Trace params initial events final}
    (initialLabels : Interface.RootLabels)
    (move : BoundaryPairingMove trace) : Type where
  labelsAligned :
    (rootLabelsBefore initialLabels
      (Lazy.eraseOperations events)
      move.deleteOperationIndex).length =
        move.deleteBefore.toInterface.blocks.length
  phase :
    Interface.RootLineagePhase move.deleteBefore.toInterface
      (rootLabelsBefore initialLabels
        (Lazy.eraseOperations events)
        move.deleteOperationIndex)
  root : Interface.RootId
  sourceBlock : Interface.Block n
  rootBlock : Interface.Block n
  sourceFound :
    move.deleteBefore.toInterface.block? move.source =
      some sourceBlock
  sourceRootFound :
    Interface.RootLabels.root?
        (rootLabelsBefore initialLabels
          (Lazy.eraseOperations events)
          move.deleteOperationIndex)
        move.source =
      some root
  rootFound :
    move.deleteBefore.toInterface.block? root = some rootBlock
  sourceShrinking : sourceBlock.mode = .shrinking
  rootShrinking : rootBlock.mode = .shrinking
  loserMem : move.loser ∈ sourceBlock.elements

/--
Every chronological boundary move automatically has a time-fixed persistent
source snapshot once the initial root labels are aligned and satisfy the
lineage phase invariant.
-/
theorem persistentSourceAt_nonempty
    {n : ℕ} {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}
    {trace : Lazy.Trace params initial events final}
    (move : BoundaryPairingMove trace)
    (initialLabels : Interface.RootLabels)
    (initialAligned :
      initialLabels.length = initial.toInterface.blocks.length)
    (initialPhase :
      Interface.RootLineagePhase initial.toInterface initialLabels) :
    Nonempty (PersistentSourceAt initialLabels move) := by
  let labels :=
    rootLabelsBefore initialLabels
      (Lazy.eraseOperations events) move.deleteOperationIndex
  have phaseFacts :=
    RichVisibleStepAt.rootLineagePhase_before move.deleteAt initialLabels
      initialAligned initialPhase
  have labelsAligned : labels.length =
      move.deleteBefore.toInterface.blocks.length :=
    phaseFacts.1
  have phase :
      Interface.RootLineagePhase move.deleteBefore.toInterface labels :=
    phaseFacts.2
  obtain ⟨sourceBlock, sourceFound, sourceShrinking, loserMem⟩ :=
    move.delete_source_valid
  obtain ⟨root, sourceRootFound⟩ :=
    Interface.root_exists_of_aligned_block_found
      labelsAligned sourceFound
  obtain ⟨rootBlock, rootFound⟩ :=
    phase.rootsRealized move.source root sourceRootFound
  have rootShrinking : rootBlock.mode = .shrinking := by
    cases rootMode : rootBlock.mode with
    | shrinking =>
        rfl
    | growing =>
        exfalso
        have sourceNonempty : sourceBlock.elements ≠ [] := by
          intro empty
          rw [empty] at loserMem
          simp at loserMem
        have sourceEqRoot :
            move.source = root :=
          phase.growingOnly root rootBlock rootFound rootMode
            move.source sourceBlock sourceFound sourceRootFound
              sourceNonempty
        subst root
        rw [sourceFound] at rootFound
        have blockEq : sourceBlock = rootBlock :=
          Option.some.inj rootFound
        rw [blockEq, rootMode] at sourceShrinking
        contradiction
  exact
    ⟨{ labelsAligned := labelsAligned
       phase := phase
       root := root
       sourceBlock := sourceBlock
       rootBlock := rootBlock
       sourceFound := sourceFound
       sourceRootFound := sourceRootFound
       rootFound := rootFound
       sourceShrinking := sourceShrinking
       rootShrinking := rootShrinking
       loserMem := loserMem }⟩

/-- Canonical choice of the automatic persistent-source snapshot. -/
noncomputable def persistentSourceAt
    {n : ℕ} {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}
    {trace : Lazy.Trace params initial events final}
    (move : BoundaryPairingMove trace)
    (initialLabels : Interface.RootLabels)
    (initialAligned :
      initialLabels.length = initial.toInterface.blocks.length)
    (initialPhase :
      Interface.RootLineagePhase initial.toInterface initialLabels) :
    PersistentSourceAt initialLabels move :=
  Classical.choice
    (persistentSourceAt_nonempty move initialLabels
      initialAligned initialPhase)

/--
The persistent root selected at delete time is still an in-range stable block
identifier at the final endpoint of the same rich trace.
-/
theorem PersistentSourceAt.root_lt_final
    {n : ℕ} {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}
    {trace : Lazy.Trace params initial events final}
    {initialLabels : Interface.RootLabels}
    {move : BoundaryPairingMove trace}
    (snapshot : PersistentSourceAt initialLabels move) :
    snapshot.root < final.blocks.length := by
  have rootLt :
      snapshot.root < move.deleteBefore.toInterface.blocks.length :=
    (List.getElem?_eq_some_iff.mp snapshot.rootFound).1
  have beforeLe :=
    RichVisibleStepAt.before_blocks_length_le_final move.deleteAt
  have rootLtRich :
      snapshot.root < move.deleteBefore.blocks.length := by
    simpa [Lazy.State.toInterface] using rootLt
  exact rootLtRich.trans_le beforeLe

/--
The manuscript's unimportant case at one exact time: the persistent lineage
is geometrically unbroken there and its current source block is at least the
chosen cutoff.

The rich model deliberately does not yet define cross-side "brokenness", so
that predicate is an explicit semantic parameter.  Size and persistent-root
identity are no longer parameters.
-/
def PersistentSourceAt.Unimportant
    {n : ℕ} {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}
    {trace : Lazy.Trace params initial events final}
    {initialLabels : Interface.RootLabels}
    {move : BoundaryPairingMove trace}
    (snapshot : PersistentSourceAt initialLabels move)
    (unbrokenAt : Lazy.State n → Interface.RootId → Prop)
    (cutoff : ℕ) : Prop :=
  unbrokenAt move.deleteBefore snapshot.root ∧
    cutoff ≤ snapshot.sourceBlock.elements.length

/-- Important is exactly the complement of the time-fixed unimportant case. -/
def PersistentSourceAt.Important
    {n : ℕ} {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}
    {trace : Lazy.Trace params initial events final}
    {initialLabels : Interface.RootLabels}
    {move : BoundaryPairingMove trace}
    (snapshot : PersistentSourceAt initialLabels move)
    (unbrokenAt : Lazy.State n → Interface.RootId → Prop)
    (cutoff : ℕ) : Prop :=
  ¬ snapshot.Unimportant unbrokenAt cutoff

end BoundaryPairingMove

namespace BoundaryPassPairingClassification

variable
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : Tree.BST 0 n}
    {sequence : Tree.BST.SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}

/--
Canonical persistent-source snapshot for any boundary move in an initialized
classification.  No importance label is used in its construction.
-/
noncomputable def persistentSourceAt
    (classification :
      BoundaryPassPairingClassification transcript params
        initial final events)
    (move : BoundaryPairingMove classification.trace) :
    BoundaryPairingMove.PersistentSourceAt [] move :=
  move.persistentSourceAt []
    (by
      simpa [Lazy.State.toInterface] using
        congrArg List.length
          classification.passClassification.initialState.2.symm)
    (Interface.RootLineagePhase.initial
      classification.passClassification.initialState)

/-- Important moves receive their persistent lineage snapshot automatically. -/
theorem importantMove_persistentSourceAt
    (classification :
      BoundaryPassPairingClassification transcript params
        initial final events)
    (move : BoundaryPairingMove classification.trace)
    (_member : move ∈ classification.importantMoves) :
    Nonempty (BoundaryPairingMove.PersistentSourceAt [] move) :=
  ⟨classification.persistentSourceAt move⟩

/-- Unimportant moves receive the same automatic lineage data. -/
theorem unimportantMove_persistentSourceAt
    (classification :
      BoundaryPassPairingClassification transcript params
        initial final events)
    (move : BoundaryPairingMove classification.trace)
    (_member : move ∈ classification.unimportantMoves) :
    Nonempty (BoundaryPairingMove.PersistentSourceAt [] move) :=
  ⟨classification.persistentSourceAt move⟩

/-- The final-state slot occupied by a boundary move's persistent root. -/
noncomputable def persistentRootSlot
    (classification :
      BoundaryPassPairingClassification transcript params
        initial final events)
    (move : BoundaryPairingMove classification.trace) :
    Fin final.blocks.length :=
  let snapshot := classification.persistentSourceAt move
  ⟨snapshot.root, snapshot.root_lt_final⟩

end BoundaryPassPairingClassification

namespace PassPairingClassification

/--
Swap the two semantically uninterpreted boundary labels while preserving the
trace, actual pass charges, and complete transcript partition.
-/
def swapBoundaryLabels
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : Tree.BST 0 n}
    {sequence : Tree.BST.SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {params : Interface.Parameters}
    {initial final : Interface.State n}
    {operations : List (Interface.Operation n)}
    (classification :
      PassPairingClassification transcript params
        initial final operations) :
    PassPairingClassification transcript params
      initial final operations where
  initialState := classification.initialState
  trace := classification.trace
  finalLabels := classification.finalLabels
  activityOccurrences := classification.activityOccurrences
  activityHistory := classification.activityHistory
  importantSlots := classification.unimportantSlots
  unimportantSlots := classification.importantSlots
  internalCharges := classification.internalCharges
  slots_partition := by
    have swapped :
        (classification.unimportantSlots ++
            classification.importantSlots ++
              classification.internalCharges.map Prod.fst).Perm
          (classification.importantSlots ++
            classification.unimportantSlots ++
              classification.internalCharges.map Prod.fst) := by
      simpa only [List.append_assoc] using
        (List.Perm.append_right
          (classification.internalCharges.map Prod.fst)
          (List.perm_append_comm :
            (classification.unimportantSlots ++
                classification.importantSlots).Perm
              (classification.importantSlots ++
                classification.unimportantSlots)))
    exact swapped.trans classification.slots_partition
  internalActivityOrdinals_nodup :=
    classification.internalActivityOrdinals_nodup

end PassPairingClassification

namespace BoundaryPassPairingClassification

/--
The current boundary-classification axioms are label-symmetric: important and
unimportant moves may be exchanged without changing any trace, move, slot,
geometry, or automatic persistent-lineage fact.
-/
def swapBoundaryLabels
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : Tree.BST 0 n}
    {sequence : Tree.BST.SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}
    (classification :
      BoundaryPassPairingClassification transcript params
        initial final events) :
    BoundaryPassPairingClassification transcript params
      initial final events where
  trace := classification.trace
  passClassification :=
    classification.passClassification.swapBoundaryLabels
  importantMoves := classification.unimportantMoves
  unimportantMoves := classification.importantMoves
  importantSlots_eq := classification.unimportantSlots_eq
  unimportantSlots_eq := classification.importantSlots_eq

@[simp]
theorem swapBoundaryLabels_important_length
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : Tree.BST 0 n}
    {sequence : Tree.BST.SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}
    (classification :
      BoundaryPassPairingClassification transcript params
        initial final events) :
    classification.swapBoundaryLabels.importantMoves.length =
      classification.unimportantMoves.length :=
  rfl

@[simp]
theorem swapBoundaryLabels_unimportant_length
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : Tree.BST 0 n}
    {sequence : Tree.BST.SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}
    (classification :
      BoundaryPassPairingClassification transcript params
        initial final events) :
    classification.swapBoundaryLabels.unimportantMoves.length =
      classification.importantMoves.length :=
  rfl

/--
Formal specification boundary: if the opposite class is larger than a proposed
important bound, the equally valid swapped classification refutes that bound.
-/
theorem swapBoundaryLabels_refutes_important_bound
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : Tree.BST 0 n}
    {sequence : Tree.BST.SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}
    (classification :
      BoundaryPassPairingClassification transcript params
        initial final events)
    {bound : ℕ}
    (tooLarge : bound < classification.unimportantMoves.length) :
    ¬ classification.swapBoundaryLabels.importantMoves.length ≤ bound := by
  simpa using Nat.not_le_of_gt tooLarge

/-- Symmetric refutation for any proposed unimportant bound. -/
theorem swapBoundaryLabels_refutes_unimportant_bound
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : Tree.BST 0 n}
    {sequence : Tree.BST.SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}
    (classification :
      BoundaryPassPairingClassification transcript params
        initial final events)
    {bound : ℕ}
    (tooLarge : bound < classification.importantMoves.length) :
    ¬ classification.swapBoundaryLabels.unimportantMoves.length ≤ bound := by
  simpa using Nat.not_le_of_gt tooLarge

end BoundaryPassPairingClassification

end Splay.Accounting
