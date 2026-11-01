import Splay.Accounting.PassPairingClassification
import Splay.Lazy.VisibleTraceOccurrence

namespace Splay.Accounting

/--
The concrete delete/insert implementation of one boundary pairing in an
actual rich trace.

The record fixes both visible-operation positions and both rich-event
positions, so silent structural events may occur between the endpoints
without losing chronology.  The destination block is explicitly required to
have the pairing winner as creator.

This still does not infer `winner` and `loser` from the abstract transcript
slot; that is the remaining tree-geometry map.
-/
structure BoundaryPairingMove
    {n : ℕ} {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}
    (trace : Lazy.Trace params initial events final) where
  slot : PairingSlot
  winner : Interface.Element n
  loser : Interface.Element n

  source : Interface.BlockId
  deleteOperationIndex : ℕ
  deleteEventIndex : ℕ
  deleteBefore : Lazy.State n
  deleteAfter : Lazy.State n
  deleteAt :
    Lazy.Trace.VisibleStepAt trace
      deleteOperationIndex deleteEventIndex
      deleteBefore (.delete source loser) deleteAfter

  destination : Interface.BlockId
  insertOperationIndex : ℕ
  insertEventIndex : ℕ
  insertBefore : Lazy.State n
  insertAfter : Lazy.State n
  insertAt :
    Lazy.Trace.VisibleStepAt trace
      insertOperationIndex insertEventIndex
      insertBefore (.insert destination loser) insertAfter

  delete_before_insert :
    deleteEventIndex < insertEventIndex

  destinationBlock : Interface.Block n
  destinationFound :
    insertBefore.toInterface.block? destination =
      some destinationBlock
  destinationCreator :
    destinationBlock.creator = winner

namespace BoundaryPairingMove

/--
The selected delete has an actual shrinking source containing the loser.
-/
theorem delete_source_valid
    {n : ℕ} {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}
    {trace : Lazy.Trace params initial events final}
    (move : BoundaryPairingMove trace) :
    ∃ sourceBlock,
      move.deleteBefore.toInterface.block? move.source =
          some sourceBlock ∧
        sourceBlock.mode = .shrinking ∧
        move.loser ∈ sourceBlock.elements := by
  have step := move.deleteAt.toInterface
  cases step.2.1 with
  | delete found shrinking present _ _ =>
      exact ⟨_, found, shrinking, present⟩

/--
The selected insert uses the recorded winner-created growing destination,
with the interface's exact unassigned and value-order preconditions.
-/
theorem insert_destination_valid
    {n : ℕ} {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}
    {trace : Lazy.Trace params initial events final}
    (move : BoundaryPairingMove trace) :
    move.destinationBlock.mode = .growing ∧
      move.destinationBlock.creator = move.winner ∧
      move.loser ∉ move.insertBefore.toInterface.allElements ∧
      move.insertBefore.toInterface.value move.winner + 1 ≤
        move.insertBefore.toInterface.value move.loser := by
  have step := move.insertAt.toInterface
  cases step.2.1 with
  | insert found growing unassigned valueOrder _ _ =>
      have blockEq : ‹_› = move.destinationBlock := by
        rw [move.destinationFound] at found
        exact Option.some.inj found.symm
      subst_vars
      exact
        ⟨growing, move.destinationCreator, unassigned,
          by simpa [move.destinationCreator] using valueOrder⟩

end BoundaryPairingMove

/--
An actual-pass classification together with chronological delete/insert
witnesses for every important and unimportant boundary slot.
-/
structure BoundaryPassPairingClassification
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : Tree.BST 0 n}
    {sequence : Tree.BST.SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    (params : Interface.Parameters)
    (initial final : Lazy.State n)
    (events : List (Lazy.Event n)) where
  trace : Lazy.Trace params initial events final
  passClassification :
    PassPairingClassification transcript params
      initial.toInterface final.toInterface
      (Lazy.eraseOperations events)

  importantMoves : List (BoundaryPairingMove trace)
  unimportantMoves : List (BoundaryPairingMove trace)

  importantSlots_eq :
    importantMoves.map BoundaryPairingMove.slot =
      passClassification.importantSlots
  unimportantSlots_eq :
    unimportantMoves.map BoundaryPairingMove.slot =
      passClassification.unimportantSlots

namespace BoundaryPassPairingClassification

/-- Important boundary slots are represented one-for-one by actual moves. -/
theorem importantMoves_length
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
    classification.importantMoves.length =
      classification.passClassification.importantSlots.length := by
  simpa only [List.length_map] using
    congrArg List.length classification.importantSlots_eq

/-- Unimportant boundary slots are represented one-for-one by actual moves. -/
theorem unimportantMoves_length
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
    classification.unimportantMoves.length =
      classification.passClassification.unimportantSlots.length := by
  simpa only [List.length_map] using
    congrArg List.length classification.unimportantSlots_eq

end BoundaryPassPairingClassification

end Splay.Accounting
