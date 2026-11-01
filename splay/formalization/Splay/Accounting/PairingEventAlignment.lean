import Splay.Accounting.PairingHeapChildEndpoints
import Splay.Lazy.ComparisonRotationPreparation

namespace Splay.Accounting

open Splay.Rank
open Splay.Tree.BST
open Splay.Lazy
open Splay.Lazy.Canonical

/--
The exact semantic residue between a realized transcript slot and one lazy
pairing event.

All chronology and tree geometry are already stored in `endpoints`.  The only
new information is that the event's two externally visible elements are the
automatically selected heap-child endpoints.  Consequently this record has
exactly the two equalities isolated by
`BoundaryPairingMove.MatchesHeapEndpoints` and
`ActivitySlotMatchesHeapEndpoints`, but retains the exact contiguous rich
event segment supplied by execution provenance.
-/
structure RealizedPairingEndpointAgreement
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    {initial : State n}
    {transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial}
    (provenance :
      SplaySequence.RepresentedTransitionProvenance
        sequence transition)
    (slot : PairingSlot)
    (winner loser : Interface.Element n) : Type where
  endpoints :
    RealizedPairingSlotHeapEndpoints transcript provenance slot
  winner_eq : winner = endpoints.winner
  loser_eq : loser = endpoints.loser

namespace RealizedPairingEndpointAgreement

/-- Endpoint agreement transfers the automatic strict comparison-rank order. -/
theorem rank_lt
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {initial : State n}
    {transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial}
    {provenance :
      SplaySequence.RepresentedTransitionProvenance
        sequence transition}
    {slot : PairingSlot}
    {winner loser : Interface.Element n}
    (agreement :
      RealizedPairingEndpointAgreement transcript provenance
        slot winner loser) :
    snapshot.rank winner < snapshot.rank loser := by
  calc
    snapshot.rank winner =
        snapshot.rank agreement.endpoints.winner :=
      congrArg snapshot.rank agreement.winner_eq
    _ < snapshot.rank agreement.endpoints.loser :=
      agreement.endpoints.rank_lt
    _ = snapshot.rank loser :=
      (congrArg snapshot.rank agreement.loser_eq).symm

/--
Endpoint agreement also transfers the exact heap-child edge in the concrete
post-zig-zig tree belonging to this slot.
-/
theorem after_canonicalParent
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {initial : State n}
    {transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial}
    {provenance :
      SplaySequence.RepresentedTransitionProvenance
        sequence transition}
    {slot : PairingSlot}
    {winner loser : Interface.Element n}
    (agreement :
      RealizedPairingEndpointAgreement transcript provenance
        slot winner loser) :
    canonicalParent snapshot
        agreement.endpoints.realized.occurrence.stepAfter loser =
      some winner := by
  calc
    canonicalParent snapshot
          agreement.endpoints.realized.occurrence.stepAfter loser =
        canonicalParent snapshot
          agreement.endpoints.realized.occurrence.stepAfter
            agreement.endpoints.loser :=
      congrArg
        (canonicalParent snapshot
          agreement.endpoints.realized.occurrence.stepAfter)
        agreement.loser_eq
    _ = some agreement.endpoints.winner :=
      agreement.endpoints.after_canonicalParent
    _ = some winner :=
      congrArg some agreement.winner_eq.symm

end RealizedPairingEndpointAgreement

namespace PassPairingClassification

/--
Execution provenance automatically realizes the heap-child endpoints of every
internal charge.  No endpoint equality with the chosen pass tuple is used.
-/
theorem internalCharge_realizedHeapEndpoints
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {initial : State n}
    {transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial}
    (provenance :
      SplaySequence.RepresentedTransitionProvenance
        sequence transition)
    (classification :
      PassPairingClassification transcript params
        initial.toInterface transition.final.toInterface
        (eraseOperations transition.events))
    (charge :
      PairingSlot × Interface.ActivitySlot (eraseOperations transition.events))
    (member : charge ∈ classification.internalCharges) :
    Nonempty
      (RealizedPairingSlotHeapEndpoints transcript provenance charge.1) :=
  RealizedPairingSlotHeapEndpoints.exists_of_mem
    transcript provenance charge.1
      (classification.internalCharge_slot_mem_pairings charge member)

end PassPairingClassification

namespace BoundaryPassPairingClassification

/-- Provenance automatically realizes every important move's endpoints. -/
theorem importantMove_realizedHeapEndpoints
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {initial : State n}
    {transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial}
    (provenance :
      SplaySequence.RepresentedTransitionProvenance
        sequence transition)
    (classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events)
    (move : BoundaryPairingMove classification.trace)
    (member : move ∈ classification.importantMoves) :
    Nonempty
      (RealizedPairingSlotHeapEndpoints transcript provenance move.slot) :=
  RealizedPairingSlotHeapEndpoints.exists_of_mem
    transcript provenance move.slot
      (classification.importantMove_slot_mem_pairings move member)

/-- Provenance automatically realizes every unimportant move's endpoints. -/
theorem unimportantMove_realizedHeapEndpoints
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {initial : State n}
    {transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial}
    (provenance :
      SplaySequence.RepresentedTransitionProvenance
        sequence transition)
    (classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events)
    (move : BoundaryPairingMove classification.trace)
    (member : move ∈ classification.unimportantMoves) :
    Nonempty
      (RealizedPairingSlotHeapEndpoints transcript provenance move.slot) :=
  RealizedPairingSlotHeapEndpoints.exists_of_mem
    transcript provenance move.slot
      (classification.unimportantMove_slot_mem_pairings move member)

end BoundaryPassPairingClassification

/--
The minimal cost-sensitive endpoint interface for a classified realized
execution.

The existing boundary/pass classification already supplies actual pass
tuples, actual chronological delete/insert moves, and a partition of every
pairing slot.  Exact sequence provenance already supplies the corresponding
contiguous rich-event segment and automatic heap-child endpoints.  The three
fields below add only endpoint agreement for the selected event in each of
the three classification classes.
-/
structure CostSensitivePairingAlignment
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    {initial : State n}
    {transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial}
    (provenance :
      SplaySequence.RepresentedTransitionProvenance
        sequence transition)
    (classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events) : Prop where
  internal :
    ∀ charge,
      charge ∈ classification.passClassification.internalCharges →
        Nonempty
          (RealizedPairingEndpointAgreement transcript provenance
            charge.1 charge.2.pairing.winner charge.2.pairing.loser)
  important :
    ∀ move,
      move ∈ classification.importantMoves →
        Nonempty
          (RealizedPairingEndpointAgreement transcript provenance
            move.slot move.winner move.loser)
  unimportant :
    ∀ move,
      move ∈ classification.unimportantMoves →
        Nonempty
          (RealizedPairingEndpointAgreement transcript provenance
            move.slot move.winner move.loser)

namespace CostSensitivePairingAlignment

variable
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {initial : State n}
    {transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial}
    {provenance :
      SplaySequence.RepresentedTransitionProvenance
        sequence transition}
    {classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events}

/--
Every classified internal charge is an actual legal pass tuple with the
automatic heap-child rank order and exact post-zig-zig parent edge.
-/
theorem internalCharge_sound
    (alignment :
      CostSensitivePairingAlignment transcript provenance classification)
    (charge :
      PairingSlot ×
        Interface.ActivitySlot (eraseOperations transition.events))
    (member :
      charge ∈ classification.passClassification.internalCharges) :
    ∃ agreement :
        RealizedPairingEndpointAgreement transcript provenance
          charge.1 charge.2.pairing.winner charge.2.pairing.loser,
      snapshot.rank charge.2.pairing.winner <
          snapshot.rank charge.2.pairing.loser ∧
        canonicalParent snapshot
            agreement.endpoints.realized.occurrence.stepAfter
            charge.2.pairing.loser =
          some charge.2.pairing.winner ∧
        ∃ before after sourceBlock,
          Interface.Trace.StepAt
              classification.passClassification.trace
              charge.2.operationIndex.val before
              (.pass charge.2.source charge.2.matching) after ∧
            before.block? charge.2.source = some sourceBlock ∧
            Interface.PairingValid before charge.2.source sourceBlock
              charge.2.pairing := by
  obtain ⟨agreement⟩ := alignment.internal charge member
  refine
    ⟨agreement, agreement.rank_lt, agreement.after_canonicalParent, ?_⟩
  exact
    classification.passClassification.internalCharge_pairingValid
      charge member

/--
Every important boundary move has the automatic rank/parent geometry, in
addition to its already checked delete and insert preconditions.
-/
theorem importantMove_sound
    (alignment :
      CostSensitivePairingAlignment transcript provenance classification)
    (move : BoundaryPairingMove classification.trace)
    (member : move ∈ classification.importantMoves) :
    ∃ agreement :
        RealizedPairingEndpointAgreement transcript provenance
          move.slot move.winner move.loser,
      snapshot.rank move.winner < snapshot.rank move.loser ∧
        canonicalParent snapshot
            agreement.endpoints.realized.occurrence.stepAfter move.loser =
          some move.winner ∧
        (∃ sourceBlock,
          move.deleteBefore.toInterface.block? move.source =
              some sourceBlock ∧
            sourceBlock.mode = .shrinking ∧
            move.loser ∈ sourceBlock.elements) ∧
        move.destinationBlock.mode = .growing ∧
        move.destinationBlock.creator = move.winner ∧
        move.loser ∉ move.insertBefore.toInterface.allElements ∧
        move.insertBefore.toInterface.value move.winner + 1 ≤
          move.insertBefore.toInterface.value move.loser := by
  obtain ⟨agreement⟩ := alignment.important move member
  exact
    ⟨agreement, agreement.rank_lt, agreement.after_canonicalParent,
      move.delete_source_valid, move.insert_destination_valid⟩

/--
Every unimportant boundary move has the same exact rank/parent and legal
delete/insert facts; only its later persistent-block accounting label differs.
-/
theorem unimportantMove_sound
    (alignment :
      CostSensitivePairingAlignment transcript provenance classification)
    (move : BoundaryPairingMove classification.trace)
    (member : move ∈ classification.unimportantMoves) :
    ∃ agreement :
        RealizedPairingEndpointAgreement transcript provenance
          move.slot move.winner move.loser,
      snapshot.rank move.winner < snapshot.rank move.loser ∧
        canonicalParent snapshot
            agreement.endpoints.realized.occurrence.stepAfter move.loser =
          some move.winner ∧
        (∃ sourceBlock,
          move.deleteBefore.toInterface.block? move.source =
              some sourceBlock ∧
            sourceBlock.mode = .shrinking ∧
            move.loser ∈ sourceBlock.elements) ∧
        move.destinationBlock.mode = .growing ∧
        move.destinationBlock.creator = move.winner ∧
        move.loser ∉ move.insertBefore.toInterface.allElements ∧
        move.insertBefore.toInterface.value move.winner + 1 ≤
          move.insertBefore.toInterface.value move.loser := by
  obtain ⟨agreement⟩ := alignment.unimportant move member
  exact
    ⟨agreement, agreement.rank_lt, agreement.after_canonicalParent,
      move.delete_source_valid, move.insert_destination_valid⟩

/-- The endpoint-aligned classification still covers both slots per zig-zig. -/
theorem pairingSlots_le_classifiedVisibleSemantics
    (_alignment :
      CostSensitivePairingAlignment transcript provenance classification) :
    2 * zigZig ≤
      classification.importantMoves.length +
        classification.unimportantMoves.length +
        Interface.totalActivity (eraseOperations transition.events) := by
  have bound :=
    classification.passClassification.zigZig_pairings
  rw [← classification.importantMoves_length,
    ← classification.unimportantMoves_length] at bound
  exact bound

end CostSensitivePairingAlignment

namespace SilentStructuralRebase

/-- A singleton silent event contains no visible interface operation. -/
theorem no_visible_operation {n : ℕ} :
    ¬ ∃ operation : Interface.Operation n,
      Event.operation operation ∈ ([Event.silent] : List (Event n)) := by
  simp

/--
A genuine same-snapshot structural rebase can change the represented splay
shape using exactly one silent event.

This is the concrete obstruction to deriving cost-sensitive endpoint
agreement from `RepresentedTransition` or its structural realizer alone:
the resulting transition has neither a pass activity slot nor even a
boundary delete/insert move.  An actual pairing macro must therefore supply
additional visible-event semantics.
-/
theorem exists_transition_without_pairing_events
    {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n}
    {beforeTree afterTree : BST 0 n}
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree)
    (initialAtomic : initial.ShiftAtomic) :
    ∃ transition :
        RepresentedTransition params
          snapshot beforeTree snapshot afterTree initial,
      transition.events = [.silent] ∧
        (¬ Nonempty
          (Interface.ActivitySlot
            (eraseOperations transition.events))) ∧
        (¬ Nonempty (BoundaryPairingMove transition.trace)) := by
  let afterView := canonicalHeapView snapshot afterTree
  have rootEq :
      afterView.root = initial.view.root := by
    change
      canonicalRoot snapshot afterTree = initial.view.root
    rw [initialRepresents.view_eq]
    exact canonicalRoot_eq snapshot afterTree beforeTree
  let final := initial.rebaseShiftAtomic afterView
  have rebaseTrace :
      Trace params initial [.silent] final := by
    exact
      initialAtomic.rebase_trace initialRepresents.valid rootEq
  have finalPrepared :
      final.RankPrepared params := by
    exact
      initialAtomic.rebase_rankPrepared
        initialRepresents.stable rootEq
  have finalStable :
      final.Stable params := by
    exact
      finalPrepared.stable
        (canonicalHeapView_heapOrdered snapshot afterTree)
  have finalRepresents :
      final.Represents params snapshot afterTree := by
    refine ⟨finalStable, ?_⟩
    exact State.rebaseShiftAtomic_view initial afterView
  let transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial := {
    initial_represents := initialRepresents
    final := final
    events := [.silent]
    trace := rebaseTrace
    final_represents := finalRepresents
  }
  refine ⟨transition, rfl, ?_, ?_⟩
  · intro slot
    obtain ⟨slot⟩ := slot
    have impossible := slot.operationIndex.isLt
    simp [transition, eraseOperations, Event.operations] at impossible
  · intro move
    obtain ⟨move⟩ := move
    have impossible := move.deleteAt.operationIndex_lt
    simp [transition, eraseOperations, Event.operations] at impossible

end SilentStructuralRebase

end Splay.Accounting
