import Splay.Accounting.CostSensitiveAlignmentInitializationObstruction

namespace Splay.Accounting

open Splay.Lazy
open Splay.Lazy.Canonical
open Splay.Rank
open Splay.Tree.BST

/--
Endpoint agreement for a boundary move without dependent transport through a
proof that the move's slot is the selected transcript slot.

Keeping `slot_eq` explicit makes the record stable under trace prefixing and
suffixing, which preserve the move fields but change the trace index.
-/
structure BoundaryPairingEndpointAgreement
    {n : ℕ} {accesses : List (Fin n)}
    {sequenceBefore sequenceAfter : BST 0 n}
    {sequence : SplaySequence accesses sequenceBefore sequenceAfter}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    (snapshot : Snapshot n)
    {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    {trace : Trace params initial events final}
    (move : BoundaryPairingMove trace) : Type where
  slot : PairingSlot
  endpoints : PairingSlotHeapEndpoints transcript snapshot slot
  slot_eq : move.slot = slot
  winner_eq : move.winner = endpoints.winner
  loser_eq : move.loser = endpoints.loser

/--
The initialization-safe replacement for `CostSensitivePairingAlignment`.

The abstract pass classification starts at the genuinely empty canonical
state and sees the complete initialized trace.  The represented transition,
on the other hand, starts only after initialization, where stability and
complete block assignment are available.  This separation is forced by
`no_costSensitivePairingAlignment_of_pos`.

Unlike the old record, endpoint agreement here uses the transcript's
canonical `PairingSlotHeapEndpoints` directly.  The rich suffix is already
stored as a represented transition, while the classification stores the
actual pass or delete/insert operation selected for every slot.
-/
structure InitializedCostSensitivePairingAlignment
    {n : ℕ} {accesses : List (Fin n)}
    {sequenceBefore sequenceAfter : BST 0 n}
    {sequence : SplaySequence accesses sequenceBefore sequenceAfter}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    {params : Interface.Parameters} {snapshot : Snapshot n}
    {suffixBefore suffixAfter : BST 0 n}
    (initialization :
      Initialization params snapshot suffixBefore)
    {transition :
      RepresentedTransition params
        snapshot suffixBefore snapshot suffixAfter initialization.final}
    (classification :
      BoundaryPassPairingClassification transcript params
        (Canonical.emptyCanonicalState snapshot suffixBefore)
        transition.final
        (initialization.events ++ transition.events)) : Prop where
  internal :
    ∀ charge,
      charge ∈ classification.passClassification.internalCharges →
        ∃ endpoints :
            PairingSlotHeapEndpoints transcript snapshot charge.1,
          ActivitySlotMatchesHeapEndpoints charge.2 endpoints
  important :
    ∀ move,
      move ∈ classification.importantMoves →
        Nonempty
          (BoundaryPairingEndpointAgreement transcript snapshot move)
  unimportant :
    ∀ move,
      move ∈ classification.unimportantMoves →
        Nonempty
          (BoundaryPairingEndpointAgreement transcript snapshot move)

namespace InitializedCostSensitivePairingAlignment

variable
    {n : ℕ} {accesses : List (Fin n)}
    {sequenceBefore sequenceAfter : BST 0 n}
    {sequence : SplaySequence accesses sequenceBefore sequenceAfter}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {params : Interface.Parameters} {snapshot : Snapshot n}
    {suffixBefore suffixAfter : BST 0 n}
    {initialization :
      Initialization params snapshot suffixBefore}
    {transition :
      RepresentedTransition params
        snapshot suffixBefore snapshot suffixAfter initialization.final}
    {classification :
      BoundaryPassPairingClassification transcript params
        (Canonical.emptyCanonicalState snapshot suffixBefore)
        transition.final
        (initialization.events ++ transition.events)}

/--
Every important move in the repaired interface has the automatic comparison
rank order and exact post-zig-zig canonical parent, in addition to the
delete/insert validity already carried by `BoundaryPairingMove`.
-/
theorem importantMove_sound
    (alignment :
      InitializedCostSensitivePairingAlignment transcript
        initialization classification)
    (move : BoundaryPairingMove classification.trace)
    (member : move ∈ classification.importantMoves) :
    ∃ agreement :
        BoundaryPairingEndpointAgreement transcript snapshot move,
        snapshot.rank move.winner < snapshot.rank move.loser ∧
        canonicalParent snapshot
            agreement.endpoints.occurrence.stepAfter
            move.loser =
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
  have rank :
      snapshot.rank move.winner < snapshot.rank move.loser := by
    rw [agreement.winner_eq, agreement.loser_eq]
    exact agreement.endpoints.rank_lt
  have parent :
      canonicalParent snapshot agreement.endpoints.occurrence.stepAfter
          move.loser =
        some move.winner := by
    rw [agreement.loser_eq, agreement.winner_eq]
    exact agreement.endpoints.after_canonicalParent
  exact
    ⟨agreement, rank, parent, move.delete_source_valid,
      move.insert_destination_valid⟩

/--
All-important suffix moves yield a repaired endpoint alignment after a
checked initialization prefix.

The endpoint premise is stated only for the suffix moves.  Prepending the
initialization trace preserves their slot, winner, and loser definitionally,
so no new semantic premise is introduced by the repair.
-/
theorem exists_ofInitializedAllImportantSuffix
    (suffixMoves : List (BoundaryPairingMove transition.trace))
    (movesSlots :
      suffixMoves.map BoundaryPairingMove.slot =
        firstPairings kinds ++ secondPairings kinds)
    (endpointMatches :
      ∀ move,
        move ∈ suffixMoves →
          Nonempty
            (BoundaryPairingEndpointAgreement
              transcript snapshot move)) :
    let classification :=
      BoundaryPassPairingClassification.ofInitializedAllImportantSuffix
        (params := params) (snapshot := snapshot)
        (initializedTree := suffixBefore)
        transcript initialization transition.trace suffixMoves movesSlots
    Nonempty
      (InitializedCostSensitivePairingAlignment transcript
        initialization classification) := by
  let classification :=
    BoundaryPassPairingClassification.ofInitializedAllImportantSuffix
      (params := params) (snapshot := snapshot)
      (initializedTree := suffixBefore)
      transcript initialization transition.trace suffixMoves movesSlots
  refine ⟨{
    internal := ?_
    important := ?_
    unimportant := ?_
  }⟩
  · intro charge member
    change charge ∈ ([] : List _) at member
    simp at member
  · intro move member
    change
      move ∈
        suffixMoves.map
          (fun suffixMove =>
            suffixMove.prepend initialization.trace) at member
    obtain ⟨suffixMove, suffixMember, moveEq⟩ :=
      List.mem_map.mp member
    subst move
    obtain ⟨agreement⟩ :=
      endpointMatches suffixMove suffixMember
    exact
      ⟨{
        slot := agreement.slot
        endpoints := agreement.endpoints
        slot_eq := agreement.slot_eq
        winner_eq := agreement.winner_eq
        loser_eq := agreement.loser_eq
      }⟩
  · intro move member
    change move ∈ ([] : List _) at member
    simp at member

end InitializedCostSensitivePairingAlignment

namespace AtomicInitializedSingleZigZigAlignment

/-- The first slot belonging to a fixed global zig-zig position. -/
def firstSlot (zigZigStep : ℕ) : PairingSlot :=
  { zigZigStep := zigZigStep, phase := .first }

/-- The second slot belonging to a fixed global zig-zig position. -/
def secondSlot (zigZigStep : ℕ) : PairingSlot :=
  { zigZigStep := zigZigStep, phase := .second }

/--
Reuse the exact same chronological zig-zig occurrence for its second pairing
phase.  Only the phase tag changes; request, local step, trees, and depth stay
definitionally identical.
-/
def secondOccurrence
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {zigZigStep : ℕ}
    (occurrence :
      PairingSlotOccurrence transcript (firstSlot zigZigStep)) :
    PairingSlotOccurrence transcript (secondSlot zigZigStep) where
  phase := .second
  phase_eq := rfl
  requestIndex := occurrence.requestIndex
  access := occurrence.access
  requestBefore := occurrence.requestBefore
  requestAfter := occurrence.requestAfter
  localStepIndex := occurrence.localStepIndex
  stepBefore := occurrence.stepBefore
  stepAfter := occurrence.stepAfter
  depth := occurrence.depth
  step := occurrence.step
  orientation := occurrence.orientation
  occurrence := occurrence.occurrence

end AtomicInitializedSingleZigZigAlignment

/--
Fully automatic initialized endpoint alignment for a transcript whose only
pairing slots are the two phases of one genuine zig-zig.

The theorem:

* recovers the exact transcript occurrence from `zigZigStep`;
* extracts both canonical heap-child endpoint pairs jointly;
* runs productive atomic initialization of the local pre-zig-zig tree;
* executes both concrete seven-event boundary macros;
* prepends initialization and builds the global all-important activity
  classification; and
* proves both move/heap-endpoint equalities by construction.

Thus neither endpoint equality nor a boundary event occurrence remains as a
premise.
-/
theorem exists_atomicInitialized_singleZigZig_aligned
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    {params : Interface.Parameters} {snapshot : Snapshot n}
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound)
    (zigZigStep : ℕ)
    (allSlots_eq :
      firstPairings kinds ++ secondPairings kinds =
        [AtomicInitializedSingleZigZigAlignment.firstSlot zigZigStep,
          AtomicInitializedSingleZigZigAlignment.secondSlot zigZigStep]) :
    ∃ occurrence :
        PairingSlotOccurrence transcript
          (AtomicInitializedSingleZigZigAlignment.firstSlot zigZigStep),
      let initialization :=
        Splay.Lazy.Canonical.atomicInitialization
          snapshot occurrence.stepBefore params growingLimit valueBound
      ∃ firstWinner firstLoser secondWinner secondLoser,
        ∃ certificate :
            ZigZigBoundaryPairingMacro.Certificate
              (params := params) (snapshot := snapshot)
              (beforeTree := occurrence.stepBefore)
              (afterTree := occurrence.stepAfter)
              (depth := occurrence.depth)
              (key := occurrence.access.val)
              initialization.final zigZigStep
              firstWinner firstLoser secondWinner secondLoser,
          let moves :=
            [certificate.firstMove, certificate.secondMove]
          let classification :=
            BoundaryPassPairingClassification.ofInitializedAllImportantSuffix
              (params := params) (snapshot := snapshot)
              (initializedTree := occurrence.stepBefore)
              transcript initialization certificate.transition.trace
              moves
              (by
                change
                  [certificate.firstMove.slot,
                    certificate.secondMove.slot] =
                    firstPairings kinds ++ secondPairings kinds
                rw [certificate.first_slot, certificate.second_slot]
                exact allSlots_eq.symm)
          Nonempty
            (InitializedCostSensitivePairingAlignment transcript
              initialization classification) := by
  let firstSlot :=
    AtomicInitializedSingleZigZigAlignment.firstSlot zigZigStep
  let secondSlot :=
    AtomicInitializedSingleZigZigAlignment.secondSlot zigZigStep
  have firstMember :
      firstSlot ∈ firstPairings kinds ++ secondPairings kinds := by
    rw [allSlots_eq]
    simp [firstSlot]
  obtain ⟨occurrence⟩ :=
    exists_pairingSlotOccurrence transcript firstSlot firstMember
  let initialization :=
    Splay.Lazy.Canonical.atomicInitialization
      snapshot occurrence.stepBefore params growingLimit valueBound
  have initializationAtomic : initialization.final.ShiftAtomic :=
    atomicInitialization_final_shiftAtomic
      snapshot occurrence.stepBefore params growingLimit valueBound
  obtain
      ⟨firstWinner, firstLoser, secondWinner, secondLoser,
        firstEndpoints, secondEndpoints, losersNe⟩ :=
    ZigZigPairingEndpointsAt.exists_both_of_orientation
      snapshot occurrence.orientation (Nat.le_refl n)
  obtain ⟨certificate⟩ :=
    ZigZigBoundaryPairingMacro.exists_certificate_of_endpoints
      initialization.final_represents initializationAtomic zigZigStep
      firstEndpoints secondEndpoints losersNe
  let secondOccurrence :=
    AtomicInitializedSingleZigZigAlignment.secondOccurrence occurrence
  let firstHeapEndpoints :
      PairingSlotHeapEndpoints transcript snapshot firstSlot := {
    occurrence := occurrence
    winner := firstWinner
    loser := firstLoser
    endpoints := firstEndpoints
  }
  let secondHeapEndpoints :
      PairingSlotHeapEndpoints transcript snapshot secondSlot := {
    occurrence := secondOccurrence
    winner := secondWinner
    loser := secondLoser
    endpoints := secondEndpoints
  }
  let moves := [certificate.firstMove, certificate.secondMove]
  have movesSlots :
      moves.map BoundaryPairingMove.slot =
        firstPairings kinds ++ secondPairings kinds := by
    change
      [certificate.firstMove.slot, certificate.secondMove.slot] =
        firstPairings kinds ++ secondPairings kinds
    rw [certificate.first_slot, certificate.second_slot]
    exact allSlots_eq.symm
  have movesMatch :
      ∀ move,
        move ∈ moves →
          Nonempty
            (BoundaryPairingEndpointAgreement
              transcript snapshot move) := by
    intro move member
    simp [moves] at member
    rcases member with rfl | rfl
    · exact
        ⟨{
          slot := firstSlot
          endpoints := firstHeapEndpoints
          slot_eq := by
            simpa [firstSlot,
              AtomicInitializedSingleZigZigAlignment.firstSlot] using
              certificate.first_slot
          winner_eq := certificate.first_winner
          loser_eq := certificate.first_loser
        }⟩
    · exact
        ⟨{
          slot := secondSlot
          endpoints := secondHeapEndpoints
          slot_eq := by
            simpa [secondSlot,
              AtomicInitializedSingleZigZigAlignment.secondSlot] using
              certificate.second_slot
          winner_eq := certificate.second_winner
          loser_eq := certificate.second_loser
        }⟩
  have aligned :=
    InitializedCostSensitivePairingAlignment.exists_ofInitializedAllImportantSuffix
      (initialization := initialization)
      (transition := certificate.transition)
      moves movesSlots movesMatch
  exact
    ⟨occurrence, firstWinner, firstLoser, secondWinner, secondLoser,
      certificate, aligned⟩

end Splay.Accounting
