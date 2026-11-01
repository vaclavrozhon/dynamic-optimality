import Splay.Accounting.MultiZigZigBoundaryPairingRealizer

namespace Splay.Accounting

open Splay.Lazy
open Splay.Lazy.Canonical
open Splay.Rank
open Splay.Tree.BST

namespace BoundaryPairingEndpointAgreement

/-- Endpoint agreement is unchanged when the rich trace is extended. -/
def append
    {n : ℕ} {accesses : List (Fin n)}
    {sequenceBefore sequenceAfter : BST 0 n}
    {sequence : SplaySequence accesses sequenceBefore sequenceAfter}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {snapshot : Snapshot n} {params : Interface.Parameters}
    {initial middle final : State n}
    {prefixEvents suffixEvents : List (Event n)}
    {prefixTrace : Trace params initial prefixEvents middle}
    {move : BoundaryPairingMove prefixTrace}
    (agreement :
      BoundaryPairingEndpointAgreement transcript snapshot
        (trace := prefixTrace) move)
    (suffixTrace : Trace params middle suffixEvents final) :
    BoundaryPairingEndpointAgreement transcript snapshot
      (move.append suffixTrace) where
  slot := agreement.slot
  endpoints := agreement.endpoints
  slot_eq := agreement.slot_eq
  winner_eq := agreement.winner_eq
  loser_eq := agreement.loser_eq

/-- Endpoint agreement is unchanged when a rich-trace prefix is added. -/
def prepend
    {n : ℕ} {accesses : List (Fin n)}
    {sequenceBefore sequenceAfter : BST 0 n}
    {sequence : SplaySequence accesses sequenceBefore sequenceAfter}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {snapshot : Snapshot n} {params : Interface.Parameters}
    {initial middle final : State n}
    {prefixEvents suffixEvents : List (Event n)}
    (prefixTrace : Trace params initial prefixEvents middle)
    {suffixTrace : Trace params middle suffixEvents final}
    {move : BoundaryPairingMove suffixTrace}
    (agreement :
      BoundaryPairingEndpointAgreement transcript snapshot
        (trace := suffixTrace) move) :
    BoundaryPairingEndpointAgreement transcript snapshot
      (move.prepend prefixTrace) where
  slot := agreement.slot
  endpoints := agreement.endpoints
  slot_eq := agreement.slot_eq
  winner_eq := agreement.winner_eq
  loser_eq := agreement.loser_eq

/-- Endpoint agreement follows proof-irrelevant reindexing of a trace. -/
def castTrace
    {n : ℕ} {accesses : List (Fin n)}
    {sequenceBefore sequenceAfter : BST 0 n}
    {sequence : SplaySequence accesses sequenceBefore sequenceAfter}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {snapshot : Snapshot n} {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    {sourceTrace : Trace params initial events final}
    (targetTrace : Trace params initial events final)
    {move : BoundaryPairingMove sourceTrace}
    (agreement :
      BoundaryPairingEndpointAgreement transcript snapshot move) :
    BoundaryPairingEndpointAgreement transcript snapshot
      (move.castTrace targetTrace) := by
  have traceEq : sourceTrace = targetTrace := Subsingleton.elim _ _
  cases traceEq
  exact agreement

end BoundaryPairingEndpointAgreement

namespace BoundaryPairingMove

/-- Endpoint matching follows proof-irrelevant trace reindexing of a list. -/
theorem endpointMatches_castAll
    {n : ℕ} {accesses : List (Fin n)}
    {sequenceBefore sequenceAfter : BST 0 n}
    {sequence : SplaySequence accesses sequenceBefore sequenceAfter}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {snapshot : Snapshot n} {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    {sourceTrace : Trace params initial events final}
    (targetTrace : Trace params initial events final)
    (moves : List (BoundaryPairingMove sourceTrace))
    (endpointMatches :
      ∀ move,
        move ∈ moves →
          Nonempty
            (BoundaryPairingEndpointAgreement
              transcript snapshot move)) :
    ∀ move,
      move ∈ castAll targetTrace moves →
        Nonempty
          (BoundaryPairingEndpointAgreement
            transcript snapshot move) := by
  intro move member
  simp only [castAll] at member
  obtain ⟨sourceMove, sourceMember, rfl⟩ :=
    List.mem_map.mp member
  obtain ⟨agreement⟩ := endpointMatches sourceMove sourceMember
  exact ⟨agreement.castTrace targetTrace⟩

/-- Endpoint matching is preserved while moves are extended by a suffix. -/
theorem endpointMatches_appendAll
    {n : ℕ} {accesses : List (Fin n)}
    {sequenceBefore sequenceAfter : BST 0 n}
    {sequence : SplaySequence accesses sequenceBefore sequenceAfter}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {snapshot : Snapshot n} {params : Interface.Parameters}
    {initial middle final : State n}
    {prefixEvents suffixEvents : List (Event n)}
    {prefixTrace : Trace params initial prefixEvents middle}
    (moves : List (BoundaryPairingMove prefixTrace))
    (suffixTrace : Trace params middle suffixEvents final)
    (endpointMatches :
      ∀ move,
        move ∈ moves →
          Nonempty
            (BoundaryPairingEndpointAgreement
              transcript snapshot move)) :
    ∀ move,
      move ∈ appendAll moves suffixTrace →
        Nonempty
          (BoundaryPairingEndpointAgreement
            transcript snapshot move) := by
  intro move member
  simp only [appendAll] at member
  obtain ⟨sourceMove, sourceMember, rfl⟩ :=
    List.mem_map.mp member
  obtain ⟨agreement⟩ := endpointMatches sourceMove sourceMember
  exact ⟨agreement.append suffixTrace⟩

/-- Endpoint matching is preserved while moves are extended by a prefix. -/
theorem endpointMatches_prependAll
    {n : ℕ} {accesses : List (Fin n)}
    {sequenceBefore sequenceAfter : BST 0 n}
    {sequence : SplaySequence accesses sequenceBefore sequenceAfter}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {snapshot : Snapshot n} {params : Interface.Parameters}
    {initial middle final : State n}
    {prefixEvents suffixEvents : List (Event n)}
    {suffixTrace : Trace params middle suffixEvents final}
    (moves : List (BoundaryPairingMove suffixTrace))
    (prefixTrace : Trace params initial prefixEvents middle)
    (endpointMatches :
      ∀ move,
        move ∈ moves →
          Nonempty
            (BoundaryPairingEndpointAgreement
              transcript snapshot move)) :
    ∀ move,
      move ∈ prependAll moves prefixTrace →
        Nonempty
          (BoundaryPairingEndpointAgreement
            transcript snapshot move) := by
  intro move member
  simp only [prependAll] at member
  obtain ⟨sourceMove, sourceMember, rfl⟩ :=
    List.mem_map.mp member
  obtain ⟨agreement⟩ := endpointMatches sourceMove sourceMember
  exact ⟨agreement.prepend prefixTrace⟩

/-- Endpoint matching is preserved while a list of moves is appended. -/
theorem endpointMatches_appendAllInto
    {n : ℕ} {accesses : List (Fin n)}
    {sequenceBefore sequenceAfter : BST 0 n}
    {sequence : SplaySequence accesses sequenceBefore sequenceAfter}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {snapshot : Snapshot n} {params : Interface.Parameters}
    {initial middle final : State n}
    {prefixEvents suffixEvents : List (Event n)}
    {prefixTrace : Trace params initial prefixEvents middle}
    (moves : List (BoundaryPairingMove prefixTrace))
    (suffixTrace : Trace params middle suffixEvents final)
    (targetTrace :
      Trace params initial (prefixEvents ++ suffixEvents) final)
    (endpointMatches :
      ∀ move,
        move ∈ moves →
          Nonempty
            (BoundaryPairingEndpointAgreement
              transcript snapshot move)) :
    ∀ move,
      move ∈ appendAllInto moves suffixTrace targetTrace →
        Nonempty
          (BoundaryPairingEndpointAgreement
            transcript snapshot move) := by
  intro move member
  simp only [appendAllInto, castAll, appendAll, List.map_map] at member
  obtain ⟨sourceMove, sourceMember, rfl⟩ :=
    List.mem_map.mp member
  obtain ⟨agreement⟩ := endpointMatches sourceMove sourceMember
  exact
    ⟨(agreement.append suffixTrace).castTrace targetTrace⟩

/-- Endpoint matching is preserved while a list of moves is prepended. -/
theorem endpointMatches_prependAllInto
    {n : ℕ} {accesses : List (Fin n)}
    {sequenceBefore sequenceAfter : BST 0 n}
    {sequence : SplaySequence accesses sequenceBefore sequenceAfter}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {snapshot : Snapshot n} {params : Interface.Parameters}
    {initial middle final : State n}
    {prefixEvents suffixEvents : List (Event n)}
    {suffixTrace : Trace params middle suffixEvents final}
    (moves : List (BoundaryPairingMove suffixTrace))
    (prefixTrace : Trace params initial prefixEvents middle)
    (targetTrace :
      Trace params initial (prefixEvents ++ suffixEvents) final)
    (endpointMatches :
      ∀ move,
        move ∈ moves →
          Nonempty
            (BoundaryPairingEndpointAgreement
              transcript snapshot move)) :
    ∀ move,
      move ∈ prependAllInto moves prefixTrace targetTrace →
        Nonempty
          (BoundaryPairingEndpointAgreement
            transcript snapshot move) := by
  intro move member
  simp only [prependAllInto, castAll, prependAll, List.map_map] at member
  obtain ⟨sourceMove, sourceMember, rfl⟩ :=
    List.mem_map.mp member
  obtain ⟨agreement⟩ := endpointMatches sourceMove sourceMember
  exact
    ⟨(agreement.prepend prefixTrace).castTrace targetTrace⟩

end BoundaryPairingMove

/--
A global slot occurrence that retains the exact access and local rotation
geometry from which it was lifted.
-/
structure LiftedPairingSlotOccurrence
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    (slot : PairingSlot)
    (access : Fin n) (stepBefore stepAfter : BST 0 n)
    (depth : ℕ) where
  occurrence : PairingSlotOccurrence transcript slot
  access_eq : occurrence.access = access
  stepBefore_eq : occurrence.stepBefore = stepBefore
  stepAfter_eq : occurrence.stepAfter = stepAfter
  depth_eq : occurrence.depth = depth

namespace LiftedPairingSlotOccurrence

/-- Package a concrete global zig-zig occurrence with its own geometry. -/
def ofSequenceOccurrence
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {globalIndex requestIndex : ℕ} {access : Fin n}
    {requestBefore requestAfter : BST 0 n}
    {localIndex : ℕ} {stepBefore stepAfter : BST 0 n} {depth : ℕ}
    (occurrence :
      SplaySequenceTranscript.ZigZigAt transcript globalIndex
        requestIndex access requestBefore requestAfter localIndex
        stepBefore stepAfter depth)
    (phase : PairingPhase) :
    LiftedPairingSlotOccurrence transcript
      { zigZigStep := globalIndex, phase := phase }
      access stepBefore stepAfter depth :=
  let geometry := occurrence.geometry
  {
    occurrence := {
      phase := phase
      phase_eq := rfl
      requestIndex := requestIndex
      access := access
      requestBefore := requestBefore
      requestAfter := requestAfter
      localStepIndex := localIndex
      stepBefore := stepBefore
      stepAfter := stepAfter
      depth := depth
      step := geometry.1
      orientation := geometry.2
      occurrence := occurrence
    }
    access_eq := rfl
    stepBefore_eq := rfl
    stepAfter_eq := rfl
    depth_eq := rfl
  }

/-- Attach canonical endpoint labels to geometry preserved by a lift. -/
def toHeapEndpoints
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {snapshot : Snapshot n} {slot : PairingSlot}
    {access : Fin n} {stepBefore stepAfter : BST 0 n}
    {depth : ℕ}
    (lifted :
      LiftedPairingSlotOccurrence transcript slot access
        stepBefore stepAfter depth)
    {winner loser : Interface.Element n}
    (endpoints :
      ZigZigPairingEndpointsAt snapshot slot.phase
        (depth := depth) (key := access.val)
        stepBefore stepAfter winner loser) :
    PairingSlotHeapEndpoints transcript snapshot slot := by
  rcases lifted with
    ⟨occurrence, accessEq, stepBeforeEq, stepAfterEq, depthEq⟩
  subst access
  subst stepBefore
  subst stepAfter
  subst depth
  exact {
    occurrence := occurrence
    winner := winner
    loser := loser
    endpoints := endpoints
  }

@[simp]
theorem toHeapEndpoints_winner
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {snapshot : Snapshot n} {slot : PairingSlot}
    {access : Fin n} {stepBefore stepAfter : BST 0 n}
    {depth : ℕ}
    (lifted :
      LiftedPairingSlotOccurrence transcript slot access
        stepBefore stepAfter depth)
    {winner loser : Interface.Element n}
    (endpoints :
      ZigZigPairingEndpointsAt snapshot slot.phase
        (depth := depth) (key := access.val)
        stepBefore stepAfter winner loser) :
    (lifted.toHeapEndpoints endpoints).winner = winner := by
  rcases lifted with
    ⟨occurrence, accessEq, stepBeforeEq, stepAfterEq, depthEq⟩
  subst access
  subst stepBefore
  subst stepAfter
  subst depth
  rfl

@[simp]
theorem toHeapEndpoints_loser
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {snapshot : Snapshot n} {slot : PairingSlot}
    {access : Fin n} {stepBefore stepAfter : BST 0 n}
    {depth : ℕ}
    (lifted :
      LiftedPairingSlotOccurrence transcript slot access
        stepBefore stepAfter depth)
    {winner loser : Interface.Element n}
    (endpoints :
      ZigZigPairingEndpointsAt snapshot slot.phase
        (depth := depth) (key := access.val)
        stepBefore stepAfter winner loser) :
    (lifted.toHeapEndpoints endpoints).loser = loser := by
  rcases lifted with
    ⟨occurrence, accessEq, stepBeforeEq, stepAfterEq, depthEq⟩
  subst access
  subst stepBefore
  subst stepAfter
  subst depth
  rfl

end LiftedPairingSlotOccurrence

/--
Embed every zig-zig occurrence of one execution into a fixed full sequence
transcript.  The offset is exactly the offset used by the boundary macro.
-/
def ExecutionPairingOccurrenceLift
    {n : ℕ} {accesses : List (Fin n)}
    {sequenceBefore sequenceAfter : BST 0 n}
    {sequence : SplaySequence accesses sequenceBefore sequenceAfter}
    {wholeKinds : List SplayStepKind}
    {wholeZig wholeZigZig wholeZigZag : ℕ}
    (wholeTranscript :
      SplaySequenceTranscript sequence wholeKinds
        wholeZig wholeZigZig wholeZigZag)
    {access : Fin n} {before after : BST 0 n}
    {execution : SplayExecution access.val before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript access.val execution kinds
        zig zigZig zigZag)
    (start : ℕ) : Type :=
  ∀ {index : ℕ} {stepBefore stepAfter : BST 0 n} {depth : ℕ},
    SplayExecutionTranscript.ZigZigAt transcript index
        stepBefore stepAfter depth →
      ∀ phase,
        LiftedPairingSlotOccurrence wholeTranscript
          { zigZigStep := start + index, phase := phase }
          access stepBefore stepAfter depth

/--
Embed every zig-zig occurrence of a suffix sequence into a fixed full
sequence transcript.
-/
def SequencePairingOccurrenceLift
    {n : ℕ} {wholeAccesses : List (Fin n)}
    {wholeBefore wholeAfter : BST 0 n}
    {wholeSequence :
      SplaySequence wholeAccesses wholeBefore wholeAfter}
    {wholeKinds : List SplayStepKind}
    {wholeZig wholeZigZig wholeZigZag : ℕ}
    (wholeTranscript :
      SplaySequenceTranscript wholeSequence wholeKinds
        wholeZig wholeZigZig wholeZigZag)
    {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    (start : ℕ) : Type :=
  ∀ {globalIndex requestIndex : ℕ} {access : Fin n}
      {requestBefore requestAfter : BST 0 n}
      {localIndex : ℕ} {stepBefore stepAfter : BST 0 n} {depth : ℕ},
    SplaySequenceTranscript.ZigZigAt transcript globalIndex
        requestIndex access requestBefore requestAfter localIndex
        stepBefore stepAfter depth →
      ∀ phase,
        LiftedPairingSlotOccurrence wholeTranscript
          { zigZigStep := start + globalIndex, phase := phase }
          access stepBefore stepAfter depth

namespace SplayExecutionEndpointAlignedBoundaryPairingMacro

/--
The recursive execution macro together with endpoint agreement for every
move it exports.  The agreements target one fixed enclosing sequence
transcript.
-/
structure Certificate
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {wholeAccesses : List (Fin n)}
    {wholeBefore wholeAfter : BST 0 n}
    {wholeSequence :
      SplaySequence wholeAccesses wholeBefore wholeAfter}
    {wholeKinds : List SplayStepKind}
    {wholeZig wholeZigZig wholeZigZag : ℕ}
    (wholeTranscript :
      SplaySequenceTranscript wholeSequence wholeKinds
        wholeZig wholeZigZig wholeZigZag)
    {access : Fin n} {beforeTree afterTree : BST 0 n}
    {execution : SplayExecution access.val beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript access.val execution kinds
        zig zigZig zigZag)
    (initial : State n) (start : ℕ) where
  base :
    SplayExecutionBoundaryPairingMacro.Certificate
      (params := params) (snapshot := snapshot)
      transcript initial start
  firstEndpointMatches :
    ∀ move,
      move ∈ base.firstMoves →
        Nonempty
          (BoundaryPairingEndpointAgreement
            wholeTranscript snapshot move)
  secondEndpointMatches :
    ∀ move,
      move ∈ base.secondMoves →
        Nonempty
          (BoundaryPairingEndpointAgreement
            wholeTranscript snapshot move)

/--
Construct the endpoint-enriched execution macro from an occurrence lift into
the enclosing sequence transcript.
-/
theorem exists_certificate
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {wholeAccesses : List (Fin n)}
    {wholeBefore wholeAfter : BST 0 n}
    {wholeSequence :
      SplaySequence wholeAccesses wholeBefore wholeAfter}
    {wholeKinds : List SplayStepKind}
    {wholeZig wholeZigZig wholeZigZag : ℕ}
    (wholeTranscript :
      SplaySequenceTranscript wholeSequence wholeKinds
        wholeZig wholeZigZig wholeZigZag)
    {access : Fin n} {beforeTree afterTree : BST 0 n}
    {execution : SplayExecution access.val beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript access.val execution kinds
        zig zigZig zigZag)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree)
    (initialAtomic : initial.ShiftAtomic)
    (start : ℕ)
    (occurrenceLift :
      ExecutionPairingOccurrenceLift wholeTranscript transcript start) :
    Nonempty
      (Certificate (params := params) (snapshot := snapshot)
        wholeTranscript transcript initial start) := by
  cases transcript with
  | done root =>
      let transition := RepresentedTransition.refl initialRepresents
      let base :
          SplayExecutionBoundaryPairingMacro.Certificate
            (params := params) (snapshot := snapshot)
            (.done root) initial start := {
        transition := transition
        finalAtomic := initialAtomic
        firstMoves := []
        secondMoves := []
        firstSlots_eq := by simp [firstPairingsFrom]
        secondSlots_eq := by simp [secondPairingsFrom]
      }
      exact
        ⟨{
          base := base
          firstEndpointMatches := by
            intro move member
            simp [base] at member
          secondEndpointMatches := by
            intro move member
            simp [base] at member
        }⟩
  | zig step tail tailTranscript =>
      obtain ⟨head⟩ :=
        ShiftAtomicStructuralRebase.exists_certificate
          initialRepresents initialAtomic
      have tailLift :
          ExecutionPairingOccurrenceLift wholeTranscript tailTranscript
            (start + 1) := by
        intro index stepBefore stepAfter depth occurrence phase
        have lifted :=
          occurrenceLift
            (.afterZig step tail tailTranscript occurrence) phase
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lifted
      obtain ⟨rest⟩ :=
        exists_certificate wholeTranscript tailTranscript
          head.transition.final_represents head.finalAtomic
          (start + 1) tailLift
      let transition :=
        head.transition.trans rest.base.transition
      let firstMoves :=
        BoundaryPairingMove.prependAllInto
          rest.base.firstMoves head.transition.trace transition.trace
      let secondMoves :=
        BoundaryPairingMove.prependAllInto
          rest.base.secondMoves head.transition.trace transition.trace
      let base :
          SplayExecutionBoundaryPairingMacro.Certificate
            (params := params) (snapshot := snapshot)
            (.zig step tail tailTranscript) initial start := {
        transition := transition
        finalAtomic := rest.base.finalAtomic
        firstMoves := firstMoves
        secondMoves := secondMoves
        firstSlots_eq := by
          calc
            firstMoves.map BoundaryPairingMove.slot =
                rest.base.firstMoves.map
                  BoundaryPairingMove.slot := by
              simpa only [firstMoves] using
                BoundaryPairingMove.prependAllInto_slots
                  rest.base.firstMoves head.transition.trace
                    transition.trace
            _ = firstPairingsFrom (start + 1) _ :=
              rest.base.firstSlots_eq
            _ = firstPairingsFrom start
                  (SplayStepKind.zig :: _) := by
              simp [firstPairingsFrom, SplayStepKind.isZigZig]
        secondSlots_eq := by
          calc
            secondMoves.map BoundaryPairingMove.slot =
                rest.base.secondMoves.map
                  BoundaryPairingMove.slot := by
              simpa only [secondMoves] using
                BoundaryPairingMove.prependAllInto_slots
                  rest.base.secondMoves head.transition.trace
                    transition.trace
            _ = secondPairingsFrom (start + 1) _ :=
              rest.base.secondSlots_eq
            _ = secondPairingsFrom start
                  (SplayStepKind.zig :: _) := by
              simp [secondPairingsFrom, SplayStepKind.isZigZig]
      }
      exact
        ⟨{
          base := base
          firstEndpointMatches := by
            intro move member
            exact
              BoundaryPairingMove.endpointMatches_prependAllInto
                rest.base.firstMoves head.transition.trace
                  transition.trace rest.firstEndpointMatches
                  move member
          secondEndpointMatches := by
            intro move member
            exact
              BoundaryPairingMove.endpointMatches_prependAllInto
                rest.base.secondMoves head.transition.trace
                  transition.trace rest.secondEndpointMatches
                  move member
        }⟩
  | zigZig step orientation tail tailTranscript =>
      obtain
          ⟨firstWinner, firstLoser, secondWinner, secondLoser,
            firstEndpoints, secondEndpoints, losersNe⟩ :=
        ZigZigPairingEndpointsAt.exists_both_of_orientation
          snapshot orientation (Nat.le_refl n)
      obtain ⟨head⟩ :=
        ZigZigBoundaryPairingMacro.exists_certificate_of_endpoints
          initialRepresents initialAtomic start
          firstEndpoints secondEndpoints losersNe
      let firstOccurrence :=
        occurrenceLift
          (.here step orientation tail tailTranscript) .first
      let secondOccurrence :=
        occurrenceLift
          (.here step orientation tail tailTranscript) .second
      let firstHeapEndpoints :
          PairingSlotHeapEndpoints wholeTranscript snapshot
            { zigZigStep := start + 0, phase := .first } :=
        firstOccurrence.toHeapEndpoints firstEndpoints
      let secondHeapEndpoints :
          PairingSlotHeapEndpoints wholeTranscript snapshot
            { zigZigStep := start + 0, phase := .second } :=
        secondOccurrence.toHeapEndpoints secondEndpoints
      let firstAgreement :
          BoundaryPairingEndpointAgreement wholeTranscript snapshot
            head.firstMove := {
        slot := { zigZigStep := start + 0, phase := .first }
        endpoints := firstHeapEndpoints
        slot_eq := by simpa using head.first_slot
        winner_eq := by
          simpa only [firstHeapEndpoints,
            LiftedPairingSlotOccurrence.toHeapEndpoints_winner] using
              head.first_winner
        loser_eq := by
          simpa only [firstHeapEndpoints,
            LiftedPairingSlotOccurrence.toHeapEndpoints_loser] using
              head.first_loser
      }
      let secondAgreement :
          BoundaryPairingEndpointAgreement wholeTranscript snapshot
            head.secondMove := {
        slot := { zigZigStep := start + 0, phase := .second }
        endpoints := secondHeapEndpoints
        slot_eq := by simpa using head.second_slot
        winner_eq := by
          simpa only [secondHeapEndpoints,
            LiftedPairingSlotOccurrence.toHeapEndpoints_winner] using
              head.second_winner
        loser_eq := by
          simpa only [secondHeapEndpoints,
            LiftedPairingSlotOccurrence.toHeapEndpoints_loser] using
              head.second_loser
      }
      have tailLift :
          ExecutionPairingOccurrenceLift wholeTranscript tailTranscript
            (start + 1) := by
        intro index stepBefore stepAfter depth occurrence phase
        have lifted :=
          occurrenceLift
            (.afterZigZig step orientation tail tailTranscript occurrence)
              phase
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lifted
      obtain ⟨rest⟩ :=
        exists_certificate wholeTranscript tailTranscript
          head.transition.final_represents head.finalAtomic
          (start + 1) tailLift
      let transition :=
        head.transition.trans rest.base.transition
      let localFirst :
          BoundaryPairingMove head.transition.trace :=
        head.firstMove.castTrace head.transition.trace
      let localSecond :
          BoundaryPairingMove head.transition.trace :=
        head.secondMove.castTrace head.transition.trace
      let globalFirst :=
        localFirst.append rest.base.transition.trace
      let globalSecond :=
        localSecond.append rest.base.transition.trace
      let rawFirstMoves :=
        globalFirst ::
          BoundaryPairingMove.prependAll
            rest.base.firstMoves head.transition.trace
      let rawSecondMoves :=
        globalSecond ::
          BoundaryPairingMove.prependAll
            rest.base.secondMoves head.transition.trace
      let firstMoves :=
        BoundaryPairingMove.castAll transition.trace rawFirstMoves
      let secondMoves :=
        BoundaryPairingMove.castAll transition.trace rawSecondMoves
      have firstMovesSlots :
          firstMoves.map BoundaryPairingMove.slot =
            head.firstMove.slot ::
              rest.base.firstMoves.map BoundaryPairingMove.slot := by
        calc
          firstMoves.map BoundaryPairingMove.slot =
              rawFirstMoves.map BoundaryPairingMove.slot := by
            exact
              BoundaryPairingMove.castAll_slots
                transition.trace rawFirstMoves
          _ = head.firstMove.slot ::
                rest.base.firstMoves.map BoundaryPairingMove.slot := by
            simp [rawFirstMoves, globalFirst, localFirst]
      have secondMovesSlots :
          secondMoves.map BoundaryPairingMove.slot =
            head.secondMove.slot ::
              rest.base.secondMoves.map BoundaryPairingMove.slot := by
        calc
          secondMoves.map BoundaryPairingMove.slot =
              rawSecondMoves.map BoundaryPairingMove.slot := by
            exact
              BoundaryPairingMove.castAll_slots
                transition.trace rawSecondMoves
          _ = head.secondMove.slot ::
                rest.base.secondMoves.map BoundaryPairingMove.slot := by
            simp [rawSecondMoves, globalSecond, localSecond]
      let base :
          SplayExecutionBoundaryPairingMacro.Certificate
            (params := params) (snapshot := snapshot)
            (.zigZig step orientation tail tailTranscript)
              initial start := {
        transition := transition
        finalAtomic := rest.base.finalAtomic
        firstMoves := firstMoves
        secondMoves := secondMoves
        firstSlots_eq := by
          calc
            firstMoves.map BoundaryPairingMove.slot =
                head.firstMove.slot ::
                  rest.base.firstMoves.map BoundaryPairingMove.slot :=
              firstMovesSlots
            _ =
                { zigZigStep := start, phase := .first } ::
                  firstPairingsFrom (start + 1) _ := by
              rw [head.first_slot, rest.base.firstSlots_eq]
            _ = firstPairingsFrom start
                  (SplayStepKind.zigZig :: _) := by
              simp [firstPairingsFrom, SplayStepKind.isZigZig]
        secondSlots_eq := by
          calc
            secondMoves.map BoundaryPairingMove.slot =
                head.secondMove.slot ::
                  rest.base.secondMoves.map BoundaryPairingMove.slot :=
              secondMovesSlots
            _ =
                { zigZigStep := start, phase := .second } ::
                  secondPairingsFrom (start + 1) _ := by
              rw [head.second_slot, rest.base.secondSlots_eq]
            _ = secondPairingsFrom start
                  (SplayStepKind.zigZig :: _) := by
              simp [secondPairingsFrom, SplayStepKind.isZigZig]
      }
      have rawFirstMatches :
          ∀ move,
            move ∈ rawFirstMoves →
              Nonempty
                (BoundaryPairingEndpointAgreement
                  wholeTranscript snapshot move) := by
        intro move member
        simp only [rawFirstMoves, List.mem_cons] at member
        rcases member with rfl | member
        · exact
            ⟨(firstAgreement.castTrace head.transition.trace).append
              rest.base.transition.trace⟩
        · exact
            BoundaryPairingMove.endpointMatches_prependAll
              rest.base.firstMoves head.transition.trace
              rest.firstEndpointMatches move member
      have rawSecondMatches :
          ∀ move,
            move ∈ rawSecondMoves →
              Nonempty
                (BoundaryPairingEndpointAgreement
                  wholeTranscript snapshot move) := by
        intro move member
        simp only [rawSecondMoves, List.mem_cons] at member
        rcases member with rfl | member
        · exact
            ⟨(secondAgreement.castTrace head.transition.trace).append
              rest.base.transition.trace⟩
        · exact
            BoundaryPairingMove.endpointMatches_prependAll
              rest.base.secondMoves head.transition.trace
              rest.secondEndpointMatches move member
      exact
        ⟨{
          base := base
          firstEndpointMatches := by
            intro move member
            exact
              BoundaryPairingMove.endpointMatches_castAll
                transition.trace rawFirstMoves rawFirstMatches
                move member
          secondEndpointMatches := by
            intro move member
            exact
              BoundaryPairingMove.endpointMatches_castAll
                transition.trace rawSecondMoves rawSecondMatches
                move member
        }⟩
  | zigZag step orientation tail tailTranscript =>
      obtain ⟨head⟩ :=
        ShiftAtomicStructuralRebase.exists_certificate
          initialRepresents initialAtomic
      have tailLift :
          ExecutionPairingOccurrenceLift wholeTranscript tailTranscript
            (start + 1) := by
        intro index stepBefore stepAfter depth occurrence phase
        have lifted :=
          occurrenceLift
            (.afterZigZag step orientation tail tailTranscript occurrence)
              phase
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lifted
      obtain ⟨rest⟩ :=
        exists_certificate wholeTranscript tailTranscript
          head.transition.final_represents head.finalAtomic
          (start + 1) tailLift
      let transition :=
        head.transition.trans rest.base.transition
      let firstMoves :=
        BoundaryPairingMove.prependAllInto
          rest.base.firstMoves head.transition.trace transition.trace
      let secondMoves :=
        BoundaryPairingMove.prependAllInto
          rest.base.secondMoves head.transition.trace transition.trace
      let base :
          SplayExecutionBoundaryPairingMacro.Certificate
            (params := params) (snapshot := snapshot)
            (.zigZag step orientation tail tailTranscript)
              initial start := {
        transition := transition
        finalAtomic := rest.base.finalAtomic
        firstMoves := firstMoves
        secondMoves := secondMoves
        firstSlots_eq := by
          calc
            firstMoves.map BoundaryPairingMove.slot =
                rest.base.firstMoves.map
                  BoundaryPairingMove.slot := by
              simpa only [firstMoves] using
                BoundaryPairingMove.prependAllInto_slots
                  rest.base.firstMoves head.transition.trace
                    transition.trace
            _ = firstPairingsFrom (start + 1) _ :=
              rest.base.firstSlots_eq
            _ = firstPairingsFrom start
                  (SplayStepKind.zigZag :: _) := by
              simp [firstPairingsFrom, SplayStepKind.isZigZig]
        secondSlots_eq := by
          calc
            secondMoves.map BoundaryPairingMove.slot =
                rest.base.secondMoves.map
                  BoundaryPairingMove.slot := by
              simpa only [secondMoves] using
                BoundaryPairingMove.prependAllInto_slots
                  rest.base.secondMoves head.transition.trace
                    transition.trace
            _ = secondPairingsFrom (start + 1) _ :=
              rest.base.secondSlots_eq
            _ = secondPairingsFrom start
                  (SplayStepKind.zigZag :: _) := by
              simp [secondPairingsFrom, SplayStepKind.isZigZig]
      }
      exact
        ⟨{
          base := base
          firstEndpointMatches := by
            intro move member
            exact
              BoundaryPairingMove.endpointMatches_prependAllInto
                rest.base.firstMoves head.transition.trace
                  transition.trace rest.firstEndpointMatches
                  move member
          secondEndpointMatches := by
            intro move member
            exact
              BoundaryPairingMove.endpointMatches_prependAllInto
                rest.base.secondMoves head.transition.trace
                  transition.trace rest.secondEndpointMatches
                  move member
        }⟩
termination_by kinds.length

end SplayExecutionEndpointAlignedBoundaryPairingMacro

namespace SplaySequenceEndpointAlignedBoundaryPairingMacro

/--
The arbitrary-request boundary macro enriched with canonical endpoint
agreement for every exported move.
-/
structure Certificate
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    (initial : State n) (start : ℕ) where
  base :
    SplaySequenceBoundaryPairingMacro.Certificate
      (params := params) (snapshot := snapshot)
      transcript initial start
  firstEndpointMatches :
    ∀ move,
      move ∈ base.firstMoves →
        Nonempty
          (BoundaryPairingEndpointAgreement
            transcript snapshot move)
  secondEndpointMatches :
    ∀ move,
      move ∈ base.secondMoves →
        Nonempty
          (BoundaryPairingEndpointAgreement
            transcript snapshot move)

/--
General recursive construction into an enclosing sequence transcript.
`occurrenceLift` is what allows recursive suffixes to retain their global
chronological indices.
-/
theorem exists_certificate_of_lift
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {wholeAccesses : List (Fin n)}
    {wholeBefore wholeAfter : BST 0 n}
    {wholeSequence :
      SplaySequence wholeAccesses wholeBefore wholeAfter}
    {wholeKinds : List SplayStepKind}
    {wholeZig wholeZigZig wholeZigZag : ℕ}
    (wholeTranscript :
      SplaySequenceTranscript wholeSequence wholeKinds
        wholeZig wholeZigZig wholeZigZag)
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree)
    (initialAtomic : initial.ShiftAtomic)
    (start : ℕ)
    (occurrenceLift :
      SequencePairingOccurrenceLift wholeTranscript transcript start) :
    ∃ base :
        SplaySequenceBoundaryPairingMacro.Certificate
          (params := params) (snapshot := snapshot)
          transcript initial start,
      (∀ move,
        move ∈ base.firstMoves →
          Nonempty
            (BoundaryPairingEndpointAgreement
              wholeTranscript snapshot move)) ∧
      (∀ move,
        move ∈ base.secondMoves →
          Nonempty
            (BoundaryPairingEndpointAgreement
              wholeTranscript snapshot move)) := by
  cases transcript with
  | done =>
      let transition := RepresentedTransition.refl initialRepresents
      let base :
          SplaySequenceBoundaryPairingMacro.Certificate
            (params := params) (snapshot := snapshot)
            (.done beforeTree) initial start := {
        transition := transition
        finalAtomic := initialAtomic
        firstMoves := []
        secondMoves := []
        firstSlots_eq := by simp [firstPairingsFrom]
        secondSlots_eq := by simp [secondPairingsFrom]
      }
      refine ⟨base, ?_, ?_⟩
      · intro move member
        change move ∈ ([] : List _) at member
        simp at member
      · intro move member
        change move ∈ ([] : List _) at member
        simp at member
  | @next access accesses before middle after
      headKinds tailKinds headZig headZigZig headZigZag
      tailZig tailZigZig tailZigZag
      head tail headTranscript tailTranscript =>
      have headLift :
          ExecutionPairingOccurrenceLift wholeTranscript headTranscript
            start := by
        intro index stepBefore stepAfter depth occurrence phase
        exact
          occurrenceLift
            (.head head tail headTranscript tailTranscript occurrence)
              phase
      obtain ⟨headCertificate⟩ :=
        SplayExecutionEndpointAlignedBoundaryPairingMacro.exists_certificate
          wholeTranscript headTranscript initialRepresents initialAtomic
          start headLift
      have tailLift :
          SequencePairingOccurrenceLift wholeTranscript tailTranscript
            (start + headKinds.length) := by
        intro globalIndex requestIndex selectedAccess requestBefore
          requestAfter localIndex stepBefore stepAfter depth
          occurrence phase
        have lifted :=
          occurrenceLift
            (.tail head tail headTranscript tailTranscript occurrence)
              phase
        simpa [Nat.add_assoc] using lifted
      obtain ⟨tailBase, tailFirstMatches, tailSecondMatches⟩ :=
        exists_certificate_of_lift wholeTranscript tailTranscript
          headCertificate.base.transition.final_represents
          headCertificate.base.finalAtomic
          (start + headKinds.length) tailLift
      let transition :=
        headCertificate.base.transition.trans tailBase.transition
      let firstMoves :=
        BoundaryPairingMove.appendAllInto
            headCertificate.base.firstMoves tailBase.transition.trace
              transition.trace ++
          BoundaryPairingMove.prependAllInto
            tailBase.firstMoves headCertificate.base.transition.trace
              transition.trace
      let secondMoves :=
        BoundaryPairingMove.appendAllInto
            headCertificate.base.secondMoves tailBase.transition.trace
              transition.trace ++
          BoundaryPairingMove.prependAllInto
            tailBase.secondMoves headCertificate.base.transition.trace
              transition.trace
      have firstMatchesLocal :
          ∀ move,
            move ∈ firstMoves →
              Nonempty
                (BoundaryPairingEndpointAgreement
                  wholeTranscript snapshot move) := by
        intro move member
        rw [List.mem_append] at member
        rcases member with headMember | tailMember
        · exact
            BoundaryPairingMove.endpointMatches_appendAllInto
              headCertificate.base.firstMoves tailBase.transition.trace
                transition.trace headCertificate.firstEndpointMatches
                move headMember
        · exact
            BoundaryPairingMove.endpointMatches_prependAllInto
              tailBase.firstMoves headCertificate.base.transition.trace
                transition.trace tailFirstMatches move tailMember
      have secondMatchesLocal :
          ∀ move,
            move ∈ secondMoves →
              Nonempty
                (BoundaryPairingEndpointAgreement
                  wholeTranscript snapshot move) := by
        intro move member
        rw [List.mem_append] at member
        rcases member with headMember | tailMember
        · exact
            BoundaryPairingMove.endpointMatches_appendAllInto
              headCertificate.base.secondMoves tailBase.transition.trace
                transition.trace headCertificate.secondEndpointMatches
                move headMember
        · exact
            BoundaryPairingMove.endpointMatches_prependAllInto
              tailBase.secondMoves headCertificate.base.transition.trace
                transition.trace tailSecondMatches move tailMember
      let base :
          SplaySequenceBoundaryPairingMacro.Certificate
            (params := params) (snapshot := snapshot)
            (.next head tail headTranscript tailTranscript)
              initial start := {
        transition := transition
        finalAtomic := tailBase.finalAtomic
        firstMoves := firstMoves
        secondMoves := secondMoves
        firstSlots_eq := by
          calc
            firstMoves.map BoundaryPairingMove.slot =
                headCertificate.base.firstMoves.map
                    BoundaryPairingMove.slot ++
                  tailBase.firstMoves.map
                    BoundaryPairingMove.slot := by
              simp only [firstMoves, List.map_append,
                BoundaryPairingMove.appendAllInto_slots,
                BoundaryPairingMove.prependAllInto_slots]
            _ = firstPairingsFrom start headKinds ++
                  firstPairingsFrom
                    (start + headKinds.length) tailKinds := by
              rw [headCertificate.base.firstSlots_eq,
                tailBase.firstSlots_eq]
            _ = firstPairingsFrom start
                  (headKinds ++ tailKinds) := by
              rw [firstPairingsFrom_append]
        secondSlots_eq := by
          calc
            secondMoves.map BoundaryPairingMove.slot =
                headCertificate.base.secondMoves.map
                    BoundaryPairingMove.slot ++
                  tailBase.secondMoves.map
                    BoundaryPairingMove.slot := by
              simp only [secondMoves, List.map_append,
                BoundaryPairingMove.appendAllInto_slots,
                BoundaryPairingMove.prependAllInto_slots]
            _ = secondPairingsFrom start headKinds ++
                  secondPairingsFrom
                    (start + headKinds.length) tailKinds := by
              rw [headCertificate.base.secondSlots_eq,
                tailBase.secondSlots_eq]
            _ = secondPairingsFrom start
                  (headKinds ++ tailKinds) := by
              rw [secondPairingsFrom_append]
      }
      exact
        ⟨base,
          by
            dsimp only [base]
            exact firstMatchesLocal,
          by
            dsimp only [base]
            exact secondMatchesLocal⟩
termination_by accesses.length

/--
Every multi-request macro automatically retains endpoint agreement for every
first- and second-phase move.
-/
theorem exists_certificate
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree)
    (initialAtomic : initial.ShiftAtomic) :
    Nonempty
      (Certificate (params := params) (snapshot := snapshot)
        transcript initial 0) := by
  have identityLift :
      SequencePairingOccurrenceLift transcript transcript 0 := by
    intro globalIndex requestIndex access requestBefore requestAfter
      localIndex stepBefore stepAfter depth occurrence phase
    simpa using
      LiftedPairingSlotOccurrence.ofSequenceOccurrence
        occurrence phase
  obtain ⟨base, firstMatches, secondMatches⟩ :=
    exists_certificate_of_lift transcript transcript initialRepresents
      initialAtomic 0 identityLift
  exact
    ⟨{
      base := base
      firstEndpointMatches := firstMatches
      secondEndpointMatches := secondMatches
    }⟩

/--
Atomic initialization followed by the endpoint-enriched multi-request macro
produces a fully automatic initialized cost-sensitive pairing alignment.

There is no endpoint-matching premise: every agreement is inherited from the
exact local zig-zig macro certificate and transported through the recursive
execution and request composition.
-/
theorem exists_atomicInitialized_aligned
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    let initialization :=
      Splay.Lazy.Canonical.atomicInitialization
        snapshot beforeTree params growingLimit valueBound
    ∃ certificate :
        Certificate (params := params) (snapshot := snapshot)
          transcript initialization.final 0,
      let moves :=
        certificate.base.firstMoves ++ certificate.base.secondMoves
      let classification :=
        BoundaryPassPairingClassification.ofInitializedAllImportantSuffix
          (params := params) (snapshot := snapshot)
          (initializedTree := beforeTree)
          transcript initialization certificate.base.transition.trace
          moves
          (by
            simp only [moves, List.map_append]
            rw [certificate.base.firstSlots_eq,
              certificate.base.secondSlots_eq]
            simp)
      Nonempty
        (InitializedCostSensitivePairingAlignment transcript
          initialization classification) := by
  let initialization :=
    Splay.Lazy.Canonical.atomicInitialization
      snapshot beforeTree params growingLimit valueBound
  have initialAtomic : initialization.final.ShiftAtomic :=
    atomicInitialization_final_shiftAtomic
      snapshot beforeTree params growingLimit valueBound
  obtain ⟨certificate⟩ :=
    exists_certificate transcript initialization.final_represents
      initialAtomic
  let moves :=
    certificate.base.firstMoves ++ certificate.base.secondMoves
  have movesSlots :
      moves.map BoundaryPairingMove.slot =
        firstPairings kinds ++ secondPairings kinds := by
    simp only [moves, List.map_append]
    rw [certificate.base.firstSlots_eq,
      certificate.base.secondSlots_eq]
    simp
  have endpointMatches :
      ∀ move,
        move ∈ moves →
          Nonempty
            (BoundaryPairingEndpointAgreement
              transcript snapshot move) := by
    intro move member
    rw [List.mem_append] at member
    rcases member with firstMember | secondMember
    · exact certificate.firstEndpointMatches move firstMember
    · exact certificate.secondEndpointMatches move secondMember
  have aligned :=
    InitializedCostSensitivePairingAlignment.exists_ofInitializedAllImportantSuffix
      (initialization := initialization)
      (transition := certificate.base.transition)
      moves movesSlots endpointMatches
  exact ⟨certificate, aligned⟩

end SplaySequenceEndpointAlignedBoundaryPairingMacro

end Splay.Accounting
