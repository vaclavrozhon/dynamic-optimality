import Splay.Accounting.ZigZigBoundaryPairingMacro
import Splay.Accounting.RequestStartBoundaryLineage
import Splay.Accounting.CreationSideBoundaryImportance

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

namespace ZigZigBoundaryRequestAdapter

/--
First-leave facts compose across an exact prefix/middle factorization.
-/
theorem noLeave_take_prefix_middle
    {α : Type} (leaves : α → Prop)
    (front middle suffix : List α) (index : ℕ)
    (index_le : index ≤ middle.length)
    (prefixNoLeave : ∀ item ∈ front, ¬ leaves item)
    (middleNoLeave :
      ∀ item ∈ middle.take index, ¬ leaves item) :
    ∀ item ∈
        ((front ++ middle) ++ suffix).take (front.length + index),
      ¬ leaves item := by
  intro item member
  have take_eq :
      ((front ++ middle) ++ suffix).take (front.length + index) =
        front ++ middle.take index := by
    simp [List.take_append, index_le]
  rw [take_eq, List.mem_append] at member
  rcases member with inPrefix | inMiddle
  · exact prefixNoLeave item inPrefix
  · exact middleNoLeave item inMiddle

/--
A request-local boundary move lifted through the exact sequence prefix and
suffix retained by `RealizedRequestAt`.

The trace proof is deliberately packaged with the move.  `Lazy.Trace` is a
proposition, but `BoundaryPairingMove` is indexed by its proof; retaining that
proof avoids imposing an artificial equality with `transition.trace`.
-/
structure LiftedMove
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
        slot winner loser)
    (request :
      SplaySequenceTranscript.RealizedRequestAt provenance
        agreement.endpoints.realized.occurrence.occurrence)
    (localMove :
      BoundaryPairingMove request.requestTransition.trace) : Type where
  trace : Lazy.Trace params initial transition.events transition.final
  move : BoundaryPairingMove trace
  alignment : RequestAlignedBoundaryMove agreement request move
  deleteOperationIndex_eq_local :
    alignment.deleteOperationIndex = localMove.deleteOperationIndex
  deleteEventIndex_eq_local :
    alignment.deleteEventIndex = localMove.deleteEventIndex
  insertOperationIndex_eq_local :
    alignment.insertOperationIndex = localMove.insertOperationIndex
  insertEventIndex_eq_local :
    alignment.insertEventIndex = localMove.insertEventIndex

/--
Turn request alignment into the exact endpoint indices required by
`CreationBoundaryMoveEvidence`.

`RequestAlignedBoundaryMove` deliberately permits its endpoint record to use
propositionally equal slot/element indices.  Eliminating those three ordinary
equalities is the only work performed by this constructor.
-/
def creationEvidence_of_requestAlignment
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
    (classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events)
    {slot : PairingSlot}
    {winner loser : Interface.Element n}
    (endpoint :
      RealizedPairingEndpointAgreement transcript provenance
        slot winner loser)
    (request :
      SplaySequenceTranscript.RealizedRequestAt provenance
        endpoint.endpoints.realized.occurrence.occurrence)
    (move : BoundaryPairingMove classification.trace)
    (chronology :
      RequestAlignedBoundaryMove endpoint request move)
    (firstLeave : chronology.NoPriorLoserLeave) :
    CreationBoundaryMoveEvidence provenance classification move := by
  cases chronology.slot_eq
  cases chronology.winner_eq
  cases chronology.loser_eq
  exact {
    endpoint := endpoint
    request := request
    chronology := chronology
    firstLeave := firstLeave
  }

/-- A classified move bundled with its complete creation-side evidence. -/
structure ClassifiedCreationMove
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
        initial transition.final transition.events) : Type where
  move : BoundaryPairingMove classification.trace
  evidence :
    CreationBoundaryMoveEvidence provenance classification move

/--
Any lifted move with first-leave chronology can be reindexed to the trace
proof stored by an arbitrary classification of the same global transition.
-/
theorem LiftedMove.creationEvidence_nonempty
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
    {agreement :
      RealizedPairingEndpointAgreement transcript provenance
        slot winner loser}
    {request :
      SplaySequenceTranscript.RealizedRequestAt provenance
        agreement.endpoints.realized.occurrence.occurrence}
    {localMove :
      BoundaryPairingMove request.requestTransition.trace}
    (lifted : LiftedMove agreement request localMove)
    (firstLeave : lifted.alignment.NoPriorLoserLeave)
    (classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events) :
    Nonempty (ClassifiedCreationMove provenance classification) := by
  let Package
      (trace :
        Lazy.Trace params initial transition.events transition.final) :
      Type :=
    Σ move : BoundaryPairingMove trace,
      { chronology :
          RequestAlignedBoundaryMove agreement request move //
        chronology.NoPriorLoserLeave }
  let source : Package lifted.trace :=
    ⟨lifted.move, ⟨lifted.alignment, firstLeave⟩⟩
  have traceEq : lifted.trace = classification.trace :=
    Subsingleton.elim _ _
  let target : Package classification.trace := by
    rw [← traceEq]
    exact source
  obtain ⟨move, chronology, firstLeave⟩ := target
  exact
    ⟨{
      move := move
      evidence :=
        creationEvidence_of_requestAlignment classification
          agreement request move chronology firstLeave
    }⟩

/--
Lift one move from the complete represented request to the complete sequence.

All index shifts are forced by the exact request prefix.  No chronological
premise is needed here: this theorem only places the already constructed local
delete and insert occurrences in the global trace.
-/
theorem lift_request_move
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
    {agreement :
      RealizedPairingEndpointAgreement transcript provenance
        slot winner loser}
    {request :
      SplaySequenceTranscript.RealizedRequestAt provenance
        agreement.endpoints.realized.occurrence.occurrence}
    (localMove :
      BoundaryPairingMove request.requestTransition.trace)
    (slot_eq : localMove.slot = slot)
    (winner_eq : localMove.winner = winner)
    (loser_eq : localMove.loser = loser) :
    Nonempty (LiftedMove agreement request localMove) := by
  let prefixTrace :
      Lazy.Trace params initial request.prefixTransition.events
        request.requestInitial := by
    rw [← request.prefix_final_eq]
    exact request.prefixTransition.trace
  let prefixedMove := localMove.prepend prefixTrace
  let composedMove := prefixedMove.append request.suffixTransition.trace
  let composedTrace :=
    (prefixTrace.append request.requestTransition.trace).append
      request.suffixTransition.trace
  let Package (events : List (Lazy.Event n)) (final : State n) : Type :=
    PSigma fun trace : Lazy.Trace params initial events final =>
      { move :
          @BoundaryPairingMove n params initial final events trace //
        move.slot = slot ∧
        move.winner = winner ∧
        move.loser = loser ∧
        move.deleteOperationIndex =
          (Lazy.eraseOperations request.prefixTransition.events).length +
            localMove.deleteOperationIndex ∧
        move.deleteEventIndex =
          request.prefixTransition.events.length +
            localMove.deleteEventIndex ∧
        move.insertOperationIndex =
          (Lazy.eraseOperations request.prefixTransition.events).length +
            localMove.insertOperationIndex ∧
        move.insertEventIndex =
          request.prefixTransition.events.length +
            localMove.insertEventIndex ∧
        Lazy.Trace.VisibleStepAt request.requestTransition.trace
          localMove.deleteOperationIndex localMove.deleteEventIndex
          move.deleteBefore (.delete move.source move.loser)
          move.deleteAfter ∧
        Lazy.Trace.VisibleStepAt request.requestTransition.trace
          localMove.insertOperationIndex localMove.insertEventIndex
          move.insertBefore (.insert move.destination move.loser)
          move.insertAfter }
  let packed :
      Package
        (request.prefixTransition.events ++
          request.requestTransition.events ++
            request.suffixTransition.events)
        request.suffixTransition.final := by
    refine ⟨composedTrace, ⟨composedMove, ?_⟩⟩
    constructor
    · simpa [composedMove, prefixedMove] using slot_eq
    constructor
    · change localMove.winner = winner
      exact winner_eq
    constructor
    · change localMove.loser = loser
      exact loser_eq
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · change
        Lazy.Trace.VisibleStepAt request.requestTransition.trace
          localMove.deleteOperationIndex localMove.deleteEventIndex
          localMove.deleteBefore
          (.delete localMove.source localMove.loser)
          localMove.deleteAfter
      exact localMove.deleteAt
    · change
        Lazy.Trace.VisibleStepAt request.requestTransition.trace
          localMove.insertOperationIndex localMove.insertEventIndex
          localMove.insertBefore
          (.insert localMove.destination localMove.loser)
          localMove.insertAfter
      exact localMove.insertAt
  let globalPacked : Package transition.events transition.final := by
    rw [request.events_eq, ← request.final_eq]
    exact packed
  obtain
      ⟨globalTrace,
        ⟨globalMove, global_slot, global_winner, global_loser,
          global_delete_operation, global_delete_event,
          global_insert_operation, global_insert_event,
          global_delete_at, global_insert_at⟩⟩ :=
    globalPacked
  exact
    ⟨{
      trace := globalTrace
      move := globalMove
      alignment := {
        slot_eq := global_slot
        winner_eq := global_winner
        loser_eq := global_loser
        deleteOperationIndex := localMove.deleteOperationIndex
        deleteEventIndex := localMove.deleteEventIndex
        deleteAtRequest := global_delete_at
        deleteOperationIndex_eq := global_delete_operation
        deleteEventIndex_eq := global_delete_event
        insertOperationIndex := localMove.insertOperationIndex
        insertEventIndex := localMove.insertEventIndex
        insertAtRequest := global_insert_at
        insertOperationIndex_eq := global_insert_operation
        insertEventIndex_eq := global_insert_event
      }
      deleteOperationIndex_eq_local := rfl
      deleteEventIndex_eq_local := rfl
      insertOperationIndex_eq_local := rfl
      insertEventIndex_eq_local := rfl
    }⟩

/--
The public move data transported together with a represented request.

Keeping these facts in the same package as the proof-indexed moves is the
minimal dependent-equality interface: transporting only a
`BoundaryPairingMove` would hide its record projections behind a cast.
-/
structure RequestMacroMoves
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {requestBefore requestAfter : BST 0 n}
    (requestInitial : State n)
    (requestTransition :
      RepresentedTransition params
        snapshot requestBefore snapshot requestAfter requestInitial)
    (zigZigStep : ℕ)
    (firstWinner firstLoser secondWinner secondLoser :
      Interface.Element n) : Type where
  firstMove : BoundaryPairingMove requestTransition.trace
  secondMove : BoundaryPairingMove requestTransition.trace
  first_slot :
    firstMove.slot =
      { zigZigStep := zigZigStep, phase := .first }
  second_slot :
    secondMove.slot =
      { zigZigStep := zigZigStep, phase := .second }
  first_winner : firstMove.winner = firstWinner
  first_loser : firstMove.loser = firstLoser
  second_winner : secondMove.winner = secondWinner
  second_loser : secondMove.loser = secondLoser
  first_delete_operation_index :
    firstMove.deleteOperationIndex = 0
  second_no_prior_leave :
    ∀ prior,
      prior ∈
          (Lazy.eraseOperations requestTransition.events).take
            secondMove.deleteOperationIndex →
        ¬ operationLeavesElement prior secondLoser

/-- Two request-local moves whose selected deletes are both first leaves. -/
structure FirstLeaveRequestMoves
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {requestBefore requestAfter : BST 0 n}
    (requestInitial : State n)
    (requestTransition :
      RepresentedTransition params
        snapshot requestBefore snapshot requestAfter requestInitial)
    (zigZigStep : ℕ)
    (firstWinner firstLoser secondWinner secondLoser :
      Interface.Element n) : Type where
  firstMove : BoundaryPairingMove requestTransition.trace
  secondMove : BoundaryPairingMove requestTransition.trace
  first_slot :
    firstMove.slot =
      { zigZigStep := zigZigStep, phase := .first }
  second_slot :
    secondMove.slot =
      { zigZigStep := zigZigStep, phase := .second }
  first_winner : firstMove.winner = firstWinner
  first_loser : firstMove.loser = firstLoser
  second_winner : secondMove.winner = secondWinner
  second_loser : secondMove.loser = secondLoser
  first_no_prior_leave :
    ∀ prior,
      prior ∈
          (Lazy.eraseOperations requestTransition.events).take
            firstMove.deleteOperationIndex →
        ¬ operationLeavesElement prior firstLoser
  second_no_prior_leave :
    ∀ prior,
      prior ∈
          (Lazy.eraseOperations requestTransition.events).take
            secondMove.deleteOperationIndex →
        ¬ operationLeavesElement prior secondLoser

/--
The proof-relevant statement that one two-phase macro is exactly the complete
represented transition of the request selected by a transcript zig-zig.

The certificate itself is indexed by the request boundary trees.  The two
`selected...Endpoints` fields additionally identify its four element labels
with the canonical heap-child endpoints of the selected local zig-zig.  Thus
the wrapper does not equate two dependent endpoint proofs; it shares their
indices and data directly.
-/
structure ExactRequestCertificate
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
    (zigZigStep : ℕ)
    (firstRealized :
      RealizedPairingSlotOccurrence transcript provenance
        { zigZigStep := zigZigStep, phase := .first })
    (request :
      SplaySequenceTranscript.RealizedRequestAt provenance
        firstRealized.occurrence.occurrence)
    (firstWinner firstLoser secondWinner secondLoser :
      Interface.Element n) : Type where
  selectedFirstEndpoints :
    ZigZigPairingEndpointsAt snapshot .first
      (depth := firstRealized.occurrence.depth)
      (key := firstRealized.occurrence.access.val)
      firstRealized.occurrence.stepBefore
      firstRealized.occurrence.stepAfter
      firstWinner firstLoser
  selectedSecondEndpoints :
    ZigZigPairingEndpointsAt snapshot .second
      (depth := firstRealized.occurrence.depth)
      (key := firstRealized.occurrence.access.val)
      firstRealized.occurrence.stepBefore
      firstRealized.occurrence.stepAfter
      secondWinner secondLoser
  certificate :
    ZigZigBoundaryPairingMacro.Certificate
      (params := params) (snapshot := snapshot)
      (beforeTree := firstRealized.occurrence.requestBefore)
      (afterTree := firstRealized.occurrence.requestAfter)
      (depth := firstRealized.occurrence.depth)
      (key := firstRealized.occurrence.access.val)
      request.requestInitial zigZigStep
      firstWinner firstLoser secondWinner secondLoser
  transition_eq :
    certificate.transition = request.requestTransition

namespace ExactRequestCertificate

def firstSlot
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
    {zigZigStep : ℕ}
    {firstRealized :
      RealizedPairingSlotOccurrence transcript provenance
        { zigZigStep := zigZigStep, phase := .first }}
    {request :
      SplaySequenceTranscript.RealizedRequestAt provenance
        firstRealized.occurrence.occurrence}
    {firstWinner firstLoser secondWinner secondLoser :
      Interface.Element n}
    (_exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    PairingSlot :=
  { zigZigStep := zigZigStep, phase := .first }

def secondSlot
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
    {zigZigStep : ℕ}
    {firstRealized :
      RealizedPairingSlotOccurrence transcript provenance
        { zigZigStep := zigZigStep, phase := .first }}
    {request :
      SplaySequenceTranscript.RealizedRequestAt provenance
        firstRealized.occurrence.occurrence}
    {firstWinner firstLoser secondWinner secondLoser :
      Interface.Element n}
    (_exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    PairingSlot :=
  { zigZigStep := zigZigStep, phase := .second }

def secondOccurrence
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
    {zigZigStep : ℕ}
    {firstRealized :
      RealizedPairingSlotOccurrence transcript provenance
        { zigZigStep := zigZigStep, phase := .first }}
    {request :
      SplaySequenceTranscript.RealizedRequestAt provenance
        firstRealized.occurrence.occurrence}
    {firstWinner firstLoser secondWinner secondLoser :
      Interface.Element n}
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    PairingSlotOccurrence transcript exact.secondSlot where
  phase := .second
  phase_eq := rfl
  requestIndex := firstRealized.occurrence.requestIndex
  access := firstRealized.occurrence.access
  requestBefore := firstRealized.occurrence.requestBefore
  requestAfter := firstRealized.occurrence.requestAfter
  localStepIndex := firstRealized.occurrence.localStepIndex
  stepBefore := firstRealized.occurrence.stepBefore
  stepAfter := firstRealized.occurrence.stepAfter
  depth := firstRealized.occurrence.depth
  step := firstRealized.occurrence.step
  orientation := firstRealized.occurrence.orientation
  occurrence := firstRealized.occurrence.occurrence

def secondRealized
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
    {zigZigStep : ℕ}
    {firstRealized :
      RealizedPairingSlotOccurrence transcript provenance
        { zigZigStep := zigZigStep, phase := .first }}
    {request :
      SplaySequenceTranscript.RealizedRequestAt provenance
        firstRealized.occurrence.occurrence}
    {firstWinner firstLoser secondWinner secondLoser :
      Interface.Element n}
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    RealizedPairingSlotOccurrence transcript provenance exact.secondSlot where
  occurrence := exact.secondOccurrence
  realized := firstRealized.realized

section Agreements

variable {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
variable {accesses : List (Fin n)}
variable {beforeTree afterTree : BST 0 n}
variable {sequence : SplaySequence accesses beforeTree afterTree}
variable {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
variable
  {transcript :
    SplaySequenceTranscript sequence kinds zig zigZig zigZag}
variable {initial : State n}
variable
  {transition :
    RepresentedTransition params
      snapshot beforeTree snapshot afterTree initial}
variable
  {provenance :
    SplaySequence.RepresentedTransitionProvenance sequence transition}
variable {zigZigStep : ℕ}
variable
  {firstRealized :
    RealizedPairingSlotOccurrence transcript provenance
      { zigZigStep := zigZigStep, phase := .first }}
variable
  {request :
    SplaySequenceTranscript.RealizedRequestAt provenance
      firstRealized.occurrence.occurrence}
variable
  {firstWinner firstLoser secondWinner secondLoser :
    Interface.Element n}

/-- Endpoint agreement for the first phase, sharing the selected realization. -/
def firstAgreement
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    RealizedPairingEndpointAgreement transcript provenance
      exact.firstSlot firstWinner firstLoser where
  endpoints := {
    realized := firstRealized
    winner := firstWinner
    loser := firstLoser
    endpoints := exact.selectedFirstEndpoints
  }
  winner_eq := rfl
  loser_eq := rfl

/-- Endpoint agreement for the second phase at the same concrete zig-zig. -/
def secondAgreement
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    RealizedPairingEndpointAgreement transcript provenance
      exact.secondSlot secondWinner secondLoser where
  endpoints := {
    realized := exact.secondRealized
    winner := secondWinner
    loser := secondLoser
    endpoints := exact.selectedSecondEndpoints
  }
  winner_eq := rfl
  loser_eq := rfl

/--
Both phase agreements reduce to the same chronological `ZigZigAt`, hence the
same `RealizedRequestAt` witness can be reused without an extra equality.
-/
def secondRequest
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    SplaySequenceTranscript.RealizedRequestAt provenance
      exact.secondAgreement.endpoints.realized.occurrence.occurrence :=
  request

/--
Transport the two moves and all projection facts across the exact transition
equality as one dependent package.
-/
def localMoves
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    RequestMacroMoves request.requestInitial request.requestTransition
      zigZigStep firstWinner firstLoser secondWinner secondLoser := by
  rw [← exact.transition_eq]
  exact {
    firstMove := exact.certificate.firstMove
    secondMove := exact.certificate.secondMove
    first_slot := exact.certificate.first_slot
    second_slot := exact.certificate.second_slot
    first_winner := exact.certificate.first_winner
    first_loser := exact.certificate.first_loser
    second_winner := exact.certificate.second_winner
    second_loser := exact.certificate.second_loser
    first_delete_operation_index :=
      exact.certificate.first_delete_operation_index
    second_no_prior_leave :=
      exact.certificate.secondLoser_no_prior_leave
  }

/-- The first macro move, transported only across transition equality. -/
def firstLocalMove
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    BoundaryPairingMove request.requestTransition.trace :=
  exact.localMoves.firstMove

/-- The second macro move, transported only across transition equality. -/
def secondLocalMove
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    BoundaryPairingMove exact.secondRequest.requestTransition.trace := by
  change BoundaryPairingMove request.requestTransition.trace
  exact exact.localMoves.secondMove

/-- The transition cast preserves all first-move public data. -/
theorem firstLocalMove_slot
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    exact.firstLocalMove.slot = exact.firstSlot := by
  exact exact.localMoves.first_slot

theorem firstLocalMove_winner
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    exact.firstLocalMove.winner = firstWinner := by
  exact exact.localMoves.first_winner

theorem firstLocalMove_loser
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    exact.firstLocalMove.loser = firstLoser := by
  exact exact.localMoves.first_loser

theorem firstLocalMove_deleteOperationIndex
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    exact.firstLocalMove.deleteOperationIndex = 0 := by
  exact exact.localMoves.first_delete_operation_index

/-- The transition cast preserves all second-move public data. -/
theorem secondLocalMove_slot
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    exact.secondLocalMove.slot = exact.secondSlot := by
  exact exact.localMoves.second_slot

theorem secondLocalMove_winner
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    exact.secondLocalMove.winner = secondWinner := by
  exact exact.localMoves.second_winner

theorem secondLocalMove_loser
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    exact.secondLocalMove.loser = secondLoser := by
  exact exact.localMoves.second_loser

/--
The macro's internal first-phase chronology becomes the complete request
chronology because `transition_eq` says that there is no extra request prefix.
-/
theorem secondLocalMove_no_prior_leave
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    ∀ prior,
      prior ∈
          (Lazy.eraseOperations
            exact.secondRequest.requestTransition.events).take
            exact.secondLocalMove.deleteOperationIndex →
        ¬ operationLeavesElement prior secondLoser := by
  intro prior member
  exact exact.localMoves.second_no_prior_leave prior member

/--
Both globally placed moves of an exact request macro, including the
first-leave chronology required by persistent-lineage transport.
-/
structure LiftedPair
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) : Type where
  first :
    LiftedMove exact.firstAgreement request exact.firstLocalMove
  second :
    LiftedMove exact.secondAgreement exact.secondRequest
      exact.secondLocalMove
  firstNoPrior :
    first.alignment.NoPriorLoserLeave
  secondNoPrior :
    second.alignment.NoPriorLoserLeave

/--
An exact request macro automatically yields both `RequestAlignedBoundaryMove`
witnesses and both first-leave proofs.
-/
theorem exists_liftedPair
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    Nonempty (LiftedPair exact) := by
  obtain ⟨first⟩ :=
    lift_request_move
      (agreement := exact.firstAgreement)
      (request := request)
      exact.firstLocalMove
      exact.firstLocalMove_slot
      exact.firstLocalMove_winner
      exact.firstLocalMove_loser
  obtain ⟨second⟩ :=
    lift_request_move
      (agreement := exact.secondAgreement)
      (request := exact.secondRequest)
      exact.secondLocalMove
      exact.secondLocalMove_slot
      exact.secondLocalMove_winner
      exact.secondLocalMove_loser
  have firstIndexZero :
      first.alignment.deleteOperationIndex = 0 :=
    first.deleteOperationIndex_eq_local.trans
      exact.firstLocalMove_deleteOperationIndex
  have firstNoPrior :
      first.alignment.NoPriorLoserLeave :=
    RequestAlignedBoundaryMove.noPriorLoserLeave_of_deleteOperationIndex_eq_zero
      first.alignment firstIndexZero
  have secondNoPrior :
      second.alignment.NoPriorLoserLeave := by
    intro prior member
    rw [second.alignment.loser_eq]
    apply exact.secondLocalMove_no_prior_leave prior
    simpa only [second.deleteOperationIndex_eq_local] using member
  exact
    ⟨{
      first := first
      second := second
      firstNoPrior := firstNoPrior
      secondNoPrior := secondNoPrior
    }⟩

theorem LiftedPair.first_creationEvidence_nonempty
    {exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser}
    (pair : LiftedPair exact)
    (classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events) :
    Nonempty (ClassifiedCreationMove provenance classification) :=
  pair.first.creationEvidence_nonempty pair.firstNoPrior classification

theorem LiftedPair.second_creationEvidence_nonempty
    {exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser}
    (pair : LiftedPair exact)
    (classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events) :
    Nonempty (ClassifiedCreationMove provenance classification) :=
  pair.second.creationEvidence_nonempty pair.secondNoPrior classification

end Agreements

end ExactRequestCertificate

/--
A two-phase macro occurring as the selected zig-zig segment inside a larger
request.

All structural placement is expressed by an exact transition factorization.
The only semantic assumptions are the two `prefixNoLeave` fields: neither
selected loser has already left before the macro segment begins.
-/
structure EmbeddedRequestCertificate
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
    (zigZigStep : ℕ)
    (firstRealized :
      RealizedPairingSlotOccurrence transcript provenance
        { zigZigStep := zigZigStep, phase := .first })
    (request :
      SplaySequenceTranscript.RealizedRequestAt provenance
        firstRealized.occurrence.occurrence)
    (firstWinner firstLoser secondWinner secondLoser :
      Interface.Element n) : Type where
  prefixTransition :
    RepresentedTransition params snapshot
      firstRealized.occurrence.requestBefore snapshot
      firstRealized.occurrence.stepBefore request.requestInitial
  certificate :
    ZigZigBoundaryPairingMacro.Certificate
      (params := params) (snapshot := snapshot)
      (beforeTree := firstRealized.occurrence.stepBefore)
      (afterTree := firstRealized.occurrence.stepAfter)
      (depth := firstRealized.occurrence.depth)
      (key := firstRealized.occurrence.access.val)
      prefixTransition.final zigZigStep
      firstWinner firstLoser secondWinner secondLoser
  suffixTransition :
    RepresentedTransition params snapshot
      firstRealized.occurrence.stepAfter snapshot
      firstRealized.occurrence.requestAfter certificate.transition.final
  transition_eq :
    (prefixTransition.trans certificate.transition).trans
        suffixTransition =
      request.requestTransition
  firstPrefixNoLeave :
    ∀ operation,
      operation ∈ Lazy.eraseOperations prefixTransition.events →
        ¬ operationLeavesElement operation firstLoser
  secondPrefixNoLeave :
    ∀ operation,
      operation ∈ Lazy.eraseOperations prefixTransition.events →
        ¬ operationLeavesElement operation secondLoser

namespace EmbeddedRequestCertificate

section

variable {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
variable {accesses : List (Fin n)}
variable {beforeTree afterTree : BST 0 n}
variable {sequence : SplaySequence accesses beforeTree afterTree}
variable {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
variable
  {transcript :
    SplaySequenceTranscript sequence kinds zig zigZig zigZag}
variable {initial : State n}
variable
  {transition :
    RepresentedTransition params
      snapshot beforeTree snapshot afterTree initial}
variable
  {provenance :
    SplaySequence.RepresentedTransitionProvenance sequence transition}
variable {zigZigStep : ℕ}
variable
  {firstRealized :
    RealizedPairingSlotOccurrence transcript provenance
      { zigZigStep := zigZigStep, phase := .first }}
variable
  {request :
    SplaySequenceTranscript.RealizedRequestAt provenance
      firstRealized.occurrence.occurrence}
variable
  {firstWinner firstLoser secondWinner secondLoser :
    Interface.Element n}

def firstSlot
    (_embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    PairingSlot :=
  { zigZigStep := zigZigStep, phase := .first }

def secondSlot
    (_embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    PairingSlot :=
  { zigZigStep := zigZigStep, phase := .second }

def secondOccurrence
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    PairingSlotOccurrence transcript embedded.secondSlot where
  phase := .second
  phase_eq := rfl
  requestIndex := firstRealized.occurrence.requestIndex
  access := firstRealized.occurrence.access
  requestBefore := firstRealized.occurrence.requestBefore
  requestAfter := firstRealized.occurrence.requestAfter
  localStepIndex := firstRealized.occurrence.localStepIndex
  stepBefore := firstRealized.occurrence.stepBefore
  stepAfter := firstRealized.occurrence.stepAfter
  depth := firstRealized.occurrence.depth
  step := firstRealized.occurrence.step
  orientation := firstRealized.occurrence.orientation
  occurrence := firstRealized.occurrence.occurrence

def secondRealized
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    RealizedPairingSlotOccurrence transcript provenance
      embedded.secondSlot where
  occurrence := embedded.secondOccurrence
  realized := firstRealized.realized

def firstAgreement
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    RealizedPairingEndpointAgreement transcript provenance
      embedded.firstSlot firstWinner firstLoser where
  endpoints := {
    realized := firstRealized
    winner := firstWinner
    loser := firstLoser
    endpoints := embedded.certificate.firstEndpoints
  }
  winner_eq := rfl
  loser_eq := rfl

def secondAgreement
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    RealizedPairingEndpointAgreement transcript provenance
      embedded.secondSlot secondWinner secondLoser where
  endpoints := {
    realized := embedded.secondRealized
    winner := secondWinner
    loser := secondLoser
    endpoints := embedded.certificate.secondEndpoints
  }
  winner_eq := rfl
  loser_eq := rfl

def secondRequest
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    SplaySequenceTranscript.RealizedRequestAt provenance
      embedded.secondAgreement.endpoints.realized.occurrence.occurrence :=
  request

/-- The exact request transition assembled from prefix, macro, and suffix. -/
def composedTransition
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    RepresentedTransition params snapshot
      firstRealized.occurrence.requestBefore snapshot
      firstRealized.occurrence.requestAfter request.requestInitial :=
  (embedded.prefixTransition.trans embedded.certificate.transition).trans
    embedded.suffixTransition

/--
Both macro moves transported into the complete request, with first-leave
chronology derived solely from the two prefix invariants.
-/
def localMoves
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    FirstLeaveRequestMoves request.requestInitial request.requestTransition
      zigZigStep firstWinner firstLoser secondWinner secondLoser := by
  let firstMove :=
    (embedded.certificate.firstMove.prepend
      embedded.prefixTransition.trace).append
        embedded.suffixTransition.trace
  let secondMove :=
    (embedded.certificate.secondMove.prepend
      embedded.prefixTransition.trace).append
        embedded.suffixTransition.trace
  let frontOps :=
    Lazy.eraseOperations embedded.prefixTransition.events
  let middleOps :=
    Lazy.eraseOperations embedded.certificate.transition.events
  let suffixOps :=
    Lazy.eraseOperations embedded.suffixTransition.events
  have firstMiddleNoLeave :
      ∀ operation ∈
          middleOps.take
            embedded.certificate.firstMove.deleteOperationIndex,
        ¬ operationLeavesElement operation firstLoser := by
    intro operation member
    rw [embedded.certificate.first_delete_operation_index] at member
    simp at member
  have firstIndexLe :
      embedded.certificate.firstMove.deleteOperationIndex ≤
        middleOps.length :=
    Nat.le_of_lt
      embedded.certificate.firstMove.deleteAt.operationIndex_lt
  have secondIndexLe :
      embedded.certificate.secondMove.deleteOperationIndex ≤
        middleOps.length :=
    Nat.le_of_lt
      embedded.certificate.secondMove.deleteAt.operationIndex_lt
  have composedOperationsEq :
      Lazy.eraseOperations embedded.composedTransition.events =
        (frontOps ++ middleOps) ++ suffixOps := by
    change
      Lazy.eraseOperations
          ((embedded.prefixTransition.events ++
              embedded.certificate.transition.events) ++
            embedded.suffixTransition.events) =
        (frontOps ++ middleOps) ++ suffixOps
    rw [eraseOperations_append, eraseOperations_append]
  let raw :
      FirstLeaveRequestMoves request.requestInitial
        embedded.composedTransition zigZigStep
        firstWinner firstLoser secondWinner secondLoser := by
    refine {
      firstMove := firstMove
      secondMove := secondMove
      first_slot := ?_
      second_slot := ?_
      first_winner := ?_
      first_loser := ?_
      second_winner := ?_
      second_loser := ?_
      first_no_prior_leave := ?_
      second_no_prior_leave := ?_
    }
    · change
        embedded.certificate.firstMove.slot =
          { zigZigStep := zigZigStep, phase := .first }
      exact embedded.certificate.first_slot
    · change
        embedded.certificate.secondMove.slot =
          { zigZigStep := zigZigStep, phase := .second }
      exact embedded.certificate.second_slot
    · change embedded.certificate.firstMove.winner = firstWinner
      exact embedded.certificate.first_winner
    · change embedded.certificate.firstMove.loser = firstLoser
      exact embedded.certificate.first_loser
    · change embedded.certificate.secondMove.winner = secondWinner
      exact embedded.certificate.second_winner
    · change embedded.certificate.secondMove.loser = secondLoser
      exact embedded.certificate.second_loser
    · intro prior member
      apply
        noLeave_take_prefix_middle
          (fun operation =>
            operationLeavesElement operation firstLoser)
          frontOps middleOps suffixOps
          embedded.certificate.firstMove.deleteOperationIndex
          firstIndexLe embedded.firstPrefixNoLeave
          firstMiddleNoLeave prior
      dsimp [firstMove] at member
      simp only [BoundaryPairingMove.append,
        BoundaryPairingMove.prepend] at member
      rw [composedOperationsEq] at member
      change
        prior ∈
          ((frontOps ++ middleOps) ++ suffixOps).take
            (frontOps.length +
              embedded.certificate.firstMove.deleteOperationIndex)
        at member
      exact member
    · intro prior member
      apply
        noLeave_take_prefix_middle
          (fun operation =>
            operationLeavesElement operation secondLoser)
          frontOps middleOps suffixOps
          embedded.certificate.secondMove.deleteOperationIndex
          secondIndexLe embedded.secondPrefixNoLeave
          embedded.certificate.secondLoser_no_prior_leave prior
      dsimp [secondMove] at member
      simp only [BoundaryPairingMove.append,
        BoundaryPairingMove.prepend] at member
      rw [composedOperationsEq] at member
      change
        prior ∈
          ((frontOps ++ middleOps) ++ suffixOps).take
            (frontOps.length +
              embedded.certificate.secondMove.deleteOperationIndex)
        at member
      exact member
  rw [← embedded.transition_eq]
  exact raw

def firstLocalMove
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    BoundaryPairingMove request.requestTransition.trace :=
  embedded.localMoves.firstMove

def secondLocalMove
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    BoundaryPairingMove embedded.secondRequest.requestTransition.trace := by
  change BoundaryPairingMove request.requestTransition.trace
  exact embedded.localMoves.secondMove

theorem firstLocalMove_slot
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    embedded.firstLocalMove.slot = embedded.firstSlot :=
  embedded.localMoves.first_slot

theorem firstLocalMove_winner
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    embedded.firstLocalMove.winner = firstWinner :=
  embedded.localMoves.first_winner

theorem firstLocalMove_loser
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    embedded.firstLocalMove.loser = firstLoser :=
  embedded.localMoves.first_loser

theorem secondLocalMove_slot
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    embedded.secondLocalMove.slot = embedded.secondSlot :=
  embedded.localMoves.second_slot

theorem secondLocalMove_winner
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    embedded.secondLocalMove.winner = secondWinner :=
  embedded.localMoves.second_winner

theorem secondLocalMove_loser
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    embedded.secondLocalMove.loser = secondLoser :=
  embedded.localMoves.second_loser

structure LiftedPair
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) : Type where
  first :
    LiftedMove embedded.firstAgreement request embedded.firstLocalMove
  second :
    LiftedMove embedded.secondAgreement embedded.secondRequest
      embedded.secondLocalMove
  firstNoPrior :
    first.alignment.NoPriorLoserLeave
  secondNoPrior :
    second.alignment.NoPriorLoserLeave

/--
The embedded macro yields both global request alignments.  No chronology
premise remains beyond the two prefix invariants stored in `embedded`.
-/
theorem exists_liftedPair
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser) :
    Nonempty (LiftedPair embedded) := by
  obtain ⟨first⟩ :=
    lift_request_move
      (agreement := embedded.firstAgreement)
      (request := request)
      embedded.firstLocalMove
      embedded.firstLocalMove_slot
      embedded.firstLocalMove_winner
      embedded.firstLocalMove_loser
  obtain ⟨second⟩ :=
    lift_request_move
      (agreement := embedded.secondAgreement)
      (request := embedded.secondRequest)
      embedded.secondLocalMove
      embedded.secondLocalMove_slot
      embedded.secondLocalMove_winner
      embedded.secondLocalMove_loser
  have firstNoPrior :
      first.alignment.NoPriorLoserLeave := by
    intro prior member
    rw [first.alignment.loser_eq]
    apply embedded.localMoves.first_no_prior_leave prior
    rw [first.deleteOperationIndex_eq_local] at member
    change
      prior ∈
        (Lazy.eraseOperations request.requestTransition.events).take
          embedded.localMoves.firstMove.deleteOperationIndex
      at member
    exact member
  have secondNoPrior :
      second.alignment.NoPriorLoserLeave := by
    intro prior member
    rw [second.alignment.loser_eq]
    apply embedded.localMoves.second_no_prior_leave prior
    rw [second.deleteOperationIndex_eq_local] at member
    change
      prior ∈
        (Lazy.eraseOperations request.requestTransition.events).take
          embedded.localMoves.secondMove.deleteOperationIndex
      at member
    exact member
  exact
    ⟨{
      first := first
      second := second
      firstNoPrior := firstNoPrior
      secondNoPrior := secondNoPrior
    }⟩

theorem LiftedPair.first_creationEvidence_nonempty
    {embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser}
    (pair : LiftedPair embedded)
    (classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events) :
    Nonempty (ClassifiedCreationMove provenance classification) :=
  pair.first.creationEvidence_nonempty pair.firstNoPrior classification

theorem LiftedPair.second_creationEvidence_nonempty
    {embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser}
    (pair : LiftedPair embedded)
    (classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events) :
    Nonempty (ClassifiedCreationMove provenance classification) :=
  pair.second.creationEvidence_nonempty pair.secondNoPrior classification

end

end EmbeddedRequestCertificate

end ZigZigBoundaryRequestAdapter

end Splay.Accounting
