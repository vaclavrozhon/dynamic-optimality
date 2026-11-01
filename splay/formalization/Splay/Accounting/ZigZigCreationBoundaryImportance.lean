import Splay.Accounting.ZigZigBoundaryRequestAdapter
import Splay.Accounting.ShiftAtomicCreationBoundaryImportance

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

namespace ZigZigBoundaryRequestAdapter

/--
The ordinary alignment-to-evidence constructor, strengthened with a
request-start property that must survive its three index substitutions.
-/
def creationEvidenceWithAtomic_of_requestAlignment
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
    (atomic : request.requestInitial.ShiftAtomic)
    (move : BoundaryPairingMove classification.trace)
    (chronology :
      RequestAlignedBoundaryMove endpoint request move)
    (firstLeave : chronology.NoPriorLoserLeave) :
    { evidence :
        CreationBoundaryMoveEvidence provenance classification move //
      evidence.request.requestInitial.ShiftAtomic } := by
  cases chronology.slot_eq
  cases chronology.winner_eq
  cases chronology.loser_eq
  exact
    ⟨{
      endpoint := endpoint
      request := request
      chronology := chronology
      firstLeave := firstLeave
    }, atomic⟩

/--
A lifted macro move reindexed to a classification trace without forgetting
its public slot and endpoint labels.
-/
structure ClassifiedAlignedCreationMove
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
    (lifted : LiftedMove agreement request localMove) : Type where
  move : BoundaryPairingMove classification.trace
  evidence :
    CreationBoundaryMoveEvidence provenance classification move
  requestInitialAtomic : evidence.request.requestInitial.ShiftAtomic
  slot_eq : move.slot = lifted.move.slot
  winner_eq : move.winner = lifted.move.winner
  loser_eq : move.loser = lifted.move.loser

/--
Proof irrelevance of rich traces reindexes the move and its chronology while
preserving all three public labels.
-/
theorem LiftedMove.classifiedAlignedCreationMove_nonempty
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
    (requestAtomic : request.requestInitial.ShiftAtomic)
    (classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events) :
    Nonempty
      (ClassifiedAlignedCreationMove provenance classification lifted) := by
  let Package
      (trace :
        Lazy.Trace params initial transition.events transition.final) :
      Type :=
    Σ move : BoundaryPairingMove trace,
      { chronology :
          RequestAlignedBoundaryMove agreement request move //
        chronology.NoPriorLoserLeave ∧
          move.slot = lifted.move.slot ∧
          move.winner = lifted.move.winner ∧
          move.loser = lifted.move.loser }
  let source : Package lifted.trace :=
    ⟨lifted.move,
      ⟨lifted.alignment, firstLeave, rfl, rfl, rfl⟩⟩
  have traceEq : lifted.trace = classification.trace :=
    Subsingleton.elim _ _
  let target : Package classification.trace := by
    rw [← traceEq]
    exact source
  obtain
      ⟨move, ⟨chronology,
        firstLeave, slotEq, winnerEq, loserEq⟩⟩ :=
    target
  obtain ⟨evidence, evidenceAtomic⟩ :=
    creationEvidenceWithAtomic_of_requestAlignment classification
      agreement request requestAtomic move chronology firstLeave
  exact
    ⟨{
      move := move
      evidence := evidence
      requestInitialAtomic := evidenceAtomic
      slot_eq := slotEq
      winner_eq := winnerEq
      loser_eq := loserEq
    }⟩

namespace ExactRequestCertificate

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

/--
Both phases of an exact shift-atomic request macro, reindexed to an arbitrary
classification trace and certified geometrically important.
-/
structure ClassifiedImportantPair
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser)
    (classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events)
    (cutoff : ℕ) : Type where
  lifted : LiftedPair exact
  first :
    ClassifiedAlignedCreationMove provenance classification lifted.first
  second :
    ClassifiedAlignedCreationMove provenance classification lifted.second
  firstImportant : first.evidence.Important cutoff
  secondImportant : second.evidence.Important cutoff
  first_slot : first.move.slot = exact.firstSlot
  second_slot : second.move.slot = exact.secondSlot
  first_winner : first.move.winner = firstWinner
  first_loser : first.move.loser = firstLoser
  second_winner : second.move.winner = secondWinner
  second_loser : second.move.loser = secondLoser

/--
At every cutoff at least two, both boundary moves generated by an exact
request macro are automatically important: their request-start loser blocks
are shift-atomic singletons.
-/
theorem exists_classifiedImportantPair
    (exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser)
    (classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events)
    {cutoff : ℕ}
    (two_le_cutoff : 2 ≤ cutoff) :
    Nonempty (ClassifiedImportantPair exact classification cutoff) := by
  obtain ⟨lifted⟩ := exact.exists_liftedPair
  obtain ⟨first⟩ :=
    lifted.first.classifiedAlignedCreationMove_nonempty
      lifted.firstNoPrior exact.certificate.initialAtomic classification
  obtain ⟨second⟩ :=
    lifted.second.classifiedAlignedCreationMove_nonempty
      lifted.secondNoPrior exact.certificate.initialAtomic classification
  have firstImportant : first.evidence.Important cutoff :=
    first.evidence.important_of_requestInitial_shiftAtomic
      first.requestInitialAtomic two_le_cutoff
  have secondImportant : second.evidence.Important cutoff :=
    second.evidence.important_of_requestInitial_shiftAtomic
      second.requestInitialAtomic two_le_cutoff
  exact
    ⟨{
      lifted := lifted
      first := first
      second := second
      firstImportant := firstImportant
      secondImportant := secondImportant
      first_slot :=
        first.slot_eq.trans lifted.first.alignment.slot_eq
      second_slot :=
        second.slot_eq.trans lifted.second.alignment.slot_eq
      first_winner :=
        first.winner_eq.trans lifted.first.alignment.winner_eq
      first_loser :=
        first.loser_eq.trans lifted.first.alignment.loser_eq
      second_winner :=
        second.winner_eq.trans lifted.second.alignment.winner_eq
      second_loser :=
        second.loser_eq.trans lifted.second.alignment.loser_eq
    }⟩

/-- Both important moves retain the automatic request-start/delete root ID. -/
theorem ClassifiedImportantPair.first_requestRootSlot_eq_persistentRootSlot
    {exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser}
    {classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events}
    {cutoff : ℕ}
    (pair : ClassifiedImportantPair exact classification cutoff) :
    pair.first.evidence.requestRootSlot =
      classification.persistentRootSlot pair.first.move :=
  pair.first.evidence.requestRootSlot_eq_persistentRootSlot

theorem ClassifiedImportantPair.second_requestRootSlot_eq_persistentRootSlot
    {exact :
      ExactRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser}
    {classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events}
    {cutoff : ℕ}
    (pair : ClassifiedImportantPair exact classification cutoff) :
    pair.second.evidence.requestRootSlot =
      classification.persistentRootSlot pair.second.move :=
  pair.second.evidence.requestRootSlot_eq_persistentRootSlot

end

end ExactRequestCertificate

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

/--
The corresponding important pair for a macro embedded later in a request.
Unlike the exact-request case, request-start atomicity is explicit: the
macro certificate only knows atomicity after its request prefix.
-/
structure ClassifiedImportantPair
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser)
    (classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events)
    (cutoff : ℕ) : Type where
  lifted : LiftedPair embedded
  first :
    ClassifiedAlignedCreationMove provenance classification lifted.first
  second :
    ClassifiedAlignedCreationMove provenance classification lifted.second
  firstImportant : first.evidence.Important cutoff
  secondImportant : second.evidence.Important cutoff
  first_slot : first.move.slot = embedded.firstSlot
  second_slot : second.move.slot = embedded.secondSlot

/--
The embedded macro's two prefix-first-leave assumptions provide chronology;
request-start shift atomicity independently makes both recovered source
intervals important at cutoff at least two.
-/
theorem exists_classifiedImportantPair
    (embedded :
      EmbeddedRequestCertificate zigZigStep firstRealized request
        firstWinner firstLoser secondWinner secondLoser)
    (requestAtomic : request.requestInitial.ShiftAtomic)
    (classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events)
    {cutoff : ℕ}
    (two_le_cutoff : 2 ≤ cutoff) :
    Nonempty (ClassifiedImportantPair embedded classification cutoff) := by
  obtain ⟨lifted⟩ := embedded.exists_liftedPair
  obtain ⟨first⟩ :=
    lifted.first.classifiedAlignedCreationMove_nonempty
      lifted.firstNoPrior requestAtomic classification
  obtain ⟨second⟩ :=
    lifted.second.classifiedAlignedCreationMove_nonempty
      lifted.secondNoPrior requestAtomic classification
  exact
    ⟨{
      lifted := lifted
      first := first
      second := second
      firstImportant :=
        first.evidence.important_of_requestInitial_shiftAtomic
          first.requestInitialAtomic two_le_cutoff
      secondImportant :=
        second.evidence.important_of_requestInitial_shiftAtomic
          second.requestInitialAtomic two_le_cutoff
      first_slot :=
        first.slot_eq.trans lifted.first.alignment.slot_eq
      second_slot :=
        second.slot_eq.trans lifted.second.alignment.slot_eq
    }⟩

end

end EmbeddedRequestCertificate

end ZigZigBoundaryRequestAdapter

end Splay.Accounting
