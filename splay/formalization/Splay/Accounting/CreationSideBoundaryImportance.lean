import Splay.Accounting.CanonicalCrossSideUnbroken

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

/--
All proof-relevant data connecting one classified boundary move to the
original loser interval at the start of its concrete request.

Endpoint geometry, the containing request, and the request-start source are
automatic.  The two genuinely cost-sensitive chronology facts retained here
are that the chosen delete/insert occur inside that request and that the
chosen delete is the loser's first leave in the request.
-/
structure CreationBoundaryMoveEvidence
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
    (move : BoundaryPairingMove classification.trace) : Type where
  endpoint :
    RealizedPairingEndpointAgreement transcript provenance
      move.slot move.winner move.loser
  request :
    SplaySequenceTranscript.RealizedRequestAt provenance
      endpoint.endpoints.realized.occurrence.occurrence
  chronology :
    RequestAlignedBoundaryMove endpoint request move
  firstLeave : chronology.NoPriorLoserLeave

namespace CreationBoundaryMoveEvidence

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
    {move : BoundaryPairingMove classification.trace}

/-- The automatic original loser interval at request start. -/
noncomputable def requestSource
    (evidence :
      CreationBoundaryMoveEvidence provenance classification move) :
    RequestStartSource evidence.endpoint evidence.request [] :=
  RequestStartSource.ofAlignment evidence.endpoint evidence.request []
    (by
      simpa [Lazy.State.toInterface] using
        congrArg List.length
          classification.passClassification.initialState.2.symm)
    (Interface.RootLineagePhase.initial
      classification.passClassification.initialState)

/-- The already automatic persistent source snapshot at the selected delete. -/
noncomputable def deleteSource
    (_evidence :
      CreationBoundaryMoveEvidence provenance classification move) :
    BoundaryPairingMove.PersistentSourceAt [] move :=
  classification.persistentSourceAt move

/--
The creation-side root and the delete-time persistent root are equal; the
equality is derived from first-leave chronology, not stored in the evidence.
-/
theorem requestSource_root_eq_deleteSource_root
    (evidence :
      CreationBoundaryMoveEvidence provenance classification move) :
    evidence.requestSource.root = evidence.deleteSource.root :=
  evidence.chronology.request_root_eq_delete_root []
    evidence.requestSource evidence.deleteSource evidence.firstLeave

/-- The original request-start root remains an in-range final block ID. -/
theorem requestSource_root_lt_final
    (evidence :
      CreationBoundaryMoveEvidence provenance classification move) :
    evidence.requestSource.root < transition.final.blocks.length := by
  rw [evidence.requestSource_root_eq_deleteSource_root]
  exact evidence.deleteSource.root_lt_final

/--
The request-start source block identifier remains an in-range slot at the
final endpoint.  Block storage is append-only: a split may empty this source
and append descendants, but it never removes or renumbers the original lazy
interval identity.  This is the stable fiber used by the manuscript's
per-interval important-pairing count.
-/
theorem requestSource_source_lt_final
    (evidence :
      CreationBoundaryMoveEvidence provenance classification move) :
    evidence.requestSource.source < transition.final.blocks.length := by
  have sourceLtRequest :
      evidence.requestSource.source <
        evidence.request.requestInitial.toInterface.blocks.length :=
    (List.getElem?_eq_some_iff.mp
      evidence.requestSource.sourceFound).1
  have requestCount :=
    evidence.request.requestTransition.trace.toInterface.blocks_length_eq
  have suffixCount :=
    evidence.request.suffixTransition.trace.toInterface.blocks_length_eq
  have requestLe :
      evidence.request.requestInitial.toInterface.blocks.length ≤
        evidence.request.requestTransition.final.toInterface.blocks.length := by
    omega
  have suffixLe :
      evidence.request.requestTransition.final.toInterface.blocks.length ≤
        evidence.request.suffixTransition.final.toInterface.blocks.length := by
    omega
  have sourceLtSuffix :
      evidence.requestSource.source <
        evidence.request.suffixTransition.final.toInterface.blocks.length :=
    sourceLtRequest.trans_le (requestLe.trans suffixLe)
  rw [evidence.request.final_eq] at sourceLtSuffix
  simpa [Lazy.State.toInterface] using sourceLtSuffix

/-- Final-state slot of the original request-start lineage. -/
noncomputable def requestRootSlot
    (evidence :
      CreationBoundaryMoveEvidence provenance classification move) :
    Fin transition.final.blocks.length :=
  ⟨evidence.requestSource.root, evidence.requestSource_root_lt_final⟩

/-- Final-state slot occupied by the original request-start lazy interval. -/
noncomputable def requestSourceSlot
    (evidence :
      CreationBoundaryMoveEvidence provenance classification move) :
    Fin transition.final.blocks.length :=
  ⟨evidence.requestSource.source, evidence.requestSource_source_lt_final⟩

/-- Creation-side and delete-time root slots are the same stable ID. -/
theorem requestRootSlot_eq_persistentRootSlot
    (evidence :
      CreationBoundaryMoveEvidence provenance classification move) :
    evidence.requestRootSlot =
      classification.persistentRootSlot move := by
  apply Fin.ext
  exact evidence.requestSource_root_eq_deleteSource_root

/-- Geometric unimportance of this move's original loser interval. -/
def Unimportant
    (evidence :
      CreationBoundaryMoveEvidence provenance classification move)
    (cutoff : ℕ) : Prop :=
  evidence.requestSource.Unimportant cutoff

/-- Geometric importance is the exact complement. -/
def Important
    (evidence :
      CreationBoundaryMoveEvidence provenance classification move)
    (cutoff : ℕ) : Prop :=
  evidence.requestSource.Important cutoff

end CreationBoundaryMoveEvidence

/--
Creation-side interpretation of both boundary labels.

There is no state/root-indexed `unbrokenAt` parameter.  Every occurrence is
interpreted in the canonical full top-down geometry of its concrete
request-start tree, using the automatically recovered original loser block.
-/
structure CreationSideBoundaryImportance
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
    (cutoff : ℕ) : Prop where
  important_spec :
    ∀ move ∈ classification.importantMoves,
      ∃ evidence :
          CreationBoundaryMoveEvidence provenance classification move,
        evidence.Important cutoff
  unimportant_spec :
    ∀ move ∈ classification.unimportantMoves,
      ∃ evidence :
          CreationBoundaryMoveEvidence provenance classification move,
        evidence.Unimportant cutoff

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
For an important move, endpoint alignment automatically constructs the
containing request and its original loser interval.  Only in-request
delete/insert chronology remains to form `CreationBoundaryMoveEvidence`.
-/
theorem important_creation_prefix_nonempty
    (alignment :
      CostSensitivePairingAlignment transcript provenance classification)
    (move : BoundaryPairingMove classification.trace)
    (member : move ∈ classification.importantMoves) :
    Nonempty
      (Σ endpoint :
          RealizedPairingEndpointAgreement transcript provenance
            move.slot move.winner move.loser,
        Σ request :
            SplaySequenceTranscript.RealizedRequestAt provenance
              endpoint.endpoints.realized.occurrence.occurrence,
          RequestStartSource endpoint request []) := by
  obtain ⟨endpoint⟩ := alignment.important move member
  obtain ⟨request⟩ := endpoint.realizedRequest_nonempty
  exact
    ⟨⟨endpoint, request,
      RequestStartSource.ofAlignment endpoint request []
        (by
          simpa [Lazy.State.toInterface] using
            congrArg List.length
              classification.passClassification.initialState.2.symm)
        (Interface.RootLineagePhase.initial
          classification.passClassification.initialState)⟩⟩

/-- The same automatic creation-side prefix for an unimportant move. -/
theorem unimportant_creation_prefix_nonempty
    (alignment :
      CostSensitivePairingAlignment transcript provenance classification)
    (move : BoundaryPairingMove classification.trace)
    (member : move ∈ classification.unimportantMoves) :
    Nonempty
      (Σ endpoint :
          RealizedPairingEndpointAgreement transcript provenance
            move.slot move.winner move.loser,
        Σ request :
            SplaySequenceTranscript.RealizedRequestAt provenance
              endpoint.endpoints.realized.occurrence.occurrence,
          RequestStartSource endpoint request []) := by
  obtain ⟨endpoint⟩ := alignment.unimportant move member
  obtain ⟨request⟩ := endpoint.realizedRequest_nonempty
  exact
    ⟨⟨endpoint, request,
      RequestStartSource.ofAlignment endpoint request []
        (by
          simpa [Lazy.State.toInterface] using
            congrArg List.length
              classification.passClassification.initialState.2.symm)
        (Interface.RootLineagePhase.initial
          classification.passClassification.initialState)⟩⟩

end CostSensitivePairingAlignment

end Splay.Accounting
