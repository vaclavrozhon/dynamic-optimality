import Splay.Accounting.PairingEventAlignment
import Splay.Accounting.PersistentBoundaryImportance
import Splay.Interface.LineageElements

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

namespace SplaySequenceTranscript

/-- The complete splay execution selected by a global zig-zig occurrence. -/
theorem ZigZigAt.requestExecution
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {globalIndex requestIndex : ℕ} {access : Fin n}
    {requestBefore requestAfter : BST 0 n}
    {localIndex depth : ℕ} {stepBefore stepAfter : BST 0 n}
    (occurrence :
      ZigZigAt transcript globalIndex requestIndex access
        requestBefore requestAfter localIndex
        stepBefore stepAfter depth) :
    SplayExecution access.val requestBefore requestAfter := by
  induction occurrence with
  | head head =>
      exact head
  | tail _ _ _ _ _ ih =>
      exact ih

/--
The complete represented request containing one chronological zig-zig.

Unlike `RealizedZigZigAt`, this record retains the request boundary itself:
`prefixTransition.final` is the state immediately before the selected splay
request.  The three transition pieces are exact pieces of the same sequence
provenance, rather than an unconstrained event-list factorization.
-/
structure RealizedRequestAt
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
    {globalIndex requestIndex : ℕ} {access : Fin n}
    {requestBefore requestAfter : BST 0 n}
    {localIndex depth : ℕ} {stepBefore stepAfter : BST 0 n}
    (occurrence :
      ZigZigAt transcript globalIndex requestIndex access
        requestBefore requestAfter localIndex
        stepBefore stepAfter depth) : Type where
  prefixTransition :
    RepresentedTransition params
      snapshot beforeTree snapshot requestBefore initial
  requestInitial : State n
  prefix_final_eq : prefixTransition.final = requestInitial
  requestTransition :
    RepresentedTransition params
      snapshot requestBefore snapshot requestAfter requestInitial
  requestProvenance :
    SplayExecution.RepresentedTransitionProvenance
      occurrence.requestExecution
      requestTransition
  suffixTransition :
    RepresentedTransition params
      snapshot requestAfter snapshot afterTree requestTransition.final
  events_eq :
    transition.events =
      prefixTransition.events ++ requestTransition.events ++
        suffixTransition.events
  final_eq : suffixTransition.final = transition.final

namespace RealizedRequestAt

/--
Sequence provenance automatically exposes the complete request containing
the selected zig-zig, including the exact rich state at request start.
-/
theorem exists_of_provenance
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
    {globalIndex requestIndex : ℕ} {access : Fin n}
    {requestBefore requestAfter : BST 0 n}
    {localIndex depth : ℕ} {stepBefore stepAfter : BST 0 n}
    (occurrence :
      ZigZigAt transcript globalIndex requestIndex access
        requestBefore requestAfter localIndex
        stepBefore stepAfter depth) :
    Nonempty (RealizedRequestAt provenance occurrence) := by
  induction occurrence generalizing initial with
  | head head tail headTranscript tailTranscript localOccurrence =>
      cases provenance with
      | next _ _ headTransition tailTransition
          headProvenance tailProvenance =>
          exact
            ⟨{
              prefixTransition :=
                RepresentedTransition.refl
                  headTransition.initial_represents
              requestInitial := initial
              prefix_final_eq := rfl
              requestTransition := headTransition
              requestProvenance := by
                simpa only [ZigZigAt.requestExecution] using
                  headProvenance
              suffixTransition := tailTransition
              events_eq := by
                simp [RepresentedTransition.refl,
                  RepresentedTransition.trans]
              final_eq := rfl
            }⟩
  | tail head tail headTranscript tailTranscript nested ih =>
      cases provenance with
      | next _ _ headTransition tailTransition
          headProvenance tailProvenance =>
          obtain ⟨realized⟩ := ih tailProvenance
          exact
            ⟨{
              prefixTransition :=
                headTransition.trans realized.prefixTransition
              requestInitial := realized.requestInitial
              prefix_final_eq := realized.prefix_final_eq
              requestTransition := realized.requestTransition
              requestProvenance := by
                simpa only [ZigZigAt.requestExecution] using
                  realized.requestProvenance
              suffixTransition := realized.suffixTransition
              events_eq := by
                change
                  headTransition.events ++ tailTransition.events =
                    (headTransition.events ++
                        realized.prefixTransition.events) ++
                      realized.requestTransition.events ++
                        realized.suffixTransition.events
                rw [realized.events_eq]
                simp only [List.append_assoc]
              final_eq := realized.final_eq
            }⟩

end RealizedRequestAt

end SplaySequenceTranscript

/-- Deterministic persistent-root labels at the selected request boundary. -/
def SplaySequenceTranscript.RealizedRequestAt.startLabels
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
    {globalIndex requestIndex : ℕ} {access : Fin n}
    {requestBefore requestAfter : BST 0 n}
    {localIndex depth : ℕ} {stepBefore stepAfter : BST 0 n}
    {occurrence :
      SplaySequenceTranscript.ZigZigAt transcript globalIndex requestIndex
        access requestBefore requestAfter localIndex
        stepBefore stepAfter depth}
    (request :
      SplaySequenceTranscript.RealizedRequestAt provenance occurrence)
    (initialLabels : Interface.RootLabels) :
    Interface.RootLabels :=
  rootLabelsBefore initialLabels
    (Lazy.eraseOperations request.prefixTransition.events)
    (Lazy.eraseOperations request.prefixTransition.events).length

namespace RichTrace

/--
The deterministic root labels and root-lineage phase at the endpoint of a
complete rich trace.  Silent events leave both the interface projection and
the label fold unchanged.
-/
theorem rootLineagePhase_final
    {n : ℕ} {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}
    (trace : Lazy.Trace params initial events final)
    (initialLabels : Interface.RootLabels)
    (initialAligned :
      initialLabels.length = initial.toInterface.blocks.length)
    (initialPhase :
      Interface.RootLineagePhase initial.toInterface initialLabels) :
    let labels :=
      rootLabelsBefore initialLabels
        (Lazy.eraseOperations events)
        (Lazy.eraseOperations events).length
    labels.length = final.toInterface.blocks.length ∧
      Interface.RootLineagePhase final.toInterface labels := by
  induction trace generalizing initialLabels with
  | nil valid =>
      exact ⟨initialAligned, initialPhase⟩
  | @cons before middle after event events head tail ih =>
      cases event with
      | operation operation =>
          have interfaceStep :
              Interface.Step params before.toInterface operation
                middle.toInterface :=
            head.interfaceStep_of_operation
          have middleAligned :
              (Interface.RootLabels.after initialLabels operation).length =
                middle.toInterface.blocks.length :=
            (Interface.HistoryStep.mk interfaceStep rfl).labels_length
              initialAligned
          have middlePhase :
              Interface.RootLineagePhase middle.toInterface
                (Interface.RootLabels.after initialLabels operation) :=
            initialPhase.after_step initialAligned interfaceStep
          simpa [Lazy.eraseOperations, Lazy.Event.operations] using
            ih (Interface.RootLabels.after initialLabels operation)
              middleAligned middlePhase
      | silent =>
          have projectionEq :
              before.toInterface = middle.toInterface :=
            head.projection_eq_of_silent
          have middleAligned :
              initialLabels.length = middle.toInterface.blocks.length := by
            rw [← projectionEq]
            exact initialAligned
          have middlePhase :
              Interface.RootLineagePhase middle.toInterface
                initialLabels := by
            rw [← projectionEq]
            exact initialPhase
          simpa [Lazy.eraseOperations, Lazy.Event.operations] using
            ih initialLabels middleAligned middlePhase

end RichTrace

/--
Whether one visible operation ends the current block-residence episode of a
specified element.  Splits are deliberately excluded: they preserve the
persistent lineage.
-/
def operationLeavesElement {n : ℕ} :
    Interface.Operation n → Interface.Element n → Prop
  | .delete _ deleted, element => deleted = element
  | .pass _ matching, element =>
      element ∈ Interface.pairingLosers matching
  | _, _ => False

namespace HistoryStep

/--
An element stays in the same persistent lineage across every operation that
does not make that element leave.  This is the local transport lemma needed
to connect request-start lineage to a later boundary delete.
-/
theorem mem_lineageElements_after_of_not_leaves
    {n : ℕ} {params : Interface.Parameters}
    {before after : Interface.State n}
    {beforeLabels afterLabels : Interface.RootLabels}
    {operation : Interface.Operation n}
    (historyStep :
      Interface.HistoryStep params before beforeLabels operation
        after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length)
    {root : Interface.RootId} {element : Interface.Element n}
    (member :
      element ∈ Interface.lineageElements before beforeLabels root)
    (notLeaves : ¬ operationLeavesElement operation element) :
    element ∈ Interface.lineageElements after afterLabels root := by
  cases operation with
  | convert blockId =>
      rw [historyStep.lineageElements_convert aligned root]
      exact member
  | create creator =>
      rw [historyStep.lineageElements_create aligned root]
      exact member
  | insert blockId inserted =>
      exact
        (historyStep.mem_lineageElements_insert_iff aligned root).2
          (Or.inl member)
  | delete blockId deleted =>
      apply
        (historyStep.mem_lineageElements_delete_iff aligned root).2
      refine ⟨member, ?_⟩
      simp only [operationLeavesElement] at notLeaves
      by_cases sourceRoot :
          Interface.RootLabels.root? beforeLabels blockId = some root
      · simp [sourceRoot, Ne.symm notLeaves]
      · simp [sourceRoot]
  | pass source matching =>
      apply
        (historyStep.mem_lineageElements_pass_iff aligned root).2
      apply Or.inl
      refine ⟨member, ?_⟩
      unfold Interface.sourceLineageLosers
      simp only [operationLeavesElement] at notLeaves
      split <;> simp_all
  | split source prefixLength =>
      rw [historyStep.lineageElements_split aligned root]
      exact member
  | valueChange changed delta =>
      rw [historyStep.lineageElements_valueChange root]
      exact member

end HistoryStep

namespace RichVisibleStepAt

/--
If an element has not left before a selected visible step, its request-start
persistent root is still its root in the exact pre-state of that step.

The premise examines the actual visible-operation prefix selected by the rich
occurrence.  In particular, it rejects an earlier delete of the element and
an earlier pass in which the element was a loser.
-/
theorem mem_lineageElements_before_of_no_prior_leave
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
    {root : Interface.RootId} {element : Interface.Element n}
    (initialMember :
      element ∈
        Interface.lineageElements initial.toInterface initialLabels root)
    (noPriorLeave :
      ∀ prior,
        prior ∈
            (Lazy.eraseOperations events).take operationIndex →
          ¬ operationLeavesElement prior element) :
    element ∈
      Interface.lineageElements before.toInterface
        (rootLabelsBefore initialLabels
          (Lazy.eraseOperations events) operationIndex)
        root := by
  induction occurrence generalizing initialLabels with
  | head step tail =>
      exact initialMember
  | @visibleTail initial middle final headOperation events
      headStep tailTrace operationIndex eventIndex before after
      operation occurrence ih =>
      have headNotLeaves :
          ¬ operationLeavesElement headOperation element := by
        apply noPriorLeave headOperation
        simp [Lazy.eraseOperations, Lazy.Event.operations]
      have interfaceStep :
          Interface.Step params initial.toInterface headOperation
            middle.toInterface :=
        headStep.interfaceStep_of_operation
      let middleLabels :=
        Interface.RootLabels.after initialLabels headOperation
      have middleAligned :
          middleLabels.length = middle.toInterface.blocks.length :=
        (Interface.HistoryStep.mk interfaceStep rfl).labels_length
          initialAligned
      have middleMember :
          element ∈
            Interface.lineageElements middle.toInterface
              middleLabels root := by
        exact
          HistoryStep.mem_lineageElements_after_of_not_leaves
            (Interface.HistoryStep.mk interfaceStep rfl)
            initialAligned initialMember headNotLeaves
      have tailNoPriorLeave :
          ∀ prior,
            prior ∈
                (Lazy.eraseOperations events).take operationIndex →
              ¬ operationLeavesElement prior element := by
        intro prior member
        apply noPriorLeave prior
        simpa [Lazy.eraseOperations, Lazy.Event.operations] using
          (Or.inr member : prior = headOperation ∨
            prior ∈
              (Lazy.eraseOperations events).take operationIndex)
      simpa [middleLabels, Lazy.eraseOperations,
        Lazy.Event.operations] using
          ih middleLabels middleAligned middleMember tailNoPriorLeave
  | @silentTail initial middle final events headStep tailTrace
      operationIndex eventIndex before after operation occurrence ih =>
      have projectionEq :
          initial.toInterface = middle.toInterface :=
        headStep.projection_eq_of_silent
      have middleAligned :
          initialLabels.length = middle.toInterface.blocks.length := by
        rw [← projectionEq]
        exact initialAligned
      have middleMember :
          element ∈
            Interface.lineageElements middle.toInterface
              initialLabels root := by
        rw [← projectionEq]
        exact initialMember
      have tailNoPriorLeave :
          ∀ prior,
            prior ∈
                (Lazy.eraseOperations events).take operationIndex →
              ¬ operationLeavesElement prior element := by
        intro prior member
        apply noPriorLeave prior
        simpa [Lazy.eraseOperations, Lazy.Event.operations] using member
      simpa [Lazy.eraseOperations, Lazy.Event.operations] using
        ih initialLabels middleAligned middleMember tailNoPriorLeave

end RichVisibleStepAt

/--
The loser block and persistent root at the beginning of the concrete request
containing an endpoint-aligned pairing.

The source is discovered from completeness of the represented request-start
state.  It is not an extra semantic selection: strict endpoint rank order
proves that the loser is not the canonical heap root, so completeness makes
it assigned, and aligned root labels then determine its unique lineage.
-/
structure RequestStartSource
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
    (initialLabels : Interface.RootLabels) : Type where
  labelsAligned :
    (request.startLabels initialLabels).length =
      request.requestInitial.toInterface.blocks.length
  phase :
    Interface.RootLineagePhase request.requestInitial.toInterface
      (request.startLabels initialLabels)
  root : Interface.RootId
  source : Interface.BlockId
  sourceBlock : Interface.Block n
  sourceFound :
    request.requestInitial.toInterface.block? source = some sourceBlock
  sourceRootFound :
    Interface.RootLabels.root?
      (request.startLabels initialLabels) source = some root
  loserMem : loser ∈ sourceBlock.elements

namespace RequestStartSource

/-- Request-start source lineage is automatic from aligned initial labels. -/
theorem exists_of_alignment
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
    (initialLabels : Interface.RootLabels)
    (initialAligned :
      initialLabels.length = initial.toInterface.blocks.length)
    (initialPhase :
      Interface.RootLineagePhase initial.toInterface initialLabels) :
    Nonempty (RequestStartSource agreement request initialLabels) := by
  have prefixFacts :=
    RichTrace.rootLineagePhase_final
      request.prefixTransition.trace initialLabels
        initialAligned initialPhase
  have prefixFactsAtRequest :
      (request.startLabels initialLabels).length =
          request.requestInitial.toInterface.blocks.length ∧
        Interface.RootLineagePhase request.requestInitial.toInterface
          (request.startLabels initialLabels) := by
    unfold SplaySequenceTranscript.RealizedRequestAt.startLabels
    rw [← request.prefix_final_eq]
    exact prefixFacts
  have loserRankPositive : 0 < snapshot.rank loser := by
    have rankLt := agreement.rank_lt
    omega
  have requestRepresents :=
    request.requestTransition.initial_represents
  have loserNotRoot :
      loser ≠ request.requestInitial.view.root := by
    intro loserEq
    have rootRank :
        snapshot.rank request.requestInitial.view.root = 0 := by
      rw [requestRepresents.view_eq]
      exact Canonical.rank_canonicalRoot_eq_zero snapshot _
    rw [loserEq, rootRank] at loserRankPositive
    omega
  have loserAssignedRich :
      loser ∈ request.requestInitial.allElements := by
    apply (requestRepresents.complete loser).2
    exact
      request.requestInitial.view.parent_ne_none_of_ne_root
        loserNotRoot
  have loserAssigned :
      loser ∈ request.requestInitial.toInterface.allElements := by
    simpa only [Lazy.State.toInterface_allElements] using
      loserAssignedRich
  obtain ⟨root, loserInLineage⟩ :=
    (Interface.mem_allElements_iff_exists_lineageElements
      prefixFactsAtRequest.1).mp loserAssigned
  obtain ⟨source, sourceBlock, sourceFound, sourceRootFound,
      loserMem⟩ :=
    (Interface.mem_lineageElements_iff prefixFactsAtRequest.1).mp
      loserInLineage
  exact
    ⟨{
      labelsAligned := prefixFactsAtRequest.1
      phase := prefixFactsAtRequest.2
      root := root
      source := source
      sourceBlock := sourceBlock
      sourceFound := sourceFound
      sourceRootFound := sourceRootFound
      loserMem := loserMem
    }⟩

/-- Canonical request-start source snapshot. -/
noncomputable def ofAlignment
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
    (initialLabels : Interface.RootLabels)
    (initialAligned :
      initialLabels.length = initial.toInterface.blocks.length)
    (initialPhase :
      Interface.RootLineagePhase initial.toInterface initialLabels) :
    RequestStartSource agreement request initialLabels :=
  Classical.choice
    (exists_of_alignment agreement request initialLabels
      initialAligned initialPhase)

end RequestStartSource

/-- Endpoint alignment automatically selects the complete containing request. -/
theorem RealizedPairingEndpointAgreement.realizedRequest_nonempty
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
    Nonempty
      (SplaySequenceTranscript.RealizedRequestAt provenance
        agreement.endpoints.realized.occurrence.occurrence) :=
  SplaySequenceTranscript.RealizedRequestAt.exists_of_provenance
    provenance agreement.endpoints.realized.occurrence.occurrence

/--
Root-label folding at an index inside the middle part of a concatenation.
This is the arithmetic bridge between global operation indices and indices
local to one selected request.
-/
theorem rootLabelsBefore_append_middle
    {n : ℕ} (initialLabels : Interface.RootLabels)
    (beforeOperations middleOperations afterOperations :
      List (Interface.Operation n))
    (index : ℕ) (index_le : index ≤ middleOperations.length) :
    rootLabelsBefore initialLabels
        (beforeOperations ++ middleOperations ++ afterOperations)
        (beforeOperations.length + index) =
      rootLabelsBefore
        (rootLabelsBefore initialLabels beforeOperations
          beforeOperations.length)
        middleOperations index := by
  have prefixMiddleBound :
      beforeOperations.length + index ≤
        (beforeOperations ++ middleOperations).length := by
    simp only [List.length_append]
    omega
  have takePrefixMiddle :
      (beforeOperations ++ middleOperations).take
          (beforeOperations.length + index) =
        beforeOperations ++ middleOperations.take index := by
    rw [List.take_append]
    rw [List.take_of_length_le (by omega)]
    simp
  unfold rootLabelsBefore
  rw [List.take_append_of_le_length prefixMiddleBound]
  rw [takePrefixMiddle, List.foldl_append, List.take_length]

/--
The exact visible placement still missing from endpoint alignment alone.

Both selected boundary operations must occur inside the complete request
containing the pairing slot, and their local indices must agree with their
global indices after adding the exact sequence prefix.  These are
chronological facts; no persistent-root equality is stored here.
-/
structure RequestAlignedBoundaryMove
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
    {moveTrace :
      Lazy.Trace params initial transition.events transition.final}
    (move : BoundaryPairingMove moveTrace) : Type where
  slot_eq : move.slot = slot
  winner_eq : move.winner = winner
  loser_eq : move.loser = loser
  deleteOperationIndex : ℕ
  deleteEventIndex : ℕ
  deleteAtRequest :
    Lazy.Trace.VisibleStepAt request.requestTransition.trace
      deleteOperationIndex deleteEventIndex move.deleteBefore
      (.delete move.source move.loser) move.deleteAfter
  deleteOperationIndex_eq :
    move.deleteOperationIndex =
      (Lazy.eraseOperations request.prefixTransition.events).length +
        deleteOperationIndex
  deleteEventIndex_eq :
    move.deleteEventIndex =
      request.prefixTransition.events.length + deleteEventIndex
  insertOperationIndex : ℕ
  insertEventIndex : ℕ
  insertAtRequest :
    Lazy.Trace.VisibleStepAt request.requestTransition.trace
      insertOperationIndex insertEventIndex move.insertBefore
      (.insert move.destination move.loser) move.insertAfter
  insertOperationIndex_eq :
    move.insertOperationIndex =
      (Lazy.eraseOperations request.prefixTransition.events).length +
        insertOperationIndex
  insertEventIndex_eq :
    move.insertEventIndex =
      request.prefixTransition.events.length + insertEventIndex

namespace RequestAlignedBoundaryMove

/--
The selected delete is the first leave of the loser inside its request.
This is exactly the chronology needed to identify the delete-time lineage
with the original request-start lineage.
-/
def NoPriorLoserLeave
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
    {moveTrace :
      Lazy.Trace params initial transition.events transition.final}
    {move : BoundaryPairingMove moveTrace}
    (alignment :
      RequestAlignedBoundaryMove agreement request move) : Prop :=
  ∀ prior,
    prior ∈
        (Lazy.eraseOperations request.requestTransition.events).take
          alignment.deleteOperationIndex →
      ¬ operationLeavesElement prior move.loser

/-- A boundary delete at local operation index zero is automatically first. -/
theorem noPriorLoserLeave_of_deleteOperationIndex_eq_zero
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
    {moveTrace :
      Lazy.Trace params initial transition.events transition.final}
    {move : BoundaryPairingMove moveTrace}
    (alignment :
      RequestAlignedBoundaryMove agreement request move)
    (indexZero : alignment.deleteOperationIndex = 0) :
    alignment.NoPriorLoserLeave := by
  intro prior member
  rw [indexZero] at member
  simp at member

/--
Under first-leave chronology, the automatically selected request-start root
is definitionally the persistent source root observed at delete time.
-/
theorem request_root_eq_delete_root
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
    {moveTrace :
      Lazy.Trace params initial transition.events transition.final}
    {move : BoundaryPairingMove moveTrace}
    (alignment :
      RequestAlignedBoundaryMove agreement request move)
    (initialLabels : Interface.RootLabels)
    (requestSource :
      RequestStartSource agreement request initialLabels)
    (deleteSource :
      BoundaryPairingMove.PersistentSourceAt initialLabels move)
    (firstLeave : alignment.NoPriorLoserLeave) :
    requestSource.root = deleteSource.root := by
  have requestStartMember :
      move.loser ∈
        Interface.lineageElements request.requestInitial.toInterface
          (request.startLabels initialLabels) requestSource.root := by
    apply
      (Interface.mem_lineageElements_iff
        requestSource.labelsAligned).2
    exact
      ⟨requestSource.source, requestSource.sourceBlock,
        requestSource.sourceFound, requestSource.sourceRootFound,
        by simpa only [alignment.loser_eq] using requestSource.loserMem⟩
  have requestLocalMember :
      move.loser ∈
        Interface.lineageElements move.deleteBefore.toInterface
          (rootLabelsBefore (request.startLabels initialLabels)
            (Lazy.eraseOperations request.requestTransition.events)
            alignment.deleteOperationIndex)
          requestSource.root :=
    RichVisibleStepAt.mem_lineageElements_before_of_no_prior_leave
      alignment.deleteAtRequest
      (request.startLabels initialLabels)
      requestSource.labelsAligned requestStartMember firstLeave
  have operationsEq :
      Lazy.eraseOperations transition.events =
        Lazy.eraseOperations request.prefixTransition.events ++
          Lazy.eraseOperations request.requestTransition.events ++
            Lazy.eraseOperations request.suffixTransition.events := by
    rw [request.events_eq]
    simp only [Lazy.eraseOperations, List.flatMap_append,
      List.append_assoc]
  have localIndexLe :
      alignment.deleteOperationIndex ≤
        (Lazy.eraseOperations
          request.requestTransition.events).length :=
    Nat.le_of_lt alignment.deleteAtRequest.operationIndex_lt
  have labelsEq :
      rootLabelsBefore initialLabels
          (Lazy.eraseOperations transition.events)
          move.deleteOperationIndex =
        rootLabelsBefore (request.startLabels initialLabels)
          (Lazy.eraseOperations request.requestTransition.events)
          alignment.deleteOperationIndex := by
    rw [operationsEq, alignment.deleteOperationIndex_eq]
    exact
      rootLabelsBefore_append_middle initialLabels
        (Lazy.eraseOperations request.prefixTransition.events)
        (Lazy.eraseOperations request.requestTransition.events)
        (Lazy.eraseOperations request.suffixTransition.events)
        alignment.deleteOperationIndex localIndexLe
  have deleteRootMember :
      move.loser ∈
        Interface.lineageElements move.deleteBefore.toInterface
          (rootLabelsBefore initialLabels
            (Lazy.eraseOperations transition.events)
            move.deleteOperationIndex)
          deleteSource.root := by
    apply
      (Interface.mem_lineageElements_iff
        deleteSource.labelsAligned).2
    exact
      ⟨move.source, deleteSource.sourceBlock,
        deleteSource.sourceFound, deleteSource.sourceRootFound,
        deleteSource.loserMem⟩
  have localAligned :
      (rootLabelsBefore (request.startLabels initialLabels)
          (Lazy.eraseOperations request.requestTransition.events)
          alignment.deleteOperationIndex).length =
        move.deleteBefore.toInterface.blocks.length := by
    rw [← labelsEq]
    exact deleteSource.labelsAligned
  have deleteRootMemberLocal :
      move.loser ∈
        Interface.lineageElements move.deleteBefore.toInterface
          (rootLabelsBefore (request.startLabels initialLabels)
            (Lazy.eraseOperations request.requestTransition.events)
            alignment.deleteOperationIndex)
          deleteSource.root := by
    rw [← labelsEq]
    exact deleteRootMember
  exact
    move.deleteAt.toInterface.1.lineage_root_unique localAligned
      requestLocalMember deleteRootMemberLocal

end RequestAlignedBoundaryMove

end Splay.Accounting
