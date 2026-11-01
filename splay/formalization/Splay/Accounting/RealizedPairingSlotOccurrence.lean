import Splay.Accounting.PairingSlotOccurrence
import Splay.Accounting.SplayExecutionProvenance

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

namespace SplayExecutionTranscript

/--
An exact rich-event segment realizing the concrete zig-zig selected by a
chronological transcript occurrence.

The prefix and suffix equation places the segment inside the event list of
the represented transition for the complete splay.  The segment provenance
then decomposes it into the two ordinary rotations of the same concrete
`DoubleRotationAt`.  No claim is made yet that either segment contains the
manuscript's visible pairing operations.
-/
structure RealizedZigZigAt
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {key : ℕ} {beforeTree afterTree : BST 0 n}
    {execution : SplayExecution key beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {initial : State n}
    {transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial}
    (provenance :
      SplayExecution.RepresentedTransitionProvenance
        execution transition)
    {index depth : ℕ} {stepBefore stepAfter : BST 0 n}
    (occurrence :
      ZigZigAt transcript index stepBefore stepAfter depth) : Type where
  segmentInitial : State n
  segmentTransition :
    RepresentedTransition params
      snapshot stepBefore snapshot stepAfter segmentInitial
  segmentProvenance :
    SplayStep.RepresentedTransitionProvenance
      (.double occurrence.geometry.1) segmentTransition
  prefixEvents : List (Event n)
  suffixEvents : List (Event n)
  events_eq :
    transition.events =
      prefixEvents ++ segmentTransition.events ++ suffixEvents

namespace RealizedZigZigAt

/--
Stepwise transition provenance places every concrete transcript zig-zig at
one exact contiguous event segment of the complete represented transition.
-/
theorem exists_of_provenance
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {key : ℕ} {beforeTree afterTree : BST 0 n}
    {execution : SplayExecution key beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    {initial : State n}
    {transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial}
    (provenance :
      SplayExecution.RepresentedTransitionProvenance
        execution transition)
    {index depth : ℕ} {stepBefore stepAfter : BST 0 n}
    (occurrence :
      ZigZigAt transcript index stepBefore stepAfter depth) :
    Nonempty (RealizedZigZigAt provenance occurrence) := by
  induction provenance generalizing
      kinds zig zigZig zigZag index depth stepBefore stepAfter with
  | done root initialRepresents =>
      cases transcript with
      | done =>
          cases occurrence
      | zig head tail tailTranscript =>
          have rootDepth := depth_eq_zero_of_hasRoot root
          have headDepth := head.depth_before_eq_one
          omega
      | zigZig head orientation tail tailTranscript =>
          have rootDepth := depth_eq_zero_of_hasRoot root
          have headDepth := head.depth_before_eq
          omega
      | zigZag head orientation tail tailTranscript =>
          have rootDepth := depth_eq_zero_of_hasRoot root
          have headDepth := head.depth_before_eq
          omega
  | @next beforeTree middleTree afterTree head tail initial
      headTransition tailTransition headProvenance tailProvenance ih =>
      cases head with
      | zig provenanceHead =>
          cases transcript with
          | done transcriptRoot =>
              have rootDepth :=
                depth_eq_zero_of_hasRoot transcriptRoot
              have headDepth := provenanceHead.depth_before_eq_one
              omega
          | zig transcriptHead transcriptTail tailTranscript =>
              have middleEq :=
                provenanceHead.after_unique transcriptHead
              subst middleEq
              have tailEq : transcriptTail = tail :=
                Subsingleton.elim _ _
              subst transcriptTail
              cases occurrence with
              | afterZig occurrenceHead occurrenceTail
                  nestedTranscript nested =>
                  have occurrenceMiddleEq :=
                    transcriptHead.after_unique occurrenceHead
                  subst occurrenceMiddleEq
                  have occurrenceTailEq : occurrenceTail = tail :=
                    Subsingleton.elim _ _
                  subst occurrenceTail
                  have nestedTranscriptEq :
                      nestedTranscript = tailTranscript :=
                    Subsingleton.elim _ _
                  cases nestedTranscriptEq
                  obtain ⟨realized⟩ :=
                    ih tailTranscript nested
                  exact
                    ⟨{
                      segmentInitial := realized.segmentInitial
                      segmentTransition := realized.segmentTransition
                      segmentProvenance := realized.segmentProvenance
                      prefixEvents :=
                        headTransition.events ++ realized.prefixEvents
                      suffixEvents := realized.suffixEvents
                      events_eq := by
                        change
                          headTransition.events ++ tailTransition.events =
                            (headTransition.events ++
                                realized.prefixEvents) ++
                              realized.segmentTransition.events ++
                                realized.suffixEvents
                        rw [realized.events_eq]
                        simp only [List.append_assoc]
                    }⟩
          | zigZig transcriptHead orientation transcriptTail
              tailTranscript =>
              have zigDepth := provenanceHead.depth_before_eq_one
              have doubleDepth := transcriptHead.depth_before_eq
              omega
          | zigZag transcriptHead orientation transcriptTail
              tailTranscript =>
              have zigDepth := provenanceHead.depth_before_eq_one
              have doubleDepth := transcriptHead.depth_before_eq
              omega
      | double provenanceHead =>
          cases transcript with
          | done transcriptRoot =>
              have rootDepth :=
                depth_eq_zero_of_hasRoot transcriptRoot
              have headDepth := provenanceHead.depth_before_eq
              omega
          | zig transcriptHead transcriptTail tailTranscript =>
              have zigDepth := transcriptHead.depth_before_eq_one
              have doubleDepth := provenanceHead.depth_before_eq
              omega
          | zigZig transcriptHead orientation transcriptTail
              tailTranscript =>
              have middleEq :=
                provenanceHead.after_unique_any_depth transcriptHead
              subst middleEq
              have tailEq : transcriptTail = tail :=
                Subsingleton.elim _ _
              subst transcriptTail
              cases occurrence with
              | here occurrenceStep occurrenceOrientation
                  occurrenceTail occurrenceTailTranscript =>
                  have stepAfterEq :=
                    transcriptHead.after_unique_any_depth
                      occurrenceStep
                  subst stepAfter
                  exact
                    ⟨{
                      segmentInitial := initial
                      segmentTransition := headTransition
                      segmentProvenance := by
                        simpa only using headProvenance
                      prefixEvents := []
                      suffixEvents := tailTransition.events
                      events_eq := by
                        simp [RepresentedTransition.trans]
                    }⟩
              | afterZigZig occurrenceHead occurrenceOrientation
                  occurrenceTail nestedTranscript nested =>
                  have occurrenceMiddleEq :=
                    transcriptHead.after_unique_any_depth occurrenceHead
                  subst occurrenceMiddleEq
                  have occurrenceTailEq : occurrenceTail = tail :=
                    Subsingleton.elim _ _
                  subst occurrenceTail
                  have nestedTranscriptEq :
                      nestedTranscript = tailTranscript :=
                    Subsingleton.elim _ _
                  cases nestedTranscriptEq
                  obtain ⟨realized⟩ :=
                    ih tailTranscript nested
                  exact
                    ⟨{
                      segmentInitial := realized.segmentInitial
                      segmentTransition := realized.segmentTransition
                      segmentProvenance := realized.segmentProvenance
                      prefixEvents :=
                        headTransition.events ++ realized.prefixEvents
                      suffixEvents := realized.suffixEvents
                      events_eq := by
                        change
                          headTransition.events ++ tailTransition.events =
                            (headTransition.events ++
                                realized.prefixEvents) ++
                              realized.segmentTransition.events ++
                                realized.suffixEvents
                        rw [realized.events_eq]
                        simp only [List.append_assoc]
                    }⟩
          | zigZag transcriptHead orientation transcriptTail
              tailTranscript =>
              have middleEq :=
                provenanceHead.after_unique_any_depth transcriptHead
              subst middleEq
              have tailEq : transcriptTail = tail :=
                Subsingleton.elim _ _
              subst transcriptTail
              cases occurrence with
              | afterZigZag occurrenceHead occurrenceOrientation
                  occurrenceTail nestedTranscript nested =>
                  have occurrenceMiddleEq :=
                    transcriptHead.after_unique_any_depth occurrenceHead
                  subst occurrenceMiddleEq
                  have occurrenceTailEq : occurrenceTail = tail :=
                    Subsingleton.elim _ _
                  subst occurrenceTail
                  have nestedTranscriptEq :
                      nestedTranscript = tailTranscript :=
                    Subsingleton.elim _ _
                  cases nestedTranscriptEq
                  obtain ⟨realized⟩ :=
                    ih tailTranscript nested
                  exact
                    ⟨{
                      segmentInitial := realized.segmentInitial
                      segmentTransition := realized.segmentTransition
                      segmentProvenance := realized.segmentProvenance
                      prefixEvents :=
                        headTransition.events ++ realized.prefixEvents
                      suffixEvents := realized.suffixEvents
                      events_eq := by
                        change
                          headTransition.events ++ tailTransition.events =
                            (headTransition.events ++
                                realized.prefixEvents) ++
                              realized.segmentTransition.events ++
                                realized.suffixEvents
                        rw [realized.events_eq]
                        simp only [List.append_assoc]
                    }⟩

end RealizedZigZigAt

end SplayExecutionTranscript

namespace SplaySequenceTranscript

/--
A global chronological zig-zig occurrence placed at one exact contiguous
event segment of the represented transition for the whole dependent splay
sequence.
-/
structure RealizedZigZigAt
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
  segmentInitial : State n
  segmentTransition :
    RepresentedTransition params
      snapshot stepBefore snapshot stepAfter segmentInitial
  segmentProvenance :
    SplayStep.RepresentedTransitionProvenance
      (.double occurrence.geometry.1) segmentTransition
  prefixEvents : List (Event n)
  suffixEvents : List (Event n)
  events_eq :
    transition.events =
      prefixEvents ++ segmentTransition.events ++ suffixEvents

namespace RealizedZigZigAt

/--
Exact sequence provenance places every global transcript zig-zig in a
contiguous segment of the sequence's event list.
-/
theorem exists_of_provenance
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
    {globalIndex requestIndex : ℕ} {access : Fin n}
    {requestBefore requestAfter : BST 0 n}
    {localIndex depth : ℕ} {stepBefore stepAfter : BST 0 n}
    (occurrence :
      ZigZigAt transcript globalIndex requestIndex access
        requestBefore requestAfter localIndex
        stepBefore stepAfter depth) :
    Nonempty (RealizedZigZigAt provenance occurrence) := by
  induction occurrence generalizing initial with
  | head head tail headTranscript tailTranscript localOccurrence =>
      cases provenance with
      | next _ _ headTransition tailTransition
          headProvenance tailProvenance =>
          obtain ⟨realized⟩ :=
            SplayExecutionTranscript.RealizedZigZigAt.exists_of_provenance
              headTranscript headProvenance localOccurrence
          exact
            ⟨{
              segmentInitial := realized.segmentInitial
              segmentTransition := realized.segmentTransition
              segmentProvenance := realized.segmentProvenance
              prefixEvents := realized.prefixEvents
              suffixEvents :=
                realized.suffixEvents ++ tailTransition.events
              events_eq := by
                change
                  headTransition.events ++ tailTransition.events =
                    realized.prefixEvents ++
                      realized.segmentTransition.events ++
                        (realized.suffixEvents ++
                          tailTransition.events)
                rw [realized.events_eq]
                simp only [List.append_assoc]
            }⟩
  | tail head tail headTranscript tailTranscript nested ih =>
      cases provenance with
      | next _ _ headTransition tailTransition
          headProvenance tailProvenance =>
          obtain ⟨realized⟩ :=
            ih tailProvenance
          exact
            ⟨{
              segmentInitial := realized.segmentInitial
              segmentTransition := realized.segmentTransition
              segmentProvenance := realized.segmentProvenance
              prefixEvents :=
                headTransition.events ++ realized.prefixEvents
              suffixEvents := realized.suffixEvents
              events_eq := by
                change
                  headTransition.events ++ tailTransition.events =
                    (headTransition.events ++
                        realized.prefixEvents) ++
                      realized.segmentTransition.events ++
                        realized.suffixEvents
                rw [realized.events_eq]
                simp only [List.append_assoc]
            }⟩

end RealizedZigZigAt

end SplaySequenceTranscript

/--
One abstract first/second pairing slot together with both of its checked
links:

* `occurrence` recovers the exact request and structural zig-zig; and
* `realized` locates that zig-zig at a contiguous event segment of the exact
  represented transition for the same dependent splay sequence.

Both phases of one zig-zig deliberately select the same transition segment.
The phase tag still distinguishes the two future pairing operations inside
that segment.
-/
structure RealizedPairingSlotOccurrence
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
    (slot : PairingSlot) : Type where
  occurrence : PairingSlotOccurrence transcript slot
  realized :
    SplaySequenceTranscript.RealizedZigZigAt
      provenance occurrence.occurrence

namespace RealizedPairingSlotOccurrence

/--
Every genuine pairing slot is automatically connected to the exact
contiguous rich-event segment for its concrete zig-zig once stepwise
transition provenance is available.
-/
theorem exists_of_mem
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
    (member :
      slot ∈ firstPairings kinds ++ secondPairings kinds) :
    Nonempty
      (RealizedPairingSlotOccurrence transcript provenance slot) := by
  obtain ⟨occurrence⟩ :=
    exists_pairingSlotOccurrence transcript slot member
  obtain ⟨realized⟩ :=
    SplaySequenceTranscript.RealizedZigZigAt.exists_of_provenance
      transcript provenance occurrence.occurrence
  exact
    ⟨{ occurrence := occurrence
       realized := realized }⟩

end RealizedPairingSlotOccurrence

end Splay.Accounting
