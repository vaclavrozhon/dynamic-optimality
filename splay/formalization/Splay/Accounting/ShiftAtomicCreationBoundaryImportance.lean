import Splay.Accounting.CreationSideBoundaryReclassification

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

namespace RequestStartSource

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
    {slot : PairingSlot}
    {winner loser : Interface.Element n}
    {agreement :
      RealizedPairingEndpointAgreement transcript provenance
        slot winner loser}
    {request :
      SplaySequenceTranscript.RealizedRequestAt provenance
        agreement.endpoints.realized.occurrence.occurrence}
    {initialLabels : Interface.RootLabels}

/--
In a shift-atomic request-start state, the automatically recovered block
containing the loser is a singleton.  Empty growing and shrinking cases are
excluded by the loser's certified membership.
-/
theorem richSourceBlock_elements_singleton_of_shiftAtomic
    (sourceAt :
      RequestStartSource agreement request initialLabels)
    (atomic : request.requestInitial.ShiftAtomic) :
    ∃ element, sourceAt.richSourceBlock.elements = [element] := by
  have blockMember :
      sourceAt.richSourceBlock ∈ request.requestInitial.blocks :=
    List.mem_of_getElem? sourceAt.richSourceFound
  have loserMember :
      loser ∈ sourceAt.richSourceBlock.elements := by
    rw [sourceAt.richSourceBlock_elements]
    exact sourceAt.loserMem
  rcases atomic sourceAt.richSourceBlock blockMember with
      growing | shrinking
  · rw [growing.2] at loserMember
    simp at loserMember
  · rcases shrinking.2 with empty | singleton
    · rw [empty] at loserMember
      simp at loserMember
    · exact singleton

/-- A shift-atomic source interval is canonically cross-side unbroken. -/
theorem unbroken_of_shiftAtomic
    (sourceAt :
      RequestStartSource agreement request initialLabels)
    (atomic : request.requestInitial.ShiftAtomic) :
    sourceAt.Unbroken := by
  obtain ⟨element, singleton⟩ :=
    sourceAt.richSourceBlock_elements_singleton_of_shiftAtomic atomic
  exact
    canonicalBlockCrossSideUnbroken_of_elements_singleton
      snapshot
      agreement.endpoints.realized.occurrence.requestBefore
      sourceAt.richSourceBlock element singleton

/--
On a shift-atomic request boundary, geometric unimportance has the exact
degenerate threshold `cutoff ≤ 1`.
-/
theorem unimportant_iff_cutoff_le_one_of_shiftAtomic
    (sourceAt :
      RequestStartSource agreement request initialLabels)
    (atomic : request.requestInitial.ShiftAtomic)
    (cutoff : ℕ) :
    sourceAt.Unimportant cutoff ↔ cutoff ≤ 1 := by
  obtain ⟨element, singleton⟩ :=
    sourceAt.richSourceBlock_elements_singleton_of_shiftAtomic atomic
  constructor
  · intro unimportant
    simpa [singleton] using unimportant.2
  · intro cutoffSmall
    exact
      ⟨sourceAt.unbroken_of_shiftAtomic atomic,
        by simpa [singleton] using cutoffSmall⟩

/-- Consequently every such move is important at the usual cutoff `≥ 2`. -/
theorem important_of_shiftAtomic
    (sourceAt :
      RequestStartSource agreement request initialLabels)
    (atomic : request.requestInitial.ShiftAtomic)
    {cutoff : ℕ}
    (two_le_cutoff : 2 ≤ cutoff) :
    sourceAt.Important cutoff := by
  rw [RequestStartSource.Important]
  rw [sourceAt.unimportant_iff_cutoff_le_one_of_shiftAtomic atomic]
  omega

end RequestStartSource

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

/--
The singleton conclusion exposed directly at the creation-evidence level.
-/
theorem requestSource_elements_singleton_of_shiftAtomic
    (evidence :
      CreationBoundaryMoveEvidence provenance classification move)
    (atomic : evidence.request.requestInitial.ShiftAtomic) :
    ∃ element, evidence.requestSource.richSourceBlock.elements = [element] :=
  evidence.requestSource.richSourceBlock_elements_singleton_of_shiftAtomic
    atomic

/--
Any chronologically aligned boundary move whose containing request starts
shift atomic is automatically important for every cutoff at least two.
-/
theorem important_of_requestInitial_shiftAtomic
    (evidence :
      CreationBoundaryMoveEvidence provenance classification move)
    (atomic : evidence.request.requestInitial.ShiftAtomic)
    {cutoff : ℕ}
    (two_le_cutoff : 2 ≤ cutoff) :
    evidence.Important cutoff :=
  evidence.requestSource.important_of_shiftAtomic atomic two_le_cutoff

end CreationBoundaryMoveEvidence

namespace CreationBoundaryEvidenceProvider

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
If every represented request boundary is shift atomic, the canonical
geometric relabelling has no unimportant moves for any cutoff at least two.

This is a useful sharp limitation of the shift-atomic macro construction:
large unbroken source intervals require a non-atomic request-start schedule.
-/
theorem unimportantMoves_eq_nil_of_all_requestInitial_shiftAtomic
    (provider :
      CreationBoundaryEvidenceProvider provenance classification)
    {cutoff : ℕ}
    (two_le_cutoff : 2 ≤ cutoff)
    (allAtomic :
      ∀ move (member : move ∈ classification.allBoundaryMoves),
        (provider.evidence move member).request.requestInitial.ShiftAtomic) :
    provider.unimportantMoves cutoff = [] := by
  classical
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro move member
  obtain ⟨sourceMember, unimportant⟩ :=
    provider.exists_unimportant_evidence cutoff move member
  have important :
      (provider.evidence move sourceMember).Important cutoff :=
    (provider.evidence move sourceMember).important_of_requestInitial_shiftAtomic
      (allAtomic move sourceMember) two_le_cutoff
  exact important unimportant

/--
Under the same hypothesis, the important list contains every boundary move,
with multiplicity.  `Perm` is the appropriate statement because the canonical
filter partition is specified extensionally rather than by a chosen ordering.
-/
theorem importantMoves_perm_allBoundaryMoves_of_all_requestInitial_shiftAtomic
    (provider :
      CreationBoundaryEvidenceProvider provenance classification)
    {cutoff : ℕ}
    (two_le_cutoff : 2 ≤ cutoff)
    (allAtomic :
      ∀ move (member : move ∈ classification.allBoundaryMoves),
        (provider.evidence move member).request.requestInitial.ShiftAtomic) :
    List.Perm
      (provider.reclassification cutoff).importantMoves
      classification.allBoundaryMoves := by
  have partition := provider.boundaryMoves_partition cutoff
  have unimportantEmpty :=
    provider.unimportantMoves_eq_nil_of_all_requestInitial_shiftAtomic
      two_le_cutoff allAtomic
  rw [unimportantEmpty, List.append_nil] at partition
  exact partition

/-- In particular, geometric relabelling preserves the full boundary count. -/
theorem importantMoves_length_eq_allBoundaryMoves_length_of_all_requestInitial_shiftAtomic
    (provider :
      CreationBoundaryEvidenceProvider provenance classification)
    {cutoff : ℕ}
    (two_le_cutoff : 2 ≤ cutoff)
    (allAtomic :
      ∀ move (member : move ∈ classification.allBoundaryMoves),
        (provider.evidence move member).request.requestInitial.ShiftAtomic) :
    (provider.reclassification cutoff).importantMoves.length =
      classification.allBoundaryMoves.length :=
  (provider.importantMoves_perm_allBoundaryMoves_of_all_requestInitial_shiftAtomic
    two_le_cutoff allAtomic).length_eq

end CreationBoundaryEvidenceProvider

end Splay.Accounting
