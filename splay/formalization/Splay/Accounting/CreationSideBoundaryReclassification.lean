import Splay.Accounting.CreationSideBoundaryImportance

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

namespace BoundaryPassPairingClassification

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

/-- All boundary moves, before assigning their geometric importance label. -/
def allBoundaryMoves
    (classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events) :
    List (BoundaryPairingMove classification.trace) :=
  classification.importantMoves ++ classification.unimportantMoves

/-- Forgetting the old labels recovers exactly the old boundary-slot list. -/
theorem allBoundaryMoves_slots
    (classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events) :
    classification.allBoundaryMoves.map BoundaryPairingMove.slot =
      classification.passClassification.importantSlots ++
        classification.passClassification.unimportantSlots := by
  simp only [allBoundaryMoves, List.map_append]
  rw [classification.importantSlots_eq,
    classification.unimportantSlots_eq]

end BoundaryPassPairingClassification

/--
Chronological evidence for every boundary move, independently of the
classification's old important/unimportant labels.

This is the exact input needed for semantic relabelling.  In particular,
arbitrary label swapping is no longer relevant once this provider exists.
-/
structure CreationBoundaryEvidenceProvider
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
  evidence :
    ∀ move : BoundaryPairingMove classification.trace,
      move ∈ classification.allBoundaryMoves →
        CreationBoundaryMoveEvidence provenance classification move

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

/-- A move belongs to the geometric unimportant class. -/
def GeometricallyUnimportant
    (provider :
      CreationBoundaryEvidenceProvider provenance classification)
    (cutoff : ℕ)
    (move : BoundaryPairingMove classification.trace) : Prop :=
  ∃ member : move ∈ classification.allBoundaryMoves,
    (provider.evidence move member).Unimportant cutoff

/-- Canonical important sublist: the complement of geometric unimportance. -/
noncomputable def importantMoves
    (provider :
      CreationBoundaryEvidenceProvider provenance classification)
    (cutoff : ℕ) :
    List (BoundaryPairingMove classification.trace) := by
  classical
  exact
    classification.allBoundaryMoves.filter fun move =>
      decide (¬ provider.GeometricallyUnimportant cutoff move)

/-- Canonical unimportant sublist selected by the request-start geometry. -/
noncomputable def unimportantMoves
    (provider :
      CreationBoundaryEvidenceProvider provenance classification)
    (cutoff : ℕ) :
    List (BoundaryPairingMove classification.trace) := by
  classical
  exact
    classification.allBoundaryMoves.filter fun move =>
      decide (provider.GeometricallyUnimportant cutoff move)

private theorem filter_not_append_filter_perm
    {α : Type*} (predicate : α → Prop) [DecidablePred predicate] :
    ∀ values : List α,
      List.Perm
        (values.filter (fun value => decide (¬ predicate value)) ++
          values.filter (fun value => decide (predicate value)))
        values := by
  intro values
  induction values with
  | nil =>
      simp
  | cons head tail ih =>
      by_cases selected : predicate head
      · have moveHead :
            List.Perm
              (tail.filter (fun value => decide (¬ predicate value)) ++
                head ::
                  tail.filter (fun value => decide (predicate value)))
              (head ::
                (tail.filter (fun value => decide (¬ predicate value)) ++
                  tail.filter (fun value => decide (predicate value)))) :=
          List.perm_middle
        simpa [selected] using moveHead.trans (ih.cons head)
      · simpa [selected] using ih.cons head

/-- Geometric relabelling is a multiplicity-preserving partition. -/
theorem boundaryMoves_partition
    (provider :
      CreationBoundaryEvidenceProvider provenance classification)
    (cutoff : ℕ) :
    List.Perm
      (provider.importantMoves cutoff ++ provider.unimportantMoves cutoff)
      classification.allBoundaryMoves := by
  classical
  simpa [importantMoves, unimportantMoves] using
    (filter_not_append_filter_perm
      (provider.GeometricallyUnimportant cutoff)
      classification.allBoundaryMoves)

/-- Every selected unimportant move carries the required geometric evidence. -/
theorem exists_unimportant_evidence
    (provider :
      CreationBoundaryEvidenceProvider provenance classification)
    (cutoff : ℕ)
    (move : BoundaryPairingMove classification.trace)
    (member : move ∈ provider.unimportantMoves cutoff) :
    ∃ sourceMember : move ∈ classification.allBoundaryMoves,
      (provider.evidence move sourceMember).Unimportant cutoff := by
  classical
  have filtered := List.mem_filter.mp member
  have selected :
      provider.GeometricallyUnimportant cutoff move := by
    simpa only [decide_eq_true_eq] using filtered.2
  simpa only [GeometricallyUnimportant] using selected

/-- Every selected important move carries the complementary evidence. -/
theorem exists_important_evidence
    (provider :
      CreationBoundaryEvidenceProvider provenance classification)
    (cutoff : ℕ)
    (move : BoundaryPairingMove classification.trace)
    (member : move ∈ provider.importantMoves cutoff) :
    ∃ sourceMember : move ∈ classification.allBoundaryMoves,
      (provider.evidence move sourceMember).Important cutoff := by
  classical
  have filtered := List.mem_filter.mp member
  refine ⟨filtered.1, ?_⟩
  have notSelected :
      ¬ provider.GeometricallyUnimportant cutoff move :=
    by simpa only [decide_eq_true_eq] using filtered.2
  intro unimportant
  exact notSelected ⟨filtered.1, unimportant⟩

/--
The pass-level classification after replacing the arbitrary old boundary
labels by the canonical geometric partition.
-/
noncomputable def passReclassification
    (provider :
      CreationBoundaryEvidenceProvider provenance classification)
    (cutoff : ℕ) :
    PassPairingClassification transcript params
      initial.toInterface transition.final.toInterface
      (eraseOperations transition.events) := by
  let old := classification.passClassification
  let important := provider.importantMoves cutoff
  let unimportant := provider.unimportantMoves cutoff
  refine
    { initialState := old.initialState
      trace := old.trace
      finalLabels := old.finalLabels
      activityOccurrences := old.activityOccurrences
      activityHistory := old.activityHistory
      importantSlots := important.map BoundaryPairingMove.slot
      unimportantSlots := unimportant.map BoundaryPairingMove.slot
      internalCharges := old.internalCharges
      slots_partition := ?_
      internalActivityOrdinals_nodup :=
        old.internalActivityOrdinals_nodup }
  have movesPermutation :=
    (provider.boundaryMoves_partition cutoff).map
      BoundaryPairingMove.slot
  have oldBoundary :
      classification.allBoundaryMoves.map BoundaryPairingMove.slot =
        old.importantSlots ++ old.unimportantSlots := by
    exact classification.allBoundaryMoves_slots
  have boundaryPermutation :
      List.Perm
        (important.map BoundaryPairingMove.slot ++
          unimportant.map BoundaryPairingMove.slot)
        (old.importantSlots ++ old.unimportantSlots) := by
    simpa only [List.map_append, oldBoundary] using movesPermutation
  exact
    (boundaryPermutation.append_right
      (old.internalCharges.map Prod.fst)).trans old.slots_partition

/--
The rich classification with the same trace, moves, and internal charges,
but with boundary labels determined by request-start geometry.
-/
noncomputable def reclassification
    (provider :
      CreationBoundaryEvidenceProvider provenance classification)
    (cutoff : ℕ) :
    BoundaryPassPairingClassification transcript params
      initial transition.final transition.events where
  trace := classification.trace
  passClassification := provider.passReclassification cutoff
  importantMoves := provider.importantMoves cutoff
  unimportantMoves := provider.unimportantMoves cutoff
  importantSlots_eq := rfl
  unimportantSlots_eq := rfl

/-- Transport one old-trace evidence value to the relabelled classification. -/
noncomputable def reclassifiedEvidence
    (provider :
      CreationBoundaryEvidenceProvider provenance classification)
    (cutoff : ℕ)
    (move : BoundaryPairingMove classification.trace)
    (member : move ∈ classification.allBoundaryMoves) :
    CreationBoundaryMoveEvidence provenance
      (provider.reclassification cutoff) move := by
  let evidence := provider.evidence move member
  exact
    { endpoint := evidence.endpoint
      request := evidence.request
      chronology := evidence.chronology
      firstLeave := evidence.firstLeave }

/--
Relabelling changes no request-start geometry.  In particular, the chosen
evidence has the same canonical unimportant proposition.
-/
theorem reclassifiedEvidence_unimportant_iff
    (provider :
      CreationBoundaryEvidenceProvider provenance classification)
    (cutoff : ℕ)
    (move : BoundaryPairingMove classification.trace)
    (member : move ∈ classification.allBoundaryMoves) :
    (provider.reclassifiedEvidence cutoff move member).Unimportant cutoff ↔
      (provider.evidence move member).Unimportant cutoff := by
  rfl

/-- The canonical relabelling automatically satisfies geometric importance. -/
theorem reclassificationImportance
    (provider :
      CreationBoundaryEvidenceProvider provenance classification)
    (cutoff : ℕ) :
    CreationSideBoundaryImportance provenance
      (provider.reclassification cutoff) cutoff where
  important_spec := by
    intro move member
    have filtered :
        move ∈ provider.importantMoves cutoff := by
      exact member
    obtain ⟨sourceMember, important⟩ :=
      provider.exists_important_evidence cutoff move filtered
    let evidence :=
      provider.reclassifiedEvidence cutoff move sourceMember
    exact
      ⟨evidence,
        (provider.reclassifiedEvidence_unimportant_iff
          cutoff move sourceMember).not.mpr important⟩
  unimportant_spec := by
    intro move member
    have filtered :
        move ∈ provider.unimportantMoves cutoff := by
      exact member
    obtain ⟨sourceMember, unimportant⟩ :=
      provider.exists_unimportant_evidence cutoff move filtered
    let evidence :=
      provider.reclassifiedEvidence cutoff move sourceMember
    exact
      ⟨evidence,
        (provider.reclassifiedEvidence_unimportant_iff
          cutoff move sourceMember).mpr unimportant⟩

/--
Every canonically important move is tied to the same persistent root both in
its original request-start geometry and at its selected delete.
-/
theorem important_requestRootSlot_eq_persistentRootSlot
    (provider :
      CreationBoundaryEvidenceProvider provenance classification)
    (cutoff : ℕ)
    (move :
      BoundaryPairingMove (provider.reclassification cutoff).trace)
    (member :
      move ∈ (provider.reclassification cutoff).importantMoves) :
    ∃ evidence :
        CreationBoundaryMoveEvidence provenance
          (provider.reclassification cutoff) move,
      evidence.Important cutoff ∧
        evidence.requestRootSlot =
          (provider.reclassification cutoff).persistentRootSlot move := by
  obtain ⟨evidence, important⟩ :=
    (provider.reclassificationImportance cutoff).important_spec
      move member
  exact
    ⟨evidence, important,
      evidence.requestRootSlot_eq_persistentRootSlot⟩

/-- The same request-start/delete-time root identity for unimportant moves. -/
theorem unimportant_requestRootSlot_eq_persistentRootSlot
    (provider :
      CreationBoundaryEvidenceProvider provenance classification)
    (cutoff : ℕ)
    (move :
      BoundaryPairingMove (provider.reclassification cutoff).trace)
    (member :
      move ∈ (provider.reclassification cutoff).unimportantMoves) :
    ∃ evidence :
        CreationBoundaryMoveEvidence provenance
          (provider.reclassification cutoff) move,
      evidence.Unimportant cutoff ∧
        evidence.requestRootSlot =
          (provider.reclassification cutoff).persistentRootSlot move := by
  obtain ⟨evidence, unimportant⟩ :=
    (provider.reclassificationImportance cutoff).unimportant_spec
      move member
  exact
    ⟨evidence, unimportant,
      evidence.requestRootSlot_eq_persistentRootSlot⟩

end CreationBoundaryEvidenceProvider

end Splay.Accounting
