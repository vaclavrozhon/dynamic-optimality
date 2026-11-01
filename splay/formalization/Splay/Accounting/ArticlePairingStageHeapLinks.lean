import Splay.Accounting.ArticleBatchHeapLinks
import Splay.Accounting.ArticlePairingStageGeometry
import Splay.Accounting.WholeSplayFinalHeapLinks

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open WholeSplayTemporaryPriorityReduction WholeSplayTemporaryCoreGeometry WholeSplayTemporaryCoreClassification

/-- Selecting either phase is exactly membership in the row's two-link set. -/
theorem mem_articleRowHeapLinks {n : ℕ} (row : ℕ × (List (External n) × List (External n)))
    (link : External n × External n) :
    link ∈ articleRowHeapLinks row ↔ ∃ phase, link ∈ selectionHeapLinks (articleRowSelection phase row) := by
  constructor
  · intro member
    rcases Finset.mem_union.mp member with first | second
    · exact ⟨.first, first⟩
    · exact ⟨.second, second⟩
  · rintro ⟨phase, member⟩
    cases phase with
    | first => exact Finset.mem_union_left _ member
    | second => exact Finset.mem_union_right _ member

namespace ArticlePairingStage

variable {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
  {before : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
  (stage : ArticlePairingStage params snapshot before key kinds initial)

/-- The directed heap links of all actual operations in the pairing stage. -/
noncomputable def matchingHeapLinks : Finset (External n × External n) :=
  (stage.matching.map fun pair => (pair.winner, pair.loser)).toFinset

/-- Internal and boundary operations together realize exactly the row links. -/
theorem matchingHeapLinks_eq_batches : stage.matchingHeapLinks = stage.allBatches.heapLinks := by
  ext link
  rw [ArticleRetainedPairingBatches.mem_heapLinks]
  constructor
  · intro member
    obtain ⟨pairing, pairingMember, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    obtain ⟨row, rowMember, phase, selected⟩ := stage.rows_sound pairingMember
    refine ⟨row, rowMember, (mem_articleRowHeapLinks row link).mpr ⟨phase, ?_⟩⟩
    rw [selected]
    exact Finset.mem_singleton.mpr equal.symm
  · rintro ⟨row, rowMember, member⟩
    obtain ⟨phase, phaseMember⟩ := (mem_articleRowHeapLinks row link).mp member
    obtain ⟨pairing, pairingMember, selected⟩ := stage.rows_complete rowMember phase
    rw [selected] at phaseMember
    have equal : link = (pairing.winner, pairing.loser) := Finset.mem_singleton.mp phaseMember
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨pairing, pairingMember, equal.symm⟩)

/-- The lazy pairing stage and the original splay transcript have exactly the
same directed pairing links. This statement refers to the actual operations. -/
theorem matchingHeapLinks_eq_transcript {after : BST 0 n}
    {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag) :
    stage.matchingHeapLinks = transcriptPairingLinks snapshot transcript := by
  rw [stage.matchingHeapLinks_eq_batches]
  exact stage.allBatches.heapLinks_eq_transcript transcript key.isLt stage.rankZero

end ArticlePairingStage

/-- Every genuinely executed pairing has its canonical parent relation at
the final splay endpoint, after all later rotations in the same request. -/
theorem ArticlePairingStage.pairing_final_canonicalParent {n : ℕ} {params : Interface.Parameters}
    (comparison : BST 0 n) (key : Fin n) (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered : leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    {before after : BST 0 n} {initial : Lazy.State n} {kinds : List SplayStepKind}
    (stage : ArticlePairingStage params
      (temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered) before key kinds initial)
    {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (placement : BoundaryPlacementAt key leftBoundary rightBoundary before)
    {pairing : Interface.Pairing n} (member : pairing ∈ stage.matching) :
    canonicalParent (temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered)
      after pairing.loser = some pairing.winner := by
  apply (mem_heapLinks_iff_parent _ _ _ _).mp
  apply (transcript.final_heapLinks comparison key comparisonRoot leftBoundary rightBoundary ordered placement).1
  apply Finset.mem_union_right
  rw [← stage.matchingHeapLinks_eq_transcript transcript]
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨pairing, member, rfl⟩)

end Splay.Accounting
