import Splay.Accounting.ArticleTransferCanonicalView
import Splay.Accounting.ArticleTemporaryTransferStage

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open WholeSplayTemporaryPriorityReduction WholeSplayTemporaryCoreGeometry WholeSplayTemporaryCoreClassification

/-- The actual preparation's snapshot is the geometric temporary snapshot
for the same two boundaries automatically selected after preparation. -/
theorem ArticleTemporaryPreparation.temporarySnapshot_eq_comparison {n : ℕ} {params : Interface.Parameters}
    (comparison : BST 0 n) (key : Fin n) (comparisonRoot : comparison.HasRoot key.val)
    {before : BST 0 n} {initial : Lazy.State n}
    (setup : ArticleTemporaryPreparation params (Snapshot.ofTree comparison) before key initial) :
    let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection setup.temporarySnapshot before key
    setup.temporarySnapshot = WholeSplayTemporaryPriorityReduction.temporarySnapshot comparison key comparisonRoot selection.left selection.right selection.ordered := by
  dsimp only
  have selectionEq := setup.boundary_selection_eq
  unfold WholeSplayTemporaryPriorityReduction.temporarySnapshot
  simp only [selectionEq.1, selectionEq.2]
  rfl

namespace ArticleTemporaryTransferStage

variable {n : ℕ} {params : Interface.Parameters} {comparison : BST 0 n}
  {before : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
  (stage : ArticleTemporaryTransferStage params (Snapshot.ofTree comparison) before key kinds initial)

/-- Every geometric equality needed to install the canonical splay endpoint
follows from this actual pairing-and-transfer construction. -/
theorem canonical_agreement (comparisonRoot : comparison.HasRoot key.val)
    {after : BST 0 n} {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag) :
    stage.final.view.rank = (canonicalHeapView stage.setup.temporarySnapshot after).rank ∧
      stage.final.view.root = (canonicalHeapView stage.setup.temporarySnapshot after).root ∧
      stage.final.view.parent = (canonicalHeapView stage.setup.temporarySnapshot after).parent ∧
      stage.final.view.side = (canonicalHeapView stage.setup.temporarySnapshot after).side := by
  let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection stage.setup.temporarySnapshot before key
  exact stage.pairing.transferBothSides_canonical_agreement comparison key comparisonRoot selection.left selection.right
    selection.ordered (stage.setup.temporarySnapshot_eq_comparison comparison key comparisonRoot)
    transcript (canonicalBoundaryPlacement stage.setup.temporarySnapshot before key) stage.leftGeometry stage.rightGeometry

/-- The endpoint differs only in the independent depth witness; blocks,
values, interval IDs and all geometrical heap data are retained. -/
noncomputable def canonicalFinal (after : BST 0 n) : Lazy.State n :=
  stage.final.replaceView (canonicalHeapView stage.setup.temporarySnapshot after)

/-- The final depth-witness replacement is an actual silent primitive step. -/
theorem canonical_step (comparisonRoot : comparison.HasRoot key.val)
    {after : BST 0 n} {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag) :
    Step params stage.final .silent (stage.canonicalFinal after) := by
  have agreement := stage.canonical_agreement comparisonRoot transcript
  exact State.replaceView_step stage.stable.1 _ agreement.1.symm
    (fun element _ => ⟨congrFun agreement.2.2.1.symm element, congrFun agreement.2.2.2.symm element⟩)

/-- Canonical representation at the true final splay tree, with temporary
priorities still installed on the two selected boundary vertices. -/
theorem canonical_represents (comparisonRoot : comparison.HasRoot key.val)
    {after : BST 0 n} {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag) :
    (stage.canonicalFinal after).Represents params stage.setup.temporarySnapshot after := by
  have agreement := stage.canonical_agreement comparisonRoot transcript
  exact ⟨State.replaceView_stable stage.stable _ agreement.1.symm agreement.2.1.symm
    agreement.2.2.1.symm agreement.2.2.2.symm, rfl⟩

/-- All preceding preparation, actual pairings, both transfers and final
canonicalization compose into this exact rich-event trace. -/
theorem canonical_trace (comparisonRoot : comparison.HasRoot key.val)
    {after : BST 0 n} {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag) :
    Trace params initial (stage.events ++ [.silent]) (stage.canonicalFinal after) :=
  stage.trace.append (Trace.singleton (stage.canonical_step comparisonRoot transcript))

/-- Canonicalization adds no visible interface operation. -/
@[simp]
theorem canonical_erased_events : eraseOperations (stage.events ++ [.silent]) = eraseOperations stage.events := by
  rw [eraseOperations_append, show eraseOperations ([.silent] : List (Event n)) = [] from rfl, List.append_nil]

/-- Installing the canonical depth witness creates no additional block. -/
theorem canonical_births (after : BST 0 n) :
    (stage.canonicalFinal after).blocks.length ≤ initial.blocks.length + 32 := stage.births

/-- Canonicalization preserves the exact geometric gap potential. -/
theorem canonical_gap_eq (comparisonRoot : comparison.HasRoot key.val)
    {after : BST 0 n} {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag) :
    geometricGapPotential (stage.canonicalFinal after) = geometricGapPotential stage.final := by
  have canonicalStable := (stage.canonical_represents comparisonRoot transcript).stable
  rw [geometricGapPotential_eq canonicalStable.2.1 canonicalStable.2.2.2.2.2,
    geometricGapPotential_eq stage.stable.2.1 stage.stable.2.2.2.2.2]
  rfl

/-- The good-pairing gap payment remains valid at the actual canonical
splay endpoint under the temporary snapshot. -/
theorem canonical_gap_pays_good (comparisonRoot : comparison.HasRoot key.val)
    {after : BST 0 n} {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag) :
    geometricGapPotential (stage.canonicalFinal after) + stage.pairing.internal.chain.goodCount ≤
      geometricGapPotential initial + 8 * params.valueBound * stage.pairing.boundaryCount := by
  rw [stage.canonical_gap_eq comparisonRoot transcript]
  exact stage.gap_pays_good

/-- A represented initial state and the actual splay transcript suffice to
construct the whole canonical prefix. The only remaining request suffix is
restoration of the two artificial boundary priorities. -/
theorem exists_canonicalPrefix (comparisonRoot : comparison.HasRoot key.val)
    {after : BST 0 n} {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (represented : initial.Represents params (Snapshot.ofTree comparison).withTruePriority before)
    (valueBound : Analysis.contractedGap (2 * (Snapshot.ofTree comparison).maxRank + 1) ≤ params.valueBound) :
    ∃ stage : ArticleTemporaryTransferStage params (Snapshot.ofTree comparison) before key kinds initial,
      Trace params initial (stage.events ++ [.silent]) (stage.canonicalFinal after) ∧
        (stage.canonicalFinal after).Represents params stage.setup.temporarySnapshot after := by
  obtain ⟨stage⟩ := exists_of_transcript transcript
    (ofTree_rank_valuePos_eq_zero_of_hasRoot comparison key comparisonRoot) represented valueBound
  exact ⟨stage, stage.canonical_trace comparisonRoot transcript, stage.canonical_represents comparisonRoot transcript⟩

end ArticleTemporaryTransferStage

end Splay.Accounting
