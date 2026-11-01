import Splay.Accounting.ArticleInternalPairingExecution
import Splay.Lazy.SplitBlockCases
import Splay.Interface.OperationCounts
import Splay.Lazy.BlockRefinement

namespace Splay.Accounting

open Splay.Lazy

/-- One actual stable numerical cut split, including exact fresh blocks,
checked event costs, and removal of every crossing in its owner-side slot. -/
structure ArticleCutSplit {n : ℕ} (params : Interface.Parameters) (initial : Lazy.State n)
    (sourceId : Interface.BlockId) (source : Block n) (cut : ℕ) where
  prefixGap : ℤ
  suffixGap : ℤ
  events : List (Event n)
  final : Lazy.State n
  trace : Trace params initial events final
  stable : final.Stable params
  view_eq : final.view = initial.view
  blocks_eq : final.blocks = (initial.split sourceId source (source.cutPrefixLength cut) prefixGap suffixGap).blocks
  births : final.blocks.length = initial.blocks.length + 2
  noInserts : Interface.totalInserts (eraseOperations events) = 0
  noIncreases : Interface.totalIncreases (eraseOperations events) = 0
  cleared : ∀ block ∈ final.blocks, block.owner = source.owner → block.side = source.side → ¬ block.CrossesCut cut

namespace ArticleCutSplit

theorem refines {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Block n} {cut : ℕ}
    (execution : ArticleCutSplit params initial sourceId source cut)
    (found : initial.blocks[sourceId]? = some source) : initial.BlockRefinement execution.final := by
  intro block member
  rw [execution.blocks_eq] at member
  exact initial.split_blockRefinement sourceId source _ execution.prefixGap execution.suffixGap found block member

theorem passRefines {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Block n} {cut : ℕ}
    (execution : ArticleCutSplit params initial sourceId source cut)
    (found : initial.blocks[sourceId]? = some source) : initial.PassRefinement execution.final :=
  (initial.split_passRefinement sourceId source _ execution.prefixGap execution.suffixGap found).trans
    (State.PassRefinement.of_blocks_eq execution.blocks_eq)

theorem growing_preserved {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Block n} {cut : ℕ}
    (execution : ArticleCutSplit params initial sourceId source cut)
    (found : initial.blocks[sourceId]? = some source) (shrinking : source.mode = .shrinking) :
    ∀ block ∈ execution.final.blocks, block.mode = .growing → block ∈ initial.blocks := by
  intro block member growing
  rw [execution.blocks_eq] at member
  exact initial.split_growing_blocks_preserved sourceId source _ execution.prefixGap execution.suffixGap found shrinking block member growing

/-- The existing attained-gap split/normalization primitive realizes this
cut, without an assumed endpoint or per-child insertion. -/
theorem exists_of_crossing {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    (stable : initial.Stable params) {sourceId : Interface.BlockId} {source : Block n}
    (found : initial.blocks[sourceId]? = some source) (shrinking : source.mode = .shrinking)
    (cut : ℕ) (crossing : source.CrossesCut cut) :
    Nonempty (ArticleCutSplit params initial sourceId source cut) := by
  obtain ⟨prefixGap, suffixGap, splitState, events, final, _prefixValid, _suffixValid,
      splitEq, eventsEq, finalEq, trace, adjustmentNoIncreases, blocksEq, viewEq, sourceValues⟩ :=
    exists_articleSplitAdjustedTrace stable found shrinking (source.cutPrefixLength cut) (source.cutPrefixLength_le cut)
  have finalStable := articleSplitAdjusted_stable stable found shrinking (source.cutPrefixLength cut)
    prefixGap suffixGap splitEq finalEq trace sourceValues
  have finalBlocks : final.blocks = (initial.split sourceId source (source.cutPrefixLength cut) prefixGap suffixGap).blocks := by
    rw [blocksEq, splitEq]
  refine ⟨{
    prefixGap := prefixGap
    suffixGap := suffixGap
    events := events
    final := final
    trace := trace
    stable := finalStable
    view_eq := viewEq
    blocks_eq := finalBlocks
    births := by rw [finalBlocks]; simp [State.split, State.splitBlocks]
    noInserts := ?_
    noIncreases := ?_
    cleared := ?_
  }⟩
  · rw [eventsEq, eraseOperations_append, Interface.totalInserts_append]
    change 0 + Interface.totalInserts (eraseOperations (splitState.adjustValuesEvents _ source.elements)) = 0
    rw [splitState.totalInserts_adjustValuesEvents_eq_zero, Nat.zero_add]
  · rw [eventsEq, eraseOperations_append, Interface.totalIncreases_append]
    change 0 + Interface.totalIncreases (eraseOperations (splitState.adjustValuesEvents _ source.elements)) = 0
    rw [adjustmentNoIncreases, Nat.zero_add]
  · rw [finalBlocks]
    exact initial.split_cut_no_crossing stable.1 sourceId source cut prefixGap suffixGap found crossing

end ArticleCutSplit
end Splay.Accounting
