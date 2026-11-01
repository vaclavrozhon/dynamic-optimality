import Splay.Accounting.ArticleGlobalFirstLeave

namespace Splay.Accounting

open Splay.Lazy Splay.Rank Splay.Tree.BST
open ArticleBatchDestinationAllocation

/-- Canonical geometry supplies second-phase outermost order for any selected
source, including a source using its exempt passes. -/
theorem ArticleSourcePairings.secondOutermostOrder_of_nestedChildOrder
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ} {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches)
    {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (valid : state.Valid params)
    (nested : state.view.NestedChildOrder)
    (secondAllocation :
      ArticleBatchDestinationAllocation .second batches state) :
    BatchOutermostOrder state.view secondAllocation.matching := by
  have sourceStructural := valid.2 source (List.mem_of_getElem? sourceFound)
  intro selected selectedMember child childMember
  obtain ⟨row, rowMember, selectedRowEq⟩ :=
    secondAllocation.agreement.exists_row_of_mem selectedMember
  obtain ⟨winner, firstLoser, secondLoser, candidates, firstEq,
      secondEq, firstAdjacent, secondAdjacent, losersNe, candidatePerm,
      candidateChunk, candidateSegment, firstInBlock, secondInBlock,
      winnerInside, firstInside, secondInside⟩ :=
    plan.row_inside rowMember
  have selectedPairEq : [winner, secondLoser] =
      [selected.winner, selected.loser] :=
    secondEq.symm.trans selectedRowEq
  have selectedEndpoints : winner = selected.winner ∧
      secondLoser = selected.loser := by
    simpa using selectedPairEq
  have winnerMember : selected.winner ∈ source.elements := by
    simpa [sourceElements, selectedEndpoints.1] using winnerInside
  have loserMember : selected.loser ∈ source.elements := by
    simpa [sourceElements, selectedEndpoints.2] using secondInside
  have winnerParent := sourceStructural.parent_eq winnerMember
  have loserParent := sourceStructural.parent_eq loserMember
  have childFacts := state.view.mem_topDown_iff.mp childMember
  have winnerNeLoser : selected.winner ≠ selected.loser := by
    intro equal
    have rankOrder := secondAllocation.agreement.rank_lt selectedMember
    rw [equal] at rankOrder
    exact Nat.lt_irrefl _ rankOrder
  have result := nested winnerParent loserParent winnerNeLoser childFacts.1
    (by simpa [Splay.Lazy.Canonical.sideOf] using childFacts.2)
  by_cases left : selected.loser.val < selected.winner.val
  · simpa [Splay.Lazy.Canonical.sideOf, left] using result
  · simpa [Splay.Lazy.Canonical.sideOf, left] using result

/-- Both ordinary fraction-admissible phases and the first two exempt phases
have the same stable restoration and potential accounting. -/
theorem ArticleSourcePairings.restoredTwoPhaseRichPassTrace_of_allocations_and_outermost
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ} {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches)
    {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (sourceShrinking : source.mode = .shrinking)
    (stable : state.Stable params)
    (rankEq : state.view.rank = snapshot.rank)
    (firstAllocation :
      ArticleBatchDestinationAllocation .first batches state)
    (originalSecondAllocation :
      ArticleBatchDestinationAllocation .second batches state)
    (admissible : source.passCount + 1 < params.exemptPasses ∨
      params.matchingNumerator * source.elements.length ≤
        params.matchingDenominator * firstAllocation.matching.length)
    (firstOutermost :
      BatchOutermostOrder state.view firstAllocation.matching)
    (secondOutermost :
      BatchOutermostOrder state.view originalSecondAllocation.matching) :
    batches.RestoredTwoPhaseRichPassTrace params state
      sourceId source firstAllocation := by
  have twoPhase : batches.TwoPhaseRichPassTrace params state
      sourceId source firstAllocation := by
    unfold ArticleRetainedPairingBatches.TwoPhaseRichPassTrace
    exact plan.exists_twoPhaseRichPassTrace_of_allocations_and_outermost sourceFound sourceElements sourceShrinking stable.valid
      stable.2.2.2.2.2 stable.2.1 stable.2.2.2.1 stable.2.2.2.2.1
      rankEq stable.2.2.1 firstAllocation
      originalSecondAllocation admissible firstOutermost secondOutermost
  exact plan.with_loserRestoration_of_invariants twoPhase stable.valid
    stable.2.2.2.2.2 rankEq sourceFound sourceElements sourceShrinking

end Splay.Accounting
