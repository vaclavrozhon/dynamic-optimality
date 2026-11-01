import Splay.Accounting.ArticleGapPotential

namespace Splay.Accounting

open Splay.Lazy Splay.Rank Splay.Tree.BST

/-- Both retained phases pay one unit for every equal-valued pairing,
measured in their common original source state. -/
theorem ArticleSourcePairings.loserTarget_drop_of_agreement
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ}
    {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches)
    {phase : PairingPhase} {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement phase batches matching)
    {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    (rankEq : state.view.rank = snapshot.rank) :
    ∀ pairing ∈ matching,
      articlePairingLoserTarget state.view pairing ≤
        state.value pairing.loser ∧
      (state.value pairing.winner = state.value pairing.loser →
        articlePairingLoserTarget state.view pairing + 1 ≤ state.value pairing.loser) := by
  intro pairing pairingMember
  obtain ⟨row, rowMember, selectedEq⟩ :=
    agreement.exists_row_of_mem pairingMember
  obtain ⟨winner, firstLoser, secondLoser, candidates, firstEq,
      secondEq, firstAdjacent, secondAdjacent, losersNe, candidatePerm,
      candidateChunk, candidateSegment, firstInBlock, secondInBlock,
      winnerInside, firstInside, secondInside⟩ :=
    plan.row_inside rowMember
  have sourceMember : source ∈ state.blocks :=
    List.mem_of_getElem? sourceFound
  cases phase with
  | first =>
      simp only [articleRowSelection] at selectedEq
      have pairEq : [winner, firstLoser] =
          [pairing.winner, pairing.loser] :=
        firstEq.symm.trans selectedEq
      have endpoints : winner = pairing.winner ∧
          firstLoser = pairing.loser := by simpa using pairEq
      have rankOrder : state.view.rank pairing.winner <
          state.view.rank pairing.loser := by
        rw [rankEq]
        exact agreement.rank_lt pairingMember
      exact (internalPairingLoserTarget_le valid values sourceMember
        (by simpa [sourceElements, endpoints.1] using winnerInside)
        (by simpa [sourceElements, endpoints.2] using firstInside)
        rankOrder)
  | second =>
      simp only [articleRowSelection] at selectedEq
      have pairEq : [winner, secondLoser] =
          [pairing.winner, pairing.loser] :=
        secondEq.symm.trans selectedEq
      have endpoints : winner = pairing.winner ∧
          secondLoser = pairing.loser := by simpa using pairEq
      have rankOrder : state.view.rank pairing.winner <
          state.view.rank pairing.loser := by
        rw [rankEq]
        exact agreement.rank_lt pairingMember
      exact (internalPairingLoserTarget_le valid values sourceMember
        (by simpa [sourceElements, endpoints.1] using winnerInside)
        (by simpa [sourceElements, endpoints.2] using secondInside)
        rankOrder)


theorem ArticleInternalPairingFractionCertificate.loserTarget_drop_of_agreement
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {phase : PairingPhase} {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement phase batches matching)
    {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    (rankEq : state.view.rank = snapshot.rank) :
    ∀ pairing ∈ matching,
      articlePairingLoserTarget state.view pairing ≤
        state.value pairing.loser ∧
      (state.value pairing.winner = state.value pairing.loser →
        articlePairingLoserTarget state.view pairing + 1 ≤ state.value pairing.loser) := by
  exact (certificate.sourcePairings batches).loserTarget_drop_of_agreement
    agreement sourceFound sourceElements valid values rankEq

end Splay.Accounting
