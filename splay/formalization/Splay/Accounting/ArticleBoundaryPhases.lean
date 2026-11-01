import Splay.Accounting.ArticlePreparedBoundarySources

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open ArticleBatchDestinationAllocation

/-- Both complete boundary phases use the same literal frozen row list. -/
structure ArticleBoundaryPhasesExecution {n key : ℕ} {snapshot : Snapshot n}
    {before : BST 0 n} {groups : List ℕ}
    (params : Interface.Parameters) (initial : Lazy.State n)
    (batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups) where
  firstAllocation : ArticleBatchDestinationAllocation .first batches initial
  first : ArticleBoundaryBatchExecution params initial firstAllocation.matching
  secondAllocation : ArticleBatchDestinationAllocation .second batches first.final
  second : ArticleBoundaryBatchExecution params first.final secondAllocation.matching

namespace ArticleBoundaryPhasesExecution

variable {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n} {groups : List ℕ}
  {params : Interface.Parameters} {initial : Lazy.State n}
  {batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups}
  (execution : ArticleBoundaryPhasesExecution params initial batches)

def events : List (Event n) := execution.first.events ++ execution.second.events

def final : Lazy.State n := execution.second.final

theorem trace : Trace params initial execution.events execution.final :=
  execution.first.trace.append execution.second.trace

theorem stable : execution.final.Stable params := execution.second.stable

theorem blocks_length_eq : execution.final.blocks.length = initial.blocks.length :=
  execution.second.blocks_length_eq.trans execution.first.blocks_length_eq

theorem shrinkingRefines : State.ShrinkingRefinement (fun _ => False) initial execution.final :=
  execution.first.shrinkingRefines.trans execution.second.shrinkingRefines

/-- Two genuine boundary insertions implement each leftover zig-zig row. -/
theorem inserts : Interface.totalInserts (eraseOperations execution.events) = 2 * batches.rows.length := by
  rw [events, eraseOperations_append, Interface.totalInserts_append, execution.first.inserts, execution.second.inserts]
  have firstLength := execution.firstAllocation.agreement.length_eq
  have secondLength := execution.secondAllocation.agreement.length_eq
  omega

theorem increases : Interface.totalIncreases (eraseOperations execution.events) ≤
    8 * params.valueBound * batches.rows.length := by
  rw [events, eraseOperations_append, Interface.totalIncreases_append]
  have firstCost := execution.first.increases
  have secondCost := execution.second.increases
  have firstLength := execution.firstAllocation.agreement.length_eq
  have secondLength := execution.secondAllocation.agreement.length_eq
  rw [← firstLength] at firstCost
  rw [← secondLength] at secondCost
  nlinarith

theorem leaving : operationLeavingElementsList (eraseOperations execution.events) =
    Interface.pairingLosers (execution.firstAllocation.matching ++ execution.secondAllocation.matching) := by
  rw [events, eraseOperations_append, operationLeavingElementsList_append,
    execution.first.leaving, execution.second.leaving]
  simp [Interface.pairingLosers]

/-- The two phases share one simultaneous endpoint with globally distinct losers. -/
def reparented (distinct : groups.Nodup) :
    BatchReparentedView initial.view (execution.firstAllocation.matching ++ execution.secondAllocation.matching) :=
  execution.first.reparented.append
    (execution.second.reparented.transportSource execution.first.view_eq)
    ((batches.rootGeometry distinct).firstSecondLosers_ne
      execution.firstAllocation.agreement execution.secondAllocation.agreement)

theorem reparented_view (distinct : groups.Nodup) :
    (execution.reparented distinct).view = execution.final.view := execution.second.view_eq

end ArticleBoundaryPhasesExecution

theorem ArticleSourceMacroChain.rank_eq {n : ℕ} {params : Interface.Parameters}
    {initial : Lazy.State n} (chain : ArticleSourceMacroChain params initial) :
    chain.final.view.rank = initial.view.rank := by
  induction chain with
  | nil => rfl
  | cons head tail ih => exact ih.trans head.rank_eq

/-- Instantiate both boundary phases at the actual endpoint of the complete
internal worklist. All source, destination, order and freshness obligations
are proved from the prepared request and the literal row partition. -/
theorem ArticleRequestPreparation.exists_boundaryPhases
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {before : BST 0 n} {key : Fin n} {initial : Lazy.State n}
    (preparation : ArticleRequestPreparation params snapshot before key initial)
    {groups : List ℕ}
    (allBatches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key.val groups)
    (distinct : groups.Nodup) (rankZero : snapshot.rank (valuePos key) = 0)
    (ordered : allBatches.Ordered)
    (valueBound : Analysis.contractedGap snapshot.maxRank ≤ params.valueBound)
    (execution : ArticleAdmissibleWorklistExecution
      (preparation.admissibleWorklist allBatches distinct rankZero)) :
    Nonempty (ArticleBoundaryPhasesExecution params execution.chain.final
      (preparation.boundaryBatches allBatches distinct rankZero)) := by
  let batches := preparation.boundaryBatches allBatches distinct rankZero
  have batchDistinct := allBatches.filtered_groups_nodup distinct
    (fun row => decide (row ∉ preparation.internalRows allBatches distinct rankZero))
  have batchOrder : batches.Ordered := ordered.filter _
  have stable := execution.chain.finalStable
  have ranks := execution.chain.rank_eq.trans preparation.represents.view_rank_eq
  have pairBound : ∀ winner loser : Interface.Element n,
      Analysis.contractedGap (snapshot.rank loser - snapshot.rank winner) ≤ params.valueBound := by
    intro winner loser
    exact (Analysis.contractedGap_mono ((Nat.sub_le _ _).trans (snapshot.rank_le_max loser))).trans valueBound
  obtain ⟨firstAllocation⟩ := batches.exists_destinationAllocation .first execution.chain.final stable.valid stable.2.2.2.1
  have firstNodup : (firstAllocation.matching.flatMap fun p => [p.winner, p.loser]).Nodup := by
    rw [firstAllocation.agreement.matchingEndpoints_eq_rows]
    exact batches.firstEndpoints_nodup
  obtain ⟨first⟩ := ArticleBoundaryBatchExecution.exists_of_ready firstAllocation.matching stable firstNodup
    (fun _ member => preparation.boundaryPair_shrinking allBatches distinct rankZero execution firstAllocation.agreement member)
    firstAllocation.richDestinations
    (by intro pairing member; rw [ranks]; exact firstAllocation.agreement.rank_lt member)
    (by intro pairing member; rw [ranks]; exact pairBound _ _)
    (preparation.boundaryPair_outermost allBatches distinct rankZero execution firstAllocation.agreement)
  obtain ⟨secondAllocation⟩ := batches.exists_destinationAllocation .second first.final first.stable.valid first.stable.2.2.2.1
  have secondNodup : (secondAllocation.matching.flatMap fun p => [p.winner, p.loser]).Nodup := by
    rw [secondAllocation.agreement.matchingEndpoints_eq_rows]
    exact batches.secondEndpoints_nodup
  have firstRanks : first.final.view.rank = snapshot.rank :=
    (congrArg HeapView.rank first.view_eq.symm).trans (first.reparented.rank_eq.trans ranks)
  have secondSources : ∀ pairing ∈ secondAllocation.matching,
      ∃ (id : Interface.BlockId) (source : Lazy.Block n),
        first.final.blocks[id]? = some source ∧ source.mode = .shrinking ∧ pairing.loser ∈ source.elements := by
    intro pairing member
    obtain ⟨id, source, found, shrinking, inside⟩ := preparation.boundaryPair_shrinking
      allBatches distinct rankZero execution secondAllocation.agreement member
    apply shrinkingResidence_after_trace first.trace found shrinking inside
    rw [first.leaving]
    intro removed
    obtain ⟨earlier, earlierMember, equal⟩ := List.mem_map.mp removed
    exact (batches.rootGeometry batchDistinct).firstSecondLosers_ne
      firstAllocation.agreement secondAllocation.agreement earlier earlierMember pairing member equal
  have secondOutermost : BatchOutermostOrder first.final.view secondAllocation.matching := by
    rw [← first.view_eq]
    exact first.reparented.secondOutermost_of_ordered batchOrder firstAllocation.agreement
      secondAllocation.agreement
      (preparation.boundaryPair_outermost allBatches distinct rankZero execution secondAllocation.agreement)
  obtain ⟨second⟩ := ArticleBoundaryBatchExecution.exists_of_ready secondAllocation.matching first.stable secondNodup
    secondSources secondAllocation.richDestinations
    (by intro pairing member; rw [firstRanks]; exact secondAllocation.agreement.rank_lt member)
    (by intro pairing member; rw [firstRanks]; exact pairBound _ _) secondOutermost
  exact ⟨⟨firstAllocation, first, secondAllocation, second⟩⟩

end Splay.Accounting
