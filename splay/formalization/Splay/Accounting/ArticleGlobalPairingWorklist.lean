import Splay.Accounting.ArticleGlobalPairingFold

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST
open ArticleBatchDestinationAllocation

/-- One nonempty request-start source together with all data needed to run its
two article phases in the current stable state.  Transporting this record
changes only the current state; the source identifier, block, fraction
certificate, and retained rows remain frozen. -/
structure ArticleReadySourceWorkItem
    {n : ℕ} (key : ℕ) (snapshot : Snapshot n) (before : BST 0 n)
    (kinds : List SplayStepKind) (params : Interface.Parameters)
    (state : Lazy.State n) where
  elements : List (Interface.Element n)
  certificate :
    ArticleInternalPairingFractionCertificate kinds elements
      (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0)
  batches : ArticleRetainedPairingBatches snapshot before
    (Nat.le_refl n) key certificate.fraction.groups
  groupsNonempty : certificate.fraction.groups ≠ []
  sourceId : Interface.BlockId
  source : Lazy.Block n
  sourceFound : state.blocks[sourceId]? = some source
  sourceElements : source.elements = elements
  sourceShrinking : source.mode = .shrinking
  firstAllocation :
    ArticleBatchDestinationAllocation .first batches state
  secondAllocation :
    ArticleBatchDestinationAllocation .second batches state
  firstOutermost :
    BatchOutermostOrder state.view firstAllocation.matching
  secondOutermost :
    BatchOutermostOrder state.view secondAllocation.matching

namespace ArticleReadySourceWorkItem

/-- The checked loser/winner projection of one ready item. -/
def batch
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n}
    (item : ArticleReadySourceWorkItem key snapshot before kinds params state) :
    ArticleSourceLoserBatch n :=
  ArticleSourceLoserBatch.ofCertificate item.certificate item.batches
    item.firstAllocation.agreement item.secondAllocation.agreement

@[simp]
theorem batch_sourceElements
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n}
    (item : ArticleReadySourceWorkItem key snapshot before kinds params state) :
    item.batch.sourceElements = item.source.elements := by
  simpa [batch, ArticleSourceLoserBatch.ofCertificate] using
    item.sourceElements.symm

/-- A stable state with canonical nested-child order supplies both concrete
destination allocations and both outermost-order witnesses automatically. -/
theorem exists_of_certificate
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    (groupsNonempty : certificate.fraction.groups ≠ [])
    (stable : state.Stable params)
    (nested : state.view.NestedChildOrder)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (sourceShrinking : source.mode = .shrinking) :
    Nonempty
      { item :
          ArticleReadySourceWorkItem key snapshot before kinds params state //
        item.sourceId = sourceId ∧ item.source = source } := by
  obtain ⟨firstAllocation⟩ :=
    batches.exists_destinationAllocation .first state stable.valid
      stable.2.2.2.1
  obtain ⟨secondAllocation⟩ :=
    batches.exists_destinationAllocation .second state stable.valid
      stable.2.2.2.1
  have sourceInterfaceFound : state.toInterface.block? sourceId =
      some source.toInterface := by
    unfold Interface.State.block? Lazy.State.toInterface
    simpa using congrArg (Option.map Lazy.Block.toInterface) sourceFound
  have firstGeometric :=
    certificate.first_geometricMatching_of_allocation batches firstAllocation
      sourceInterfaceFound sourceElements sourceShrinking
  have firstOutermost :
      BatchOutermostOrder state.view firstAllocation.matching :=
    outermostOrder_of_nestedChildOrder stable.valid sourceFound
      firstGeometric nested
  have secondOutermost :
      BatchOutermostOrder state.view secondAllocation.matching :=
    articleSecondOutermostOrder_of_nestedChildOrder certificate batches
      sourceFound sourceElements stable.valid nested secondAllocation
  exact ⟨⟨{
      elements := elements
      certificate := certificate
      batches := batches
      groupsNonempty := groupsNonempty
      sourceId := sourceId
      source := source
      sourceFound := sourceFound
      sourceElements := sourceElements
      sourceShrinking := sourceShrinking
      firstAllocation := firstAllocation
      secondAllocation := secondAllocation
      firstOutermost := firstOutermost
      secondOutermost := secondOutermost
    }, rfl, rfl⟩⟩

/-- Transport a later ready item through an executed earlier source macro.
Distinct shrinking source identifiers preserve its block and allocations;
disjoint source payloads preserve both outermost-order witnesses. -/
def transportAfter
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n}
    (item : ArticleReadySourceWorkItem key snapshot before kinds params state)
    (earlier : ArticleExecutedSourceMacro params state)
    (sourceNe : item.sourceId ≠ earlier.sourceId)
    (payloadDisjoint :
      List.Disjoint earlier.batch.sourceElements item.source.elements) :
    ArticleReadySourceWorkItem key snapshot before kinds params earlier.final := by
  let firstAllocation := earlier.transportAllocation item.firstAllocation
  let secondAllocation := earlier.transportAllocation item.secondAllocation
  have winnersNeFirst :
      ∀ preceding ∈ earlier.batch.firstMatching ++
          earlier.batch.secondMatching,
        ∀ later ∈ firstAllocation.matching,
          preceding.winner ≠ later.winner := by
    intro preceding precedingMember later laterMember equal
    have precedingInSource :=
      earlier.batch.winner_mem_source preceding precedingMember
    have laterInSource : later.winner ∈ item.source.elements := by
      rw [item.sourceElements]
      exact item.certificate.first_winner_mem_source item.batches
        firstAllocation.agreement laterMember
    exact (List.disjoint_left.mp payloadDisjoint precedingInSource)
      (by simpa only [equal] using laterInSource)
  have winnersNeSecond :
      ∀ preceding ∈ earlier.batch.firstMatching ++
          earlier.batch.secondMatching,
        ∀ later ∈ secondAllocation.matching,
          preceding.winner ≠ later.winner := by
    intro preceding precedingMember later laterMember equal
    have precedingInSource :=
      earlier.batch.winner_mem_source preceding precedingMember
    have laterInSource : later.winner ∈ item.source.elements := by
      rw [item.sourceElements]
      exact item.certificate.second_winner_mem_source item.batches
        secondAllocation.agreement laterMember
    exact (List.disjoint_left.mp payloadDisjoint precedingInSource)
      (by simpa only [equal] using laterInSource)
  exact {
    elements := item.elements
    certificate := item.certificate
    batches := item.batches
    groupsNonempty := item.groupsNonempty
    sourceId := item.sourceId
    source := item.source
    sourceFound := earlier.preservesOtherShrinkingSource
      item.sourceFound item.sourceShrinking sourceNe
    sourceElements := item.sourceElements
    sourceShrinking := item.sourceShrinking
    firstAllocation := firstAllocation
    secondAllocation := secondAllocation
    firstOutermost := earlier.transportOutermost
      firstAllocation.matching (by
        rw [earlier.transportAllocation_matching item.firstAllocation]
        exact item.firstOutermost) winnersNeFirst
    secondOutermost := earlier.transportOutermost
      secondAllocation.matching (by
        rw [earlier.transportAllocation_matching item.secondAllocation]
        exact item.secondOutermost) winnersNeSecond
  }

@[simp]
theorem transportAfter_sourceId
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n}
    (item : ArticleReadySourceWorkItem key snapshot before kinds params state)
    (earlier : ArticleExecutedSourceMacro params state)
    (sourceNe : item.sourceId ≠ earlier.sourceId)
    (payloadDisjoint :
      List.Disjoint earlier.batch.sourceElements item.source.elements) :
    (item.transportAfter earlier sourceNe payloadDisjoint).sourceId =
      item.sourceId := rfl

@[simp]
theorem transportAfter_source_elements
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n}
    (item : ArticleReadySourceWorkItem key snapshot before kinds params state)
    (earlier : ArticleExecutedSourceMacro params state)
    (sourceNe : item.sourceId ≠ earlier.sourceId)
    (payloadDisjoint :
      List.Disjoint earlier.batch.sourceElements item.source.elements) :
    (item.transportAfter earlier sourceNe payloadDisjoint).source.elements =
      item.source.elements := rfl

end ArticleReadySourceWorkItem

/-- A request-level worklist execution together with the exact correspondence
between its chain batches and the frozen source payloads. -/
structure ArticleReadyWorklistExecution
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n}
    (items : List
      (ArticleReadySourceWorkItem key snapshot before kinds params state)) where
  chain : ArticleSourceMacroChain params state
  batchSourceElements_eq :
    chain.batches.map ArticleSourceLoserBatch.sourceElements =
      items.map fun item => item.source.elements

namespace ArticleReadyWorklistExecution

/-- A fully ready, duplicate-free request worklist executes sequentially to
one stable rich trace. -/
theorem exists_of_ready
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n}
    (items : List
      (ArticleReadySourceWorkItem key snapshot before kinds params state))
    (stable : state.Stable params)
    (rankEq : state.view.rank = snapshot.rank)
    (articleFraction :
      10 * params.matchingNumerator ≤ params.matchingDenominator)
    (idsNodup : (items.map fun item => item.sourceId).Nodup)
    (payloadsDisjoint :
      (items.map fun item => item.source.elements).Pairwise List.Disjoint) :
    Nonempty (ArticleReadyWorklistExecution items) := by
  cases items with
  | nil =>
      exact ⟨{
        chain := .nil state stable
        batchSourceElements_eq := rfl
      }⟩
  | cons head tail =>
      have idsParts := List.nodup_cons.mp idsNodup
      have payloadParts := List.pairwise_cons.mp payloadsDisjoint
      have restored :=
        head.certificate.restoredTwoPhaseRichPassTrace_of_allocations_and_outermost
          head.batches head.sourceFound head.sourceElements
          head.sourceShrinking stable rankEq articleFraction
          head.groupsNonempty head.firstAllocation head.secondAllocation
          head.firstOutermost head.secondOutermost
      obtain ⟨⟨executed, executedSourceId, executedSource⟩⟩ :=
        head.certificate.executedSourceMacro_of_restoredTwoPhase
          head.batches head.sourceFound head.sourceElements
          head.sourceShrinking stable rankEq head.firstAllocation restored
      have tailSourceNe : ∀ item ∈ tail,
          item.sourceId ≠ executed.sourceId := by
        intro item itemMember equal
        apply idsParts.1
        apply List.mem_map.mpr
        exact ⟨item, itemMember, by
          rw [executedSourceId] at equal
          exact equal⟩
      have tailPayloadDisjoint : ∀ item ∈ tail,
          List.Disjoint executed.batch.sourceElements
            item.source.elements := by
        intro item itemMember
        have headDisjoint := payloadParts.1 item.source.elements
          (List.mem_map.mpr ⟨item, itemMember, rfl⟩)
        rw [executed.sourceElements_eq, executedSource]
        exact headDisjoint
      let transportedTail := tail.attach.map fun item =>
        item.1.transportAfter executed
          (tailSourceNe item.1 item.2)
          (tailPayloadDisjoint item.1 item.2)
      have transportedIds :
          transportedTail.map (fun item => item.sourceId) =
            tail.map (fun item => item.sourceId) := by
        simp [transportedTail]
      have transportedPayloads :
          transportedTail.map (fun item => item.source.elements) =
            tail.map (fun item => item.source.elements) := by
        simp [transportedTail]
      have transportedIdsNodup :
          (transportedTail.map fun item => item.sourceId).Nodup := by
        rw [transportedIds]
        exact idsParts.2
      have transportedPayloadsDisjoint :
          (transportedTail.map fun item => item.source.elements).Pairwise
            List.Disjoint := by
        rw [transportedPayloads]
        exact payloadParts.2
      have finalRankEq : executed.final.view.rank = snapshot.rank :=
        executed.rank_eq.trans rankEq
      obtain ⟨tailExecution⟩ := exists_of_ready transportedTail
        executed.finalStable finalRankEq articleFraction
        transportedIdsNodup transportedPayloadsDisjoint
      refine ⟨{
        chain := .cons executed tailExecution.chain
        batchSourceElements_eq := ?_
      }⟩
      simp only [ArticleSourceMacroChain.batches, List.map_cons]
      rw [executed.sourceElements_eq, tailExecution.batchSourceElements_eq,
        transportedPayloads, executedSource]
termination_by items.length
decreasing_by simp_all

/-- Pairwise-disjoint request-start payloads therefore give a globally
duplicate-free residence-ending footprint for the constructed rich trace. -/
theorem leavingElements_nodup
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n}
    {items : List
      (ArticleReadySourceWorkItem key snapshot before kinds params state)}
    (execution : ArticleReadyWorklistExecution items)
    (payloadsDisjoint :
      (items.map fun item => item.source.elements).Pairwise List.Disjoint) :
    (operationLeavingElementsList
      (Lazy.eraseOperations execution.chain.events)).Nodup := by
  apply execution.chain.leavingElements_nodup
  have mapped :
      (execution.chain.batches.map
        ArticleSourceLoserBatch.sourceElements).Pairwise List.Disjoint := by
    rw [execution.batchSourceElements_eq]
    exact payloadsDisjoint
  exact (List.pairwise_map
    (f := ArticleSourceLoserBatch.sourceElements)
    (R := List.Disjoint)
    (l := execution.chain.batches)).mp mapped

end ArticleReadyWorklistExecution

end Splay.Accounting
