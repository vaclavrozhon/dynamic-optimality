import Splay.Accounting.ArticleGlobalPairingFold
import Splay.Accounting.ArticleSourceExecution

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST
open ArticleBatchDestinationAllocation

/-- One source with fixed selected rows and admissible first and second
passes. The quantitative certificate is needed only after the exempt passes.
Identifiers and selected rows remain fixed during sequential transport. -/
structure ArticleAdmissibleSourceWorkItem
    {n : ℕ} (key : ℕ) (snapshot : Snapshot n) (before : BST 0 n)
    (params : Interface.Parameters)
    (state : Lazy.State n) where
  elements : List (Interface.Element n)
  groups : List ℕ
  batches : ArticleRetainedPairingBatches snapshot before
    (Nat.le_refl n) key groups
  geometry : ArticleSourcePairings elements batches
  sourceId : Interface.BlockId
  source : Lazy.Block n
  sourceFound : state.blocks[sourceId]? = some source
  sourceElements : source.elements = elements
  sourceShrinking : source.mode = .shrinking
  admissible : source.passCount + 1 < params.exemptPasses ∨
    params.matchingNumerator * source.elements.length ≤
      params.matchingDenominator * groups.length
  firstAllocation :
    ArticleBatchDestinationAllocation .first batches state
  secondAllocation :
    ArticleBatchDestinationAllocation .second batches state
  firstOutermost :
    BatchOutermostOrder state.view firstAllocation.matching
  secondOutermost :
    BatchOutermostOrder state.view secondAllocation.matching

namespace ArticleAdmissibleSourceWorkItem

/-- The checked loser/winner projection of one ready item. -/
def batch
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {params : Interface.Parameters}
    {state : Lazy.State n}
    (item : ArticleAdmissibleSourceWorkItem key snapshot before params state) :
    ArticleSourceLoserBatch n :=
  ArticleSourceLoserBatch.ofSourcePairings item.geometry
    item.firstAllocation.agreement item.secondAllocation.agreement

@[simp]
theorem batch_sourceElements
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {params : Interface.Parameters}
    {state : Lazy.State n}
    (item : ArticleAdmissibleSourceWorkItem key snapshot before params state) :
    item.batch.sourceElements = item.source.elements := by
  simpa [batch, ArticleSourceLoserBatch.ofSourcePairings] using
    item.sourceElements.symm

/-- A stable state with canonical nested-child order supplies both concrete
destination allocations and both outermost-order witnesses automatically. -/
theorem exists_of_geometry
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {params : Interface.Parameters}
    {state : Lazy.State n}
    {elements : List (Interface.Element n)}
    {groups : List ℕ}
    {batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key groups}
    (geometry : ArticleSourcePairings elements batches)
    (stable : state.Stable params)
    (nested : state.view.NestedChildOrder)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (sourceShrinking : source.mode = .shrinking)
    (admissible : source.passCount + 1 < params.exemptPasses ∨
      params.matchingNumerator * source.elements.length ≤
        params.matchingDenominator * groups.length) :
    Nonempty
      { item :
          ArticleAdmissibleSourceWorkItem key snapshot before params state //
        item.sourceId = sourceId ∧ item.source = source ∧
          item.batches.rows = batches.rows } := by
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
    geometry.first_geometricMatching_of_allocation firstAllocation
      sourceInterfaceFound sourceElements sourceShrinking
  have firstOutermost :
      BatchOutermostOrder state.view firstAllocation.matching :=
    outermostOrder_of_nestedChildOrder stable.valid sourceFound
      firstGeometric nested
  have secondOutermost :
      BatchOutermostOrder state.view secondAllocation.matching :=
    geometry.secondOutermostOrder_of_nestedChildOrder
      sourceFound sourceElements stable.valid nested secondAllocation
  exact ⟨⟨{
      elements := elements
      groups := groups
      batches := batches
      geometry := geometry
      admissible := admissible
      sourceId := sourceId
      source := source
      sourceFound := sourceFound
      sourceElements := sourceElements
      sourceShrinking := sourceShrinking
      firstAllocation := firstAllocation
      secondAllocation := secondAllocation
      firstOutermost := firstOutermost
      secondOutermost := secondOutermost
    }, rfl, rfl, rfl⟩⟩

/-- Transport a later ready item through an executed earlier source macro.
Distinct shrinking source identifiers preserve its block and allocations;
disjoint source payloads preserve both outermost-order witnesses. -/
def transportAfter
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {params : Interface.Parameters}
    {state : Lazy.State n}
    (item : ArticleAdmissibleSourceWorkItem key snapshot before params state)
    (earlier : ArticleExecutedSourceMacro params state)
    (sourceNe : item.sourceId ≠ earlier.sourceId)
    (payloadDisjoint :
      List.Disjoint earlier.batch.sourceElements item.source.elements) :
    ArticleAdmissibleSourceWorkItem key snapshot before params earlier.final := by
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
      exact (item.geometry.endpoints_mem_source firstAllocation.agreement laterMember).1
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
      exact (item.geometry.endpoints_mem_source secondAllocation.agreement laterMember).1
    exact (List.disjoint_left.mp payloadDisjoint precedingInSource)
      (by simpa only [equal] using laterInSource)
  exact {
    elements := item.elements
    groups := item.groups
    batches := item.batches
    geometry := item.geometry
    admissible := item.admissible
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
    {params : Interface.Parameters}
    {state : Lazy.State n}
    (item : ArticleAdmissibleSourceWorkItem key snapshot before params state)
    (earlier : ArticleExecutedSourceMacro params state)
    (sourceNe : item.sourceId ≠ earlier.sourceId)
    (payloadDisjoint :
      List.Disjoint earlier.batch.sourceElements item.source.elements) :
    (item.transportAfter earlier sourceNe payloadDisjoint).sourceId =
      item.sourceId := rfl

@[simp]
theorem transportAfter_source_elements
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {params : Interface.Parameters}
    {state : Lazy.State n}
    (item : ArticleAdmissibleSourceWorkItem key snapshot before params state)
    (earlier : ArticleExecutedSourceMacro params state)
    (sourceNe : item.sourceId ≠ earlier.sourceId)
    (payloadDisjoint :
      List.Disjoint earlier.batch.sourceElements item.source.elements) :
    (item.transportAfter earlier sourceNe payloadDisjoint).source.elements =
      item.source.elements := rfl

end ArticleAdmissibleSourceWorkItem

/-- A request-level worklist execution together with the exact correspondence
between its chain batches and the frozen source payloads. -/
structure ArticleAdmissibleWorklistExecution
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {params : Interface.Parameters}
    {state : Lazy.State n}
    (items : List
      (ArticleAdmissibleSourceWorkItem key snapshot before params state)) where
  chain : ArticleSourceMacroChain params state
  firstPassSources_eq : chain.firstPassSources =
    items.map fun item => (item.source, item.batches.rows.length)
  shrinkingRefines : State.ShrinkingRefinement (fun owner => ∃ item ∈ items, item.source.owner = owner) state chain.final
  batchRowsAgreement : List.Forall₂
    (fun batch rows =>
      List.Forall₂ (fun row pairing => row.2.1 = [pairing.winner, pairing.loser]) rows batch.firstMatching ∧
      List.Forall₂ (fun row pairing => row.2.2 = [pairing.winner, pairing.loser]) rows batch.secondMatching)
    chain.batches (items.map fun item => item.batches.rows)
  batchSourceElements_eq :
    chain.batches.map ArticleSourceLoserBatch.sourceElements =
      items.map fun item => item.source.elements
  batchEndpoints_eq :
    (chain.batches.map fun batch =>
      (batch.firstMatching.flatMap (fun p => [p.winner, p.loser]),
        batch.secondMatching.flatMap (fun p => [p.winner, p.loser]))) =
      items.map fun item =>
        (item.batches.rows.flatMap (fun row => row.2.1),
          item.batches.rows.flatMap (fun row => row.2.2))

namespace ArticleAdmissibleWorklistExecution

/-- A fully ready, duplicate-free request worklist executes sequentially to
one stable rich trace. -/
theorem exists_of_ready
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {params : Interface.Parameters}
    {state : Lazy.State n}
    (items : List
      (ArticleAdmissibleSourceWorkItem key snapshot before params state))
    (stable : state.Stable params)
    (rankEq : state.view.rank = snapshot.rank)
    (idsNodup : (items.map fun item => item.sourceId).Nodup)
    (payloadsDisjoint :
      (items.map fun item => item.source.elements).Pairwise List.Disjoint) :
    Nonempty (ArticleAdmissibleWorklistExecution items) := by
  cases items with
  | nil =>
      exact ⟨{
        chain := .nil state stable
        firstPassSources_eq := rfl
        shrinkingRefines := State.ShrinkingRefinement.refl _ _
        batchRowsAgreement := .nil
        batchSourceElements_eq := rfl
        batchEndpoints_eq := rfl
      }⟩
  | cons head tail =>
      have idsParts := List.nodup_cons.mp idsNodup
      have payloadParts := List.pairwise_cons.mp payloadsDisjoint
      have restored :=
        head.geometry.restoredTwoPhaseRichPassTrace_of_allocations_and_outermost
          head.sourceFound head.sourceElements
          head.sourceShrinking stable rankEq
          head.firstAllocation head.secondAllocation (by
            simpa only [head.firstAllocation.agreement.matching_length_eq_eligibleGroups_length]
              using head.admissible)
          head.firstOutermost head.secondOutermost
      obtain ⟨⟨executed, executedSourceId, executedSource, firstAgreement, secondAgreement⟩⟩ :=
        head.geometry.executedSourceMacro_of_restoredTwoPhase
          head.sourceFound head.sourceElements
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
        executed.finalStable finalRankEq
        transportedIdsNodup transportedPayloadsDisjoint
      refine ⟨{
        chain := .cons executed tailExecution.chain
        firstPassSources_eq := ?_
        shrinkingRefines := ?_
        batchRowsAgreement := ?_
        batchSourceElements_eq := ?_
        batchEndpoints_eq := ?_
      }⟩
      · simp only [ArticleSourceMacroChain.firstPassSources, List.map_cons,
          tailExecution.firstPassSources_eq]
        congr 1
        · exact Prod.ext executedSource firstAgreement.length_eq.symm
        · simp [transportedTail, ArticleAdmissibleSourceWorkItem.transportAfter]
      · apply (executed.shrinkingRefines.mono (fun owner equal => ?_)).trans
          (tailExecution.shrinkingRefines.mono (fun owner selected => ?_))
        · exact ⟨head, List.mem_cons_self, by rw [executedSource] at equal; exact equal.symm⟩
        · obtain ⟨item, member, equal⟩ := selected
          obtain ⟨original, originalMember, itemEq⟩ := List.mem_map.mp member
          subst item
          exact ⟨original.val, List.mem_cons_of_mem _ original.property, equal⟩
      · apply List.Forall₂.cons ⟨firstAgreement, secondAgreement⟩
        simpa [transportedTail, ArticleAdmissibleSourceWorkItem.transportAfter] using tailExecution.batchRowsAgreement
      · simp only [ArticleSourceMacroChain.batches, List.map_cons]
        rw [executed.sourceElements_eq, tailExecution.batchSourceElements_eq,
          transportedPayloads, executedSource]
      · simp only [ArticleSourceMacroChain.batches, List.map_cons,
          tailExecution.batchEndpoints_eq]
        congr 1
        · simp only [firstAgreement.matchingEndpoints_eq_rows,
            secondAgreement.matchingEndpoints_eq_rows, articleRowSelection]
        · simp [transportedTail, ArticleAdmissibleSourceWorkItem.transportAfter]
termination_by items.length
decreasing_by simp_all

/-- Pairwise-disjoint request-start payloads therefore give a globally
duplicate-free residence-ending footprint for the constructed rich trace. -/
theorem leavingElements_nodup
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {params : Interface.Parameters}
    {state : Lazy.State n}
    {items : List
      (ArticleAdmissibleSourceWorkItem key snapshot before params state)}
    (execution : ArticleAdmissibleWorklistExecution items)
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

end ArticleAdmissibleWorklistExecution

end Splay.Accounting
