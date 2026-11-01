import Splay.Accounting.ArticleGlobalLoserUniqueness
import Splay.Accounting.RequestStartBoundaryLineage
import Splay.Accounting.ArticlePairingGapDrop
import Splay.Accounting.ArticleEventCounts
import Splay.Accounting.ArticleReparentedComposition
import Splay.Lazy.ShrinkingRefinement

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST
open ArticleBatchDestinationAllocation

/-- The elements whose current block-residence episode is ended by one
visible operation.  This is the list-valued counterpart of
`operationLeavesElement`; the list form lets global accounting use `Nodup`.
-/
def operationLeavingElements {n : ℕ} :
    Interface.Operation n → List (Interface.Element n)
  | .delete _ deleted => [deleted]
  | .pass _ matching => Interface.pairingLosers matching
  | _ => []

@[simp]
theorem mem_operationLeavingElements_iff
    {n : ℕ} {operation : Interface.Operation n}
    {element : Interface.Element n} :
    element ∈ operationLeavingElements operation ↔
      operationLeavesElement operation element := by
  cases operation <;>
    simp [operationLeavingElements, operationLeavesElement, eq_comm]

/-- All residence-ending elements, in chronological operation order. -/
def operationLeavingElementsList {n : ℕ}
    (operations : List (Interface.Operation n)) :
    List (Interface.Element n) :=
  operations.flatMap operationLeavingElements

@[simp]
theorem operationLeavingElementsList_nil {n : ℕ} :
    operationLeavingElementsList ([] : List (Interface.Operation n)) = [] :=
  rfl

@[simp]
theorem operationLeavingElementsList_append
    {n : ℕ} (first second : List (Interface.Operation n)) :
    operationLeavingElementsList (first ++ second) =
      operationLeavingElementsList first ++
        operationLeavingElementsList second := by
  simp [operationLeavingElementsList]

/-- Winner preparation and restoration are value-only, so they never end a
block-residence episode. -/
@[simp]
theorem operationLeavingElementsList_adjustValueEvents
    {n : ℕ} (state : Lazy.State n) (element : Interface.Element n)
    (target : ℕ) :
    operationLeavingElementsList
        (Lazy.eraseOperations (state.adjustValueEvents element target)) = [] := by
  rw [Lazy.State.eraseOperations_adjustValueEvents]
  split <;>
    simp [operationLeavingElementsList, operationLeavingElements]

@[simp]
theorem eraseOperations_map_operation
    {n : ℕ} (operations : List (Interface.Operation n)) :
    Lazy.eraseOperations (operations.map Lazy.Event.operation) = operations := by
  induction operations with
  | nil => rfl
  | cons operation operations ih =>
      change operation ::
          Lazy.eraseOperations (operations.map Lazy.Event.operation) =
        operation :: operations
      rw [ih]

/-- A list of rich value-change events has no residence-ending element. -/
@[simp]
theorem operationLeavingElementsList_map_valueChangeEvents
    {n : ℕ} (elements : List (Interface.Element n))
    (delta : Interface.ValueDelta) :
    operationLeavingElementsList
        (Lazy.eraseOperations
          (elements.map fun element =>
            Lazy.Event.operation
              (Interface.Operation.valueChange element delta))) = [] := by
  rw [show
    (elements.map fun element =>
        Lazy.Event.operation
          (Interface.Operation.valueChange element delta)) =
      (elements.map fun element =>
        Interface.Operation.valueChange element delta).map
          Lazy.Event.operation by
    simp]
  rw [eraseOperations_map_operation]
  simp [operationLeavingElementsList, operationLeavingElements]

/-- One concrete article pass has exactly its matching losers as its leaving
footprint; the surrounding winner value changes contribute nothing. -/
@[simp]
theorem operationLeavingElementsList_articlePairingPassEvents
    {n : ℕ} (state : Lazy.State n) (sourceId : Interface.BlockId)
    (matching : List (Interface.Pairing n)) :
    operationLeavingElementsList
        (Lazy.eraseOperations
          (articlePairingPassEvents state sourceId matching)) =
      Interface.pairingLosers matching := by
  unfold articlePairingPassEvents
  simp only [Lazy.eraseOperations_append, operationLeavingElementsList_append,
    operationLeavingElementsList_map_valueChangeEvents]
  simp [operationLeavingElementsList, operationLeavingElements,
    Lazy.eraseOperations, Lazy.Event.operations]

/-- Loser-value restoration has an empty residence-ending footprint. -/
@[simp]
theorem operationLeavingElementsList_restoreArticlePairingLoserEvents
    {n : ℕ} (view : Lazy.HeapView n) (state : Lazy.State n)
    (matching : List (Interface.Pairing n)) :
    operationLeavingElementsList
        (Lazy.eraseOperations
          (restoreArticlePairingLoserEvents view state matching)) = [] := by
  induction matching generalizing state with
  | nil =>
      rfl
  | cons pairing matching ih =>
      rw [restoreArticlePairingLoserEvents, Lazy.eraseOperations_append,
        operationLeavingElementsList_append,
        operationLeavingElementsList_adjustValueEvents, ih]
      rfl

/-- The uniform projection of one executed source macro that a global fold
needs.  It retains the exact rich trace, its stable endpoint, the checked
source-local loser batch, and the equality between that batch and the visible
residence-ending footprint. -/
structure ArticleExecutedSourceMacro
    {n : ℕ} (params : Interface.Parameters) (initial : Lazy.State n) where
  sourceId : Interface.BlockId
  source : Lazy.Block n
  sourceFound : initial.blocks[sourceId]? = some source
  sourceShrinking : source.mode = .shrinking
  batch : ArticleSourceLoserBatch n
  sourceElements_eq : batch.sourceElements = source.elements
  events : List (Lazy.Event n)
  initialPass : ∃ (winners : List (Interface.Element n)) (suffix : List (Interface.Operation n)),
    eraseOperations events =
      (winners.map fun winner => Interface.Operation.valueChange winner .decrease) ++
        .pass sourceId batch.firstMatching :: suffix
  final : Lazy.State n
  trace : Lazy.Trace params initial events final
  finalStable : final.Stable params
  rank_eq : final.view.rank = initial.view.rank
  view_reparented : ∃ after : BatchReparentedView initial.view
    (batch.firstMatching ++ batch.secondMatching), after.view = final.view
  preservesOtherShrinkingSource :
    ∀ {queriedId : Interface.BlockId} {queried : Lazy.Block n},
      initial.blocks[queriedId]? = some queried →
      queried.mode = .shrinking → queriedId ≠ sourceId →
      final.blocks[queriedId]? = some queried
  preservesGrowingBlock :
    ∀ {queriedId : Interface.BlockId} {queried : Lazy.Block n},
      initial.blocks[queriedId]? = some queried → queried.mode = .growing →
      (∀ pairing ∈ batch.firstMatching ++ batch.secondMatching, pairing.winner ≠ queried.owner) →
      final.blocks[queriedId]? = some queried
  transportAllocation :
    ∀ {lower upper key : ℕ} {snapshot : Snapshot n}
      {before : BST lower upper} {upper_le_n : upper ≤ n}
      {eligibleGroups : List ℕ} {phase : PairingPhase}
      {otherBatches : ArticleRetainedPairingBatches
        snapshot before upper_le_n key eligibleGroups},
      ArticleBatchDestinationAllocation phase otherBatches initial →
        ArticleBatchDestinationAllocation phase otherBatches final
  transportAllocation_matching :
    ∀ {lower upper key : ℕ} {snapshot : Snapshot n}
      {before : BST lower upper} {upper_le_n : upper ≤ n}
      {eligibleGroups : List ℕ} {phase : PairingPhase}
      {otherBatches : ArticleRetainedPairingBatches
        snapshot before upper_le_n key eligibleGroups}
      (allocation :
        ArticleBatchDestinationAllocation phase otherBatches initial),
      (transportAllocation allocation).matching = allocation.matching
  transportOutermost :
    ∀ (later : List (Interface.Pairing n)),
      BatchOutermostOrder initial.view later →
      (∀ earlier ∈ batch.firstMatching ++ batch.secondMatching,
        ∀ laterPairing ∈ later,
          earlier.winner ≠ laterPairing.winner) →
      BatchOutermostOrder final.view later
  leavingElements_eq :
    operationLeavingElementsList (Lazy.eraseOperations events) =
      Interface.pairingLosers
        (batch.firstMatching ++ batch.secondMatching)
  goodCount : ℕ
  activity_eq_pairings : Interface.totalActivity (eraseOperations events) =
    (batch.firstMatching ++ batch.secondMatching).length
  inserts_eq_zero : Interface.totalInserts (eraseOperations events) = 0
  increases_eq_good : Interface.totalIncreases (eraseOperations events) = goodCount
  gap_drop : geometricGapPotential final + goodCount ≤ geometricGapPotential initial
  blocks_length_eq : final.blocks.length = initial.blocks.length
  shrinkingRefines : State.ShrinkingRefinement (fun owner => owner = source.owner) initial final

theorem ArticleSourcePairings.executedSourceMacro_of_restoredTwoPhase
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
    (restored :
      batches.RestoredTwoPhaseRichPassTrace params state
        sourceId source firstAllocation) :
    Nonempty { executed : ArticleExecutedSourceMacro params state //
      executed.sourceId = sourceId ∧ executed.source = source ∧
        ArticleBatchEndpointAgreement .first batches executed.batch.firstMatching ∧
        ArticleBatchEndpointAgreement .second batches executed.batch.secondMatching } := by
  unfold ArticleRetainedPairingBatches.RestoredTwoPhaseRichPassTrace at restored
  obtain ⟨afterFirst, firstIntervalGap, firstIntervalGapEq,
      middleValid, middleValueEq, secondAllocation, afterSecond,
      secondIntervalGap, secondIntervalGapEq, fullTrace, noInserts,
      noIncreases, finalViewEq, loserValues, finalValues, finalStable⟩ :=
    restored
  let firstWinners :=
    articleGoodWinners state firstAllocation.matching
  let firstPrepared := decreaseEach state firstWinners
  let firstPassed := firstPrepared.passAtView afterFirst.view sourceId source
    firstAllocation.matching firstIntervalGap
  let middle := increaseEach firstPassed firstWinners
  let secondSource := source.afterPassSource
    firstAllocation.matching firstIntervalGap
  let secondWinners :=
    articleGoodWinners middle secondAllocation.matching
  let secondPrepared := decreaseEach middle secondWinners
  let secondPassed := secondPrepared.passAtView afterSecond.view sourceId
    secondSource secondAllocation.matching secondIntervalGap
  let passFinal := increaseEach secondPassed secondWinners
  let matching :=
    firstAllocation.matching ++ secondAllocation.matching
  let final := restoreArticlePairingLosers state.view passFinal matching
  let restorationEvents :=
    restoreArticlePairingLoserEvents state.view passFinal matching
  let events :=
    articlePairingPassEvents state sourceId firstAllocation.matching ++
      articlePairingPassEvents middle sourceId secondAllocation.matching ++
        restorationEvents
  let batch := ArticleSourceLoserBatch.ofSourcePairings plan
    firstAllocation.agreement secondAllocation.agreement
  have middleView : middle.view = afterFirst.view := by
    simp [middle, firstPassed, firstPrepared, firstWinners]
  let secondReparented := afterSecond.transportSource middleView.symm
  let reparented := afterFirst.append secondReparented
    (plan.firstSecondLosers_ne firstAllocation.agreement secondAllocation.agreement)
  have reparentedView : reparented.view = final.view := by
    change afterSecond.view = final.view
    exact finalViewEq.symm
  refine ⟨⟨{
    sourceId := sourceId
    source := source
    sourceFound := sourceFound
    sourceShrinking := sourceShrinking
    batch := batch
    sourceElements_eq := ?_
    events := events
    initialPass := ?_
    final := final
    trace := ?_
    finalStable := ?_
    rank_eq := ?_
    view_reparented := ⟨reparented, reparentedView⟩
    preservesOtherShrinkingSource := ?_
    preservesGrowingBlock := ?_
    transportAllocation := ?_
    transportAllocation_matching := ?_
    transportOutermost := ?_
    leavingElements_eq := ?_
    goodCount := firstWinners.length + secondWinners.length
    activity_eq_pairings := ?_
    inserts_eq_zero := ?_
    increases_eq_good := ?_
    gap_drop := ?_
    blocks_length_eq := ?_
    shrinkingRefines := ?_
  }, rfl, rfl, firstAllocation.agreement, secondAllocation.agreement⟩⟩
  · simpa [batch, ArticleSourceLoserBatch.ofSourcePairings] using
      sourceElements.symm
  · refine ⟨firstWinners, eraseOperations
      ((firstWinners.map fun winner => Event.operation (.valueChange winner .increase)) ++
        articlePairingPassEvents middle sourceId secondAllocation.matching ++ restorationEvents), ?_⟩
    simp [events, articlePairingPassEvents, firstWinners, batch,
      ArticleSourceLoserBatch.ofSourcePairings, eraseOperations, Event.operations,
      List.append_assoc, List.flatMap_map, ← List.map_eq_flatMap]
  · simpa [events, final, restorationEvents, matching, passFinal,
      secondPassed, secondPrepared, secondWinners, secondSource, middle,
      firstPassed, firstPrepared, firstWinners] using fullTrace
  · simpa [final, restorationEvents, matching, passFinal, secondPassed,
      secondPrepared, secondWinners, secondSource, middle, firstPassed,
      firstPrepared, firstWinners] using finalStable
  · calc
      final.view.rank = afterSecond.view.rank := by
        rw [show final.view = afterSecond.view by
          simpa [final, passFinal, secondPassed, secondPrepared,
            secondWinners, secondSource, middle, firstPassed,
            firstPrepared, firstWinners] using finalViewEq]
      _ = middle.view.rank := afterSecond.rank_eq
      _ = afterFirst.view.rank := by
        simp [middle, firstPassed, firstPrepared, firstWinners]
      _ = state.view.rank := afterFirst.rank_eq
  · intro queriedId queried queriedFound queriedShrinking queriedNeSource
    have firstDestinationNe : ∀ pairing ∈ firstAllocation.matching,
        pairing.destination ≠ queriedId := by
      intro pairing pairingMember destinationEq
      obtain ⟨destination, destinationFound, destinationGrowing,
          destinationOwner, destinationSide⟩ :=
        firstAllocation.richDestinations pairing pairingMember
      rw [destinationEq, queriedFound] at destinationFound
      have destinationEqBlock : destination = queried :=
        Option.some.inj destinationFound.symm
      rw [destinationEqBlock, queriedShrinking] at destinationGrowing
      contradiction
    have firstQueriedFound : firstPassed.blocks[queriedId]? = some queried := by
      change (Lazy.Block.passBlocks firstPrepared.blocks sourceId source
        firstAllocation.matching firstIntervalGap)[queriedId]? = some queried
      rw [Lazy.Block.passBlocks_getElem?_of_ne]
      · simpa [firstPrepared, firstWinners] using queriedFound
      · exact queriedNeSource
      · exact firstDestinationNe
    have middleQueriedFound : middle.blocks[queriedId]? = some queried := by
      simpa [middle] using firstQueriedFound
    have secondDestinationNe : ∀ pairing ∈ secondAllocation.matching,
        pairing.destination ≠ queriedId := by
      intro pairing pairingMember destinationEq
      obtain ⟨destination, destinationFound, destinationGrowing,
          destinationOwner, destinationSide⟩ :=
        secondAllocation.richDestinations pairing pairingMember
      rw [destinationEq, middleQueriedFound] at destinationFound
      have destinationEqBlock : destination = queried :=
        Option.some.inj destinationFound.symm
      rw [destinationEqBlock, queriedShrinking] at destinationGrowing
      contradiction
    have secondPreparedQueriedFound :
        secondPrepared.blocks[queriedId]? = some queried := by
      simpa [secondPrepared, secondWinners] using middleQueriedFound
    have secondQueriedFound :
        secondPassed.blocks[queriedId]? = some queried := by
      change (Lazy.Block.passBlocks secondPrepared.blocks sourceId secondSource
        secondAllocation.matching secondIntervalGap)[queriedId]? = some queried
      rw [Lazy.Block.passBlocks_getElem?_of_ne]
      · exact secondPreparedQueriedFound
      · exact queriedNeSource
      · exact secondDestinationNe
    simpa [final, passFinal, matching] using secondQueriedFound
  · intro queriedId queried queriedFound queriedGrowing notWinner
    change (∀ pairing ∈ firstAllocation.matching ++ secondAllocation.matching, pairing.winner ≠ queried.owner) at notWinner
    have queriedNeSource : queriedId ≠ sourceId := by
      intro equal
      rw [equal, sourceFound] at queriedFound
      have blocksEq := Option.some.inj queriedFound
      rw [← blocksEq, sourceShrinking] at queriedGrowing
      contradiction
    have firstDestinationNe : ∀ pairing ∈ firstAllocation.matching,
        pairing.destination ≠ queriedId := by
      intro pairing pairingMember destinationEq
      obtain ⟨destination, destinationFound, destinationGrowing,
          destinationOwner, destinationSide⟩ :=
        firstAllocation.richDestinations pairing pairingMember
      rw [destinationEq, queriedFound] at destinationFound
      have destinationEqBlock : destination = queried :=
        Option.some.inj destinationFound.symm
      rw [destinationEqBlock] at destinationOwner
      exact notWinner pairing (List.mem_append_left _ pairingMember) destinationOwner.symm
    have firstQueriedFound : firstPassed.blocks[queriedId]? = some queried := by
      change (Lazy.Block.passBlocks firstPrepared.blocks sourceId source
        firstAllocation.matching firstIntervalGap)[queriedId]? = some queried
      rw [Lazy.Block.passBlocks_getElem?_of_ne]
      · simpa [firstPrepared, firstWinners] using queriedFound
      · exact queriedNeSource
      · exact firstDestinationNe
    have middleQueriedFound : middle.blocks[queriedId]? = some queried := by
      simpa [middle] using firstQueriedFound
    have secondDestinationNe : ∀ pairing ∈ secondAllocation.matching,
        pairing.destination ≠ queriedId := by
      intro pairing pairingMember destinationEq
      obtain ⟨destination, destinationFound, destinationGrowing,
          destinationOwner, destinationSide⟩ :=
        secondAllocation.richDestinations pairing pairingMember
      rw [destinationEq, middleQueriedFound] at destinationFound
      have destinationEqBlock : destination = queried :=
        Option.some.inj destinationFound.symm
      rw [destinationEqBlock] at destinationOwner
      exact notWinner pairing (List.mem_append_right _ pairingMember) destinationOwner.symm
    have secondPreparedQueriedFound :
        secondPrepared.blocks[queriedId]? = some queried := by
      simpa [secondPrepared, secondWinners] using middleQueriedFound
    have secondQueriedFound :
        secondPassed.blocks[queriedId]? = some queried := by
      change (Lazy.Block.passBlocks secondPrepared.blocks sourceId secondSource
        secondAllocation.matching secondIntervalGap)[queriedId]? = some queried
      rw [Lazy.Block.passBlocks_getElem?_of_ne]
      · exact secondPreparedQueriedFound
      · exact queriedNeSource
      · exact secondDestinationNe
    simpa [final, passFinal, matching] using secondQueriedFound
  · intro lower upper otherKey otherSnapshot otherBefore upperLe
      eligibleGroups phase otherBatches allocation
    let firstPreparedAllocation :
        ArticleBatchDestinationAllocation phase otherBatches firstPrepared :=
      allocation.transport_blocks_eq (by
        simp [firstPrepared, firstWinners])
    have firstPreparedSourceFound :
        firstPrepared.blocks[sourceId]? = some source := by
      simpa [firstPrepared, firstWinners] using sourceFound
    let afterFirstAllocation :
        ArticleBatchDestinationAllocation phase otherBatches firstPassed :=
      firstPreparedAllocation.transport_after_passAtView
        firstPreparedSourceFound sourceShrinking
        firstAllocation.destinationsNodup afterFirst.view firstIntervalGap
    let middleAllocation :
        ArticleBatchDestinationAllocation phase otherBatches middle :=
      afterFirstAllocation.transport_blocks_eq (by
        simp [middle, firstPassed, firstWinners])
    have sourceInterfaceFound : state.toInterface.block? sourceId =
        some source.toInterface := by
      unfold Interface.State.block? Lazy.State.toInterface
      simpa using congrArg (Option.map Lazy.Block.toInterface) sourceFound
    have firstDestinationsNeSource :
        ∀ pairing ∈ firstAllocation.matching,
          pairing.destination ≠ sourceId := by
      intro pairing pairingMember
      exact (firstAllocation.destinations_ne_source sourceInterfaceFound
        sourceShrinking pairing pairingMember).1
    have middleSourceFound : middle.blocks[sourceId]? = some secondSource := by
      rw [show middle.blocks = firstPassed.blocks by simp [middle]]
      change (Lazy.Block.passBlocks firstPrepared.blocks sourceId source
        firstAllocation.matching firstIntervalGap)[sourceId]? =
          some secondSource
      exact Lazy.Block.passBlocks_source_getElem? firstPrepared.blocks
        sourceId source firstAllocation.matching firstIntervalGap
        firstPreparedSourceFound firstDestinationsNeSource
    have secondSourceShrinking : secondSource.mode = .shrinking := by
      simp [secondSource, Lazy.Block.afterPassSource, sourceShrinking]
    let secondPreparedAllocation :
        ArticleBatchDestinationAllocation phase otherBatches secondPrepared :=
      middleAllocation.transport_blocks_eq (by
        simp [secondPrepared, secondWinners])
    have secondPreparedSourceFound :
        secondPrepared.blocks[sourceId]? = some secondSource := by
      simpa [secondPrepared, secondWinners] using middleSourceFound
    let afterSecondAllocation :
        ArticleBatchDestinationAllocation phase otherBatches secondPassed :=
      secondPreparedAllocation.transport_after_passAtView
        secondPreparedSourceFound secondSourceShrinking
        secondAllocation.destinationsNodup afterSecond.view secondIntervalGap
    exact afterSecondAllocation.transport_blocks_eq (by
      simp [final, passFinal, matching])
  · intro lower upper otherKey otherSnapshot otherBefore upperLe
      eligibleGroups phase otherBatches allocation
    rfl
  · intro later base winnersNe
    have firstWinnersNe : ∀ earlier ∈ firstAllocation.matching,
        ∀ laterPairing ∈ later,
          earlier.winner ≠ laterPairing.winner := by
      intro earlier earlierMember laterPairing laterMember
      exact winnersNe earlier
        (by simp [batch, ArticleSourceLoserBatch.ofSourcePairings, earlierMember])
        laterPairing laterMember
    have afterFirstOrder : BatchOutermostOrder afterFirst.view later :=
      afterFirst.outermostOrder_after_of_winners_ne base firstWinnersNe
    have middleOrder : BatchOutermostOrder middle.view later := by
      simpa [middle, firstPassed, firstPrepared, firstWinners] using
        afterFirstOrder
    have secondWinnersNe : ∀ earlier ∈ secondAllocation.matching,
        ∀ laterPairing ∈ later,
          earlier.winner ≠ laterPairing.winner := by
      intro earlier earlierMember laterPairing laterMember
      exact winnersNe earlier
        (by simp [batch, ArticleSourceLoserBatch.ofSourcePairings, earlierMember])
        laterPairing laterMember
    have afterSecondOrder : BatchOutermostOrder afterSecond.view later :=
      afterSecond.outermostOrder_after_of_winners_ne
        middleOrder secondWinnersNe
    have finalView : final.view = afterSecond.view := by
      simpa [final, passFinal, secondPassed, secondPrepared, secondWinners,
        secondSource, middle, firstPassed, firstPrepared, firstWinners] using
        finalViewEq
    rw [finalView]
    exact afterSecondOrder
  · simp [events, restorationEvents, batch,
      ArticleSourceLoserBatch.ofSourcePairings,
      Lazy.eraseOperations_append, Interface.pairingLosers]
  · simp [events, restorationEvents, batch, ArticleSourceLoserBatch.ofSourcePairings,
      eraseOperations_append, Interface.totalActivity_append]
  · have restorationZero : Interface.totalInserts (eraseOperations restorationEvents) = 0 := noInserts
    simp only [events, eraseOperations_append]
    rw [show Interface.totalInserts
        (eraseOperations (articlePairingPassEvents state sourceId firstAllocation.matching) ++
          eraseOperations (articlePairingPassEvents middle sourceId secondAllocation.matching) ++
            eraseOperations restorationEvents) =
        Interface.totalInserts (eraseOperations (articlePairingPassEvents state sourceId firstAllocation.matching)) +
          Interface.totalInserts (eraseOperations (articlePairingPassEvents middle sourceId secondAllocation.matching)) +
            Interface.totalInserts (eraseOperations restorationEvents) by simp [Interface.totalInserts, Nat.add_assoc]]
    simp [restorationZero]
  · have restorationZero : Interface.totalIncreases (eraseOperations restorationEvents) = 0 := noIncreases
    simp only [events, eraseOperations_append]
    rw [show Interface.totalIncreases
        (eraseOperations (articlePairingPassEvents state sourceId firstAllocation.matching) ++
          eraseOperations (articlePairingPassEvents middle sourceId secondAllocation.matching) ++
            eraseOperations restorationEvents) =
        Interface.totalIncreases (eraseOperations (articlePairingPassEvents state sourceId firstAllocation.matching)) +
          Interface.totalIncreases (eraseOperations (articlePairingPassEvents middle sourceId secondAllocation.matching)) +
            Interface.totalIncreases (eraseOperations restorationEvents) by simp [Interface.totalIncreases, Nat.add_assoc]]
    simp [restorationZero, firstWinners, secondWinners]
  · have secondEndpoints : (secondAllocation.matching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]).Nodup := by
      rw [secondAllocation.agreement.matchingEndpoints_eq_rows]
      simpa [articleRowSelection] using batches.secondEndpoints_nodup
    have passValue : passFinal.value = state.value :=
      (articlePassRestoredValue middle secondWinners (articleGoodWinners_nodup secondEndpoints)
        (fun element _ => (middleValid.toInterface.2.1 element).1)
        afterSecond.view sourceId secondSource secondAllocation.matching secondIntervalGap).trans middleValueEq
    have drop := restoreArticlePairingLosers_pays_good state.view state passFinal matching passValue
      (plan.twoPhaseLosers_nodup firstAllocation.agreement secondAllocation.agreement) (by
        intro pairing member
        rcases List.mem_append.mp member with first | second
        · exact plan.loserTarget_drop_of_agreement firstAllocation.agreement
            sourceFound sourceElements stable.valid stable.2.2.2.2.2 rankEq pairing first
        · exact plan.loserTarget_drop_of_agreement secondAllocation.agreement
            sourceFound sourceElements stable.valid stable.2.2.2.2.2 rankEq pairing second)
    have middleValue : middle.value = state.value := middleValueEq
    have goodEq : (articleGoodWinners state matching).length = firstWinners.length + secondWinners.length := by
      simp only [matching, firstWinners, secondWinners, articleGoodWinners, articleGoodPairings,
        List.filter_append, List.map_append, List.length_append, middleValue]
    rw [goodEq] at drop
    rw [geometricGapPotential_eq stable.2.1 stable.2.2.2.2.2,
      geometricGapPotential_eq finalStable.2.1 finalStable.2.2.2.2.2]
    exact drop
  · simp [final, passFinal, secondPassed, secondPrepared, middle, firstPassed, firstPrepared,
      State.passAtView_blocks, State.pass]

  · have firstFound : firstPrepared.blocks[sourceId]? = some source := by simpa [firstPrepared] using sourceFound
    have firstDestinations : ∀ pairing ∈ firstAllocation.matching, ∃ block : Lazy.Block n,
        firstPrepared.blocks[pairing.destination]? = some block ∧ block.mode = .growing := by
      intro pairing member
      obtain ⟨block, found, growing, _, _⟩ := firstAllocation.richDestinations pairing member
      exact ⟨block, by simpa [firstPrepared] using found, growing⟩
    have firstRefines := firstPrepared.passAtView_shrinkingRefinement afterFirst.view sourceId source
      firstAllocation.matching firstIntervalGap firstFound sourceShrinking firstAllocation.destinationsNodup firstDestinations
    have destinationsNe : ∀ pairing ∈ firstAllocation.matching, pairing.destination ≠ sourceId := by
      intro pairing member equal
      obtain ⟨block, found, growing⟩ := firstDestinations pairing member
      rw [equal, firstFound] at found
      have same := Option.some.inj found
      rw [← same, sourceShrinking] at growing
      contradiction
    have middleFound : middle.blocks[sourceId]? = some secondSource := by
      rw [show middle.blocks = firstPassed.blocks by simp [middle]]
      change (Block.passBlocks firstPrepared.blocks sourceId source firstAllocation.matching firstIntervalGap)[sourceId]? = _
      exact Block.passBlocks_source_getElem? _ _ _ _ _ firstFound destinationsNe
    have secondFound : secondPrepared.blocks[sourceId]? = some secondSource := by simpa [secondPrepared] using middleFound
    have secondDestinations : ∀ pairing ∈ secondAllocation.matching, ∃ block : Lazy.Block n,
        secondPrepared.blocks[pairing.destination]? = some block ∧ block.mode = .growing := by
      intro pairing member
      obtain ⟨block, found, growing, _, _⟩ := secondAllocation.richDestinations pairing member
      exact ⟨block, by simpa [secondPrepared, middle, firstPassed, firstPrepared, firstWinners] using found, growing⟩
    have secondRefines := secondPrepared.passAtView_shrinkingRefinement afterSecond.view sourceId secondSource
      secondAllocation.matching secondIntervalGap secondFound sourceShrinking secondAllocation.destinationsNodup secondDestinations
    have beforeFirst : State.ShrinkingRefinement (fun owner => owner = source.owner) state firstPrepared :=
      State.ShrinkingRefinement.of_blocks_eq _ (by simp [firstPrepared])
    have between : State.ShrinkingRefinement (fun owner => owner = source.owner) firstPassed secondPrepared :=
      State.ShrinkingRefinement.of_blocks_eq _ (by simp [secondPrepared, middle])
    have afterSecondFrame : State.ShrinkingRefinement (fun owner => owner = source.owner) secondPassed final :=
      State.ShrinkingRefinement.of_blocks_eq _ (by simp [final, passFinal])
    exact (((beforeFirst.trans firstRefines).trans between).trans secondRefines).trans afterSecondFrame

namespace ArticleInternalPairingFractionCertificate

/-- Forget the internal existential states of a restored two-phase macro and
export exactly the compositional record used by request-level accounting. -/
theorem executedSourceMacro_of_restoredTwoPhase
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (sourceShrinking : source.mode = .shrinking)
    (stable : state.Stable params)
    (rankEq : state.view.rank = snapshot.rank)
    (firstAllocation :
      ArticleBatchDestinationAllocation .first batches state)
    (restored :
      certificate.RestoredTwoPhaseRichPassTrace batches params state
        sourceId source firstAllocation) :
    Nonempty { executed : ArticleExecutedSourceMacro params state //
      executed.sourceId = sourceId ∧ executed.source = source } := by
  obtain ⟨⟨executed, sourceIdEq, sourceEq, _firstAgreement, _secondAgreement⟩⟩ :=
    (certificate.sourcePairings batches).executedSourceMacro_of_restoredTwoPhase
      sourceFound sourceElements sourceShrinking stable rankEq firstAllocation restored
  exact ⟨⟨executed, sourceIdEq, sourceEq⟩⟩

end ArticleInternalPairingFractionCertificate

/-- If all residence-ending occurrences in an operation list are globally
unique, then an element leaving at position `operationIndex` did not leave at
any earlier position.

This is the generic chronology lemma needed by article pairing.  It separates
the combinatorial fact (global loser uniqueness) from the trace occurrence
bookkeeping used by boundary-lineage accounting. -/
theorem noPriorLeave_of_operationLeavingElementsList_nodup
    {n : ℕ} {operations : List (Interface.Operation n)}
    {operationIndex : ℕ} (operationIndex_lt : operationIndex < operations.length)
    {selected : Interface.Operation n}
    (selected_eq : operations[operationIndex] = selected)
    {element : Interface.Element n}
    (selectedLeaves : operationLeavesElement selected element)
    (globalNodup : (operationLeavingElementsList operations).Nodup) :
    ∀ prior, prior ∈ operations.take operationIndex →
      ¬ operationLeavesElement prior element := by
  intro prior priorMember priorLeaves
  obtain ⟨priorIndex, priorFound⟩ :=
    List.mem_iff_getElem?.mp priorMember
  rw [List.getElem?_take] at priorFound
  split at priorFound
  next priorIndex_lt =>
    have originalFound : operations[priorIndex]? = some prior := by
      simpa using priorFound
    obtain ⟨priorIndexInBounds, prior_eq⟩ :=
      List.getElem?_eq_some_iff.mp originalFound
    have operationsPairwise :
        operations.Pairwise
          (Function.onFun List.Disjoint operationLeavingElements) :=
      (List.nodup_flatMap.mp globalNodup).2
    have disjoint :
        List.Disjoint
          (operationLeavingElements operations[priorIndex])
          (operationLeavingElements operations[operationIndex]) :=
      (List.pairwise_iff_getElem.mp operationsPairwise)
        priorIndex operationIndex priorIndexInBounds operationIndex_lt
        priorIndex_lt
    have firstMember :
        element ∈ operationLeavingElements operations[priorIndex] := by
      rw [prior_eq]
      exact mem_operationLeavingElements_iff.mpr priorLeaves
    have secondMember :
        element ∈ operationLeavingElements operations[operationIndex] := by
      rw [selected_eq]
      exact mem_operationLeavingElements_iff.mpr selectedLeaves
    exact (List.disjoint_left.mp disjoint firstMember) secondMember
  next priorIndex_not_lt =>
    simp at priorFound

namespace RequestAlignedBoundaryMove

/-- Global uniqueness of all residence-ending occurrences in the request is
sufficient for the request-start lineage chronology of every aligned boundary
move. -/
theorem noPriorLoserLeave_of_globalLeavingElements_nodup
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
      SplaySequence.RepresentedTransitionProvenance sequence transition}
    {slot : PairingSlot}
    {winner loser : Interface.Element n}
    {agreement :
      RealizedPairingEndpointAgreement transcript provenance
        slot winner loser}
    {request :
      SplaySequenceTranscript.RealizedRequestAt provenance
        agreement.endpoints.realized.occurrence.occurrence}
    {moveTrace :
      Lazy.Trace params initial transition.events transition.final}
    {move : BoundaryPairingMove moveTrace}
    (alignment :
      RequestAlignedBoundaryMove agreement request move)
    (globalNodup :
      (operationLeavingElementsList
        (Lazy.eraseOperations request.requestTransition.events)).Nodup) :
    alignment.NoPriorLoserLeave := by
  have selected_eq :
      (Lazy.eraseOperations request.requestTransition.events)[
          alignment.deleteOperationIndex]'
            alignment.deleteAtRequest.operationIndex_lt =
        Interface.Operation.delete move.source move.loser := by
    simpa only [List.get_eq_getElem] using
      alignment.deleteAtRequest.operation_eq_get
  exact noPriorLeave_of_operationLeavingElementsList_nodup
    alignment.deleteAtRequest.operationIndex_lt selected_eq
    (by simp [operationLeavesElement]) globalNodup

end RequestAlignedBoundaryMove

end Splay.Accounting
