import Splay.Accounting.ArticlePairingLoserRestoration
import Splay.Accounting.RootHeavyPathBoundaryDecomposition
import Splay.Lazy.PassRefinement

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST
open Splay.Lazy.Canonical
open ArticleBatchDestinationAllocation

private theorem articleTotalInserts_append
    {n : ℕ} (first second : List (Interface.Operation n)) :
    Interface.totalInserts (first ++ second) =
      Interface.totalInserts first + Interface.totalInserts second := by
  simp [Interface.totalInserts]

private theorem articleTotalIncreases_append
    {n : ℕ} (first second : List (Interface.Operation n)) :
    Interface.totalIncreases (first ++ second) =
      Interface.totalIncreases first + Interface.totalIncreases second := by
  simp [Interface.totalIncreases]

private theorem modify_second_appended {α : Type*}
    (values : List α) (first second : α) (update : α → α) :
    (values ++ [first, second]).modify (values.length + 1) update =
      values ++ [first, update second] := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      simp only [List.length_cons, List.cons_append, Nat.add_assoc,
        List.modify_succ_cons]
      rw [ih]

/-- Target value of an element after converting its growing interval to a
shrinking interval with the attained signed minimum `intervalGap`. -/
def articleConvertedGapTarget {n : ℕ} (view : Lazy.HeapView n)
    (intervalGap : ℤ) (element : Interface.Element n) : ℕ :=
  Analysis.transientContractedGap (view.rawGap element) intervalGap

/-- Convert-and-replace preserves every old growing top-most block except the
converted one, while the fresh replacement is empty and hence top-most. -/
theorem articleConvertAndCreate_growingTopmost
    {n : ℕ} (state : Lazy.State n)
    (blockId : Interface.BlockId) (block : Lazy.Block n)
    (intervalGap : ℤ)
    (found : state.blocks[blockId]? = some block)
    (topmost : state.GrowingTopmost) :
    ((state.convert blockId intervalGap).create
      block.creator block.side).GrowingTopmost := by
  let afterState := (state.convert blockId intervalGap).create
    block.creator block.side
  intro id
  let current := afterState.blocks.get id
  change current.mode = .growing → ∃ suffix,
    afterState.view.topDown current.owner current.side =
      current.elements ++ suffix
  intro currentGrowing
  have currentMember : current ∈ afterState.blocks := List.get_mem _ id
  change current ∈
      (state.blocks.modify blockId fun old => old.converted intervalGap) ++
        [Lazy.Block.emptyGrowing block.creator block.side]
    at currentMember
  simp only [List.mem_append, List.mem_singleton] at currentMember
  rcases currentMember with modifiedMember | replacementEq
  · obtain ⟨currentId, modifiedFound⟩ :=
      List.mem_iff_getElem?.mp modifiedMember
    rw [List.getElem?_modify] at modifiedFound
    split at modifiedFound
    next selected =>
      have blockAt : state.blocks[currentId]? = some block := by
        simpa only [selected] using found
      rw [blockAt] at modifiedFound
      have currentEq : block.converted intervalGap = current := by
        simpa using modifiedFound
      rw [← currentEq] at currentGrowing
      simp [Lazy.Block.converted] at currentGrowing
    next untouched =>
      have oldFound : state.blocks[currentId]? = some current := by
        simpa using modifiedFound
      obtain ⟨currentLt, currentEq⟩ :=
        List.getElem?_eq_some_iff.mp oldFound
      let oldId : Fin state.blocks.length := ⟨currentId, currentLt⟩
      have oldGet : state.blocks.get oldId = current := currentEq
      have oldGrowing : (state.blocks.get oldId).mode = .growing := by
        rw [oldGet]
        exact currentGrowing
      obtain ⟨suffix, topDownEq⟩ := topmost oldId oldGrowing
      refine ⟨suffix, ?_⟩
      change state.view.topDown current.owner current.side =
        current.elements ++ suffix
      simpa only [oldGet] using topDownEq
  · rw [replacementEq]
    refine ⟨state.view.topDown block.creator block.side, ?_⟩
    simp [afterState, Lazy.Block.emptyGrowing]

/-- Checked interface translation of the article's `Convert` setup step.

The growing block is converted, its empty growing replacement is created,
and all old payload values are normalized downward to the new contracted
point gaps.  The normalization suffix contains no value increase. -/
theorem exists_articleConvertAndCreateAdjustedTrace
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (stable : state.Stable params)
    {blockId : Interface.BlockId} {block : Lazy.Block n}
    (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing) :
    ∃ intervalGap converted events final,
      (block.converted intervalGap).GapValid state.view ∧
      converted =
        (state.convert blockId intervalGap).create block.creator block.side ∧
      events =
        [.operation (.convert blockId),
          .operation (.create block.creator)] ++
          converted.adjustValuesEvents
            (articleConvertedGapTarget state.view intervalGap)
            block.elements ∧
      final = converted.adjustValues
        (articleConvertedGapTarget state.view intervalGap) block.elements ∧
      Trace params state events final ∧
      Interface.totalIncreases
          (eraseOperations
            (converted.adjustValuesEvents
              (articleConvertedGapTarget state.view intervalGap)
              block.elements)) = 0 ∧
      final.blocks = converted.blocks ∧
      final.view = state.view ∧
      ∀ element ∈ block.elements,
        final.value element =
          articleConvertedGapTarget state.view intervalGap element := by
  have blockMember : block ∈ state.blocks := List.mem_of_getElem? found
  have structural := stable.valid.2 block blockMember
  have oldGapFacts :
      block.intervalGap = 0 ∧
        ∀ element ∈ block.elements, 0 ≤ state.view.rawGap element := by
    simpa only [Lazy.Block.GapValid, growing] using structural.2.2
  have oldGapZero : block.intervalGap = 0 := by
    exact oldGapFacts.1
  have oldRawNonnegative : ∀ element ∈ block.elements,
      0 ≤ state.view.rawGap element := by
    exact oldGapFacts.2
  obtain ⟨intervalGap, convertedGapValid, intervalNonnegative⟩ :
      ∃ intervalGap,
        (block.converted intervalGap).GapValid state.view ∧
          0 ≤ intervalGap := by
    by_cases empty : block.elements = []
    · refine ⟨0, ?_, by omega⟩
      simp [Lazy.Block.GapValid, Lazy.Block.converted, empty]
    · obtain ⟨intervalGap, minimum⟩ :=
        Lazy.Block.exists_intervalGap state.view block.elements empty
      have nonnegative : 0 ≤ intervalGap := by
        obtain ⟨minimizer, minimizerMember, attains⟩ := minimum.1
        rw [← attains]
        exact oldRawNonnegative minimizer (by simpa using minimizerMember)
      refine ⟨intervalGap, ?_, nonnegative⟩
      simp only [Lazy.Block.GapValid, Lazy.Block.converted]
      exact Or.inr ⟨empty, minimum⟩
  let converted :=
    (state.convert blockId intervalGap).create block.creator block.side
  have conversionTrace : Trace params state
      [.operation (.convert blockId),
        .operation (.create block.creator)] converted := by
    exact state.convertAndCreate_trace blockId block intervalGap stable.valid
      found growing convertedGapValid
  let target := articleConvertedGapTarget state.view intervalGap
  have targetPositive : ∀ element ∈ block.elements,
      1 ≤ target element := by
    intro element elementMember
    simp [target, articleConvertedGapTarget,
      Analysis.transientContractedGap, Analysis.contractedGap]
  have targetLeState : ∀ element ∈ block.elements,
      target element ≤ state.value element := by
    intro element elementMember
    rw [stable.value_eq_transientContractedGap blockMember elementMember,
      oldGapZero]
    exact Analysis.transientContractedGap_le_zeroGap intervalNonnegative
      (by
        have convertedFacts :
            Analysis.IsIntervalGap block.elements.toFinset state.view.rawGap
              intervalGap := by
          have sourceNonempty : block.elements ≠ [] :=
            List.ne_nil_of_mem elementMember
          have gapCases := convertedGapValid
          simp only [Lazy.Block.GapValid, Lazy.Block.converted] at gapCases
          exact (Or.resolve_left gapCases (by
            rintro ⟨empty, _⟩
            exact sourceNonempty empty)).2
        exact convertedFacts.interval_le (by simpa using elementMember))
  have targetBounded : ∀ element ∈ block.elements,
      target element ≤ params.valueBound := by
    intro element elementMember
    exact (targetLeState element elementMember).trans
      (stable.valid.toInterface.2.1 element).2
  let final := converted.adjustValues target block.elements
  let adjustmentEvents := converted.adjustValuesEvents target block.elements
  have adjustmentTrace : Trace params converted adjustmentEvents final := by
    exact converted.adjustValues_trace target block.elements
      conversionTrace.final_valid targetPositive targetBounded
  have sourceNodup : block.elements.Nodup := by
    have interfaceFound : state.toInterface.block? blockId =
        some block.toInterface := by
      unfold Interface.State.block? Lazy.State.toInterface
      simpa using congrArg (Option.map Lazy.Block.toInterface) found
    have interfaceNodup :=
      stable.valid.toInterface.block_elements_nodup interfaceFound
    change block.elements.Nodup at interfaceNodup
    exact interfaceNodup
  have convertedValue : converted.value = state.value := rfl
  have targetLeConverted : ∀ element ∈ block.elements,
      target element ≤ converted.value element := by
    intro element elementMember
    rw [convertedValue]
    exact targetLeState element elementMember
  have noIncreases : Interface.totalIncreases
      (eraseOperations adjustmentEvents) = 0 := by
    exact converted.totalIncreases_adjustValuesEvents_eq_zero_of_le
      target block.elements sourceNodup targetLeConverted
  have finalBlocks : final.blocks = converted.blocks := by
    simp [final]
  have finalView : final.view = state.view := by
    calc
      final.view = converted.view := by simp [final]
      _ = state.view := rfl
  have finalSourceValues : ∀ element ∈ block.elements,
      final.value element = target element := by
    intro element elementMember
    exact converted.adjustValues_value_of_mem target sourceNodup elementMember
      targetPositive
  refine ⟨intervalGap, converted,
    [.operation (.convert blockId),
      .operation (.create block.creator)] ++ adjustmentEvents,
    final, convertedGapValid, rfl, rfl, rfl, ?_, noIncreases,
    finalBlocks, finalView, finalSourceValues⟩
  exact conversionTrace.append adjustmentTrace

/-- The article `Convert`/`Create` macro and its downward value repair return
to a stable checkpoint. -/
theorem articleConvertAndCreateAdjusted_stable
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (stable : state.Stable params)
    {blockId : Interface.BlockId} {block : Lazy.Block n}
    (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing)
    (intervalGap : ℤ) {converted final : Lazy.State n}
    {events : List (Event n)}
    (convertedEq : converted =
      (state.convert blockId intervalGap).create block.creator block.side)
    (finalEq : final = converted.adjustValues
      (articleConvertedGapTarget state.view intervalGap) block.elements)
    (trace : Trace params state events final)
    (finalSourceValues : ∀ element ∈ block.elements,
      final.value element =
        articleConvertedGapTarget state.view intervalGap element) :
    final.Stable params := by
  let target := articleConvertedGapTarget state.view intervalGap
  have blockMember : block ∈ state.blocks := List.mem_of_getElem? found
  have blockNodup : block.elements.Nodup := by
    have interfaceFound : state.toInterface.block? blockId =
        some block.toInterface := by
      unfold Interface.State.block? Lazy.State.toInterface
      simpa using congrArg (Option.map Lazy.Block.toInterface) found
    have interfaceNodup :=
      stable.valid.toInterface.block_elements_nodup interfaceFound
    change block.elements.Nodup at interfaceNodup
    exact interfaceNodup
  have finalBlocks : final.blocks = converted.blocks := by
    simp [finalEq]
  have finalView : final.view = state.view := by
    calc
      final.view = converted.view := by simp [finalEq]
      _ = state.view := by rw [convertedEq]; rfl
  have convertedView : converted.view = state.view := by
    rw [convertedEq]
    rfl
  have convertedAssigned : converted.allElements = state.allElements := by
    rw [convertedEq, Lazy.State.create_allElements,
      Lazy.State.convert_allElements]
  have finalComplete : final.Complete := by
    intro element
    have assignedEq : final.allElements = state.allElements := by
      calc
        final.allElements = converted.allElements := by
          simp [Lazy.State.allElements, finalBlocks]
        _ = state.allElements := convertedAssigned
    rw [assignedEq, stable.2.1 element, finalView]
  have convertedOneGrowing : converted.OneGrowingPerSide := by
    rw [convertedEq]
    exact state.convertAndCreate_oneGrowingPerSide blockId block intervalGap
      stable.valid found growing stable.2.2.2.1
  have finalOneGrowing : final.OneGrowingPerSide := by
    rw [Lazy.State.OneGrowingPerSide, finalBlocks]
    exact convertedOneGrowing
  have convertedTopmost : converted.GrowingTopmost := by
    rw [convertedEq]
    exact articleConvertAndCreate_growingTopmost state blockId block
      intervalGap found stable.2.2.2.2.1
  have finalTopmost : final.GrowingTopmost := by
    rw [Lazy.State.GrowingTopmost, finalBlocks]
    intro id
    dsimp only
    intro currentGrowing
    obtain ⟨suffix, topDownEq⟩ := convertedTopmost id currentGrowing
    refine ⟨suffix, ?_⟩
    rw [finalView, ← convertedView]
    exact topDownEq
  have rootNotBlock : state.view.root ∉ block.elements := by
    intro rootMember
    exact stable.valid.root_not_mem
      (Lazy.State.mem_allElements_iff.mpr
        ⟨block, blockMember, rootMember⟩)
  have finalRootValue : final.value final.view.root = 1 := by
    rw [finalView]
    calc
      final.value state.view.root = converted.value state.view.root := by
        rw [finalEq]
        exact converted.adjustValues_value_of_not_mem target block.elements
          rootNotBlock
      _ = state.value state.view.root := by rw [convertedEq]; rfl
      _ = 1 := stable.2.2.2.2.2.1
  have finalBlockValues : ∀ current ∈ final.blocks,
      ∀ element ∈ current.elements,
        final.value element =
          Analysis.transientContractedGap
            (final.view.rawGap element) current.intervalGap := by
    intro current currentMember element elementMember
    have convertedMember : current ∈ converted.blocks := by
      simpa only [finalBlocks] using currentMember
    rw [convertedEq] at convertedMember
    change current ∈
        (state.blocks.modify blockId fun old => old.converted intervalGap) ++
          [Lazy.Block.emptyGrowing block.creator block.side]
      at convertedMember
    simp only [List.mem_append, List.mem_singleton] at convertedMember
    rcases convertedMember with modifiedMember | replacementEq
    · obtain ⟨currentId, modifiedFound⟩ :=
        List.mem_iff_getElem?.mp modifiedMember
      rw [List.getElem?_modify] at modifiedFound
      split at modifiedFound
      next selected =>
        have blockAt : state.blocks[currentId]? = some block := by
          simpa only [selected] using found
        rw [blockAt] at modifiedFound
        have currentEq : block.converted intervalGap = current := by
          simpa using modifiedFound
        rw [← currentEq] at elementMember ⊢
        have sourceElement : element ∈ block.elements := by
          simpa [Lazy.Block.converted] using elementMember
        rw [finalSourceValues element sourceElement, finalView]
        rfl
      next untouched =>
        have oldFound : state.blocks[currentId]? = some current := by
          simpa using modifiedFound
        have elementNotBlock : element ∉ block.elements := by
          intro sourceElement
          have idsEq := stable.valid.blockId_eq_of_element_mem
            oldFound elementMember found sourceElement
          exact untouched idsEq.symm
        calc
          final.value element = converted.value element := by
            rw [finalEq]
            exact converted.adjustValues_value_of_not_mem target
              block.elements elementNotBlock
          _ = state.value element := by rw [convertedEq]; rfl
          _ = Analysis.transientContractedGap
              (state.view.rawGap element) current.intervalGap :=
            stable.value_eq_transientContractedGap
              (List.mem_of_getElem? oldFound) elementMember
          _ = Analysis.transientContractedGap
              (final.view.rawGap element) current.intervalGap := by
            rw [finalView]
    · rw [replacementEq] at elementMember
      simp [Lazy.Block.emptyGrowing] at elementMember
  have finalValues : final.ValuesRealizeGaps :=
    ⟨finalRootValue, finalBlockValues⟩
  have finalOrdered : final.view.HeapOrdered := by
    rw [finalView]
    exact stable.2.2.1
  exact ⟨trace.final_valid, finalComplete, finalOrdered,
    finalOneGrowing, finalTopmost, finalValues⟩

/-- The unique growing interval at one owner/side slot has empty payload.
This is the precise rich-state form of the manuscript's instruction to
convert the growing lazy interval: the converted history remains shrinking,
while the mandatory replacement growing interval is empty. -/
def ArticleGrowingEmptyAt {n : ℕ} (state : Lazy.State n)
    (owner : Interface.Element n) (childSide : Lazy.Side) : Prop :=
  ∀ id : Fin state.blocks.length,
    let block := state.blocks.get id
    block.mode = .growing →
      block.owner = owner →
      block.side = childSide →
      block.elements = []

/-- Article Step 1 at one owner/side slot.

If its unique growing interval is already empty, this is a no-op.  Otherwise
the interval is converted, an empty growing replacement is created, and its
old payload values are repaired only downward.  Empty growing slots at every
different owner/side pair are preserved, so these macros can be composed for
`x`, `x⁻`, and `x⁺`. -/
theorem exists_articleEmptyGrowingAtFramedRefinedTrace
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (stable : state.Stable params)
    (owner : Interface.Element n) (childSide : Lazy.Side) :
    ∃ (events : List (Event n)) (final : Lazy.State n),
      Trace params state events final ∧
      final.blocks.length ≤ state.blocks.length + 1 ∧
      Interface.totalInserts (eraseOperations events) = 0 ∧
      Interface.totalIncreases (eraseOperations events) = 0 ∧
      final.Stable params ∧
      final.view = state.view ∧
      ArticleGrowingEmptyAt final owner childSide ∧
      (∀ otherOwner otherSide,
        (otherOwner ≠ owner ∨ otherSide ≠ childSide) →
        ArticleGrowingEmptyAt state otherOwner otherSide →
        ArticleGrowingEmptyAt final otherOwner otherSide) ∧
      (∀ (oldId : Interface.BlockId) (oldBlock : Lazy.Block n), state.blocks[oldId]? = some oldBlock →
        oldBlock.mode = .shrinking → final.blocks[oldId]? = some oldBlock) ∧
      state.PassRefinement final := by
  obtain ⟨selectedId, selectedProperty, selectedUnique⟩ :=
    stable.2.2.2.1 owner childSide
  let block := state.blocks.get selectedId
  have growing : block.mode = .growing := selectedProperty.1
  have blockOwner : block.owner = owner := selectedProperty.2.1
  have blockSide : block.side = childSide := selectedProperty.2.2
  have found : state.blocks[selectedId.val]? = some block := by
    exact List.getElem?_eq_some_iff.mpr ⟨selectedId.isLt, rfl⟩
  by_cases empty : block.elements = []
  · have targetEmpty : ArticleGrowingEmptyAt state owner childSide := by
      intro id
      dsimp only
      intro idGrowing idOwner idSide
      have idEq : id = selectedId :=
        selectedUnique id ⟨idGrowing, idOwner, idSide⟩
      subst id
      exact empty
    exact ⟨[], state, Trace.nil stable.valid, by omega, rfl, rfl, stable,
      rfl, targetEmpty, by
        intro otherOwner otherSide _different alreadyEmpty
        exact alreadyEmpty, by
        intro oldId oldBlock oldFound _shrinking
        exact oldFound, State.PassRefinement.refl state⟩
  · obtain ⟨intervalGap, converted, events, final, _gapValid,
        convertedEq, eventsEq, finalEq, trace, adjustmentNoIncreases,
        finalBlocks, finalView, finalSourceValues⟩ :=
      exists_articleConvertAndCreateAdjustedTrace stable found growing
    have finalStable : final.Stable params :=
      articleConvertAndCreateAdjusted_stable stable found growing intervalGap
        convertedEq finalEq trace finalSourceValues
    have noInserts :
        Interface.totalInserts (eraseOperations events) = 0 := by
      rw [eventsEq, eraseOperations_append, articleTotalInserts_append]
      rw [converted.totalInserts_adjustValuesEvents_eq_zero
        (articleConvertedGapTarget state.view intervalGap) block.elements]
      rfl
    have noIncreases :
        Interface.totalIncreases (eraseOperations events) = 0 := by
      rw [eventsEq, eraseOperations_append, articleTotalIncreases_append,
        adjustmentNoIncreases]
      rfl
    have creatorEq : block.creator = owner := by
      have structural := stable.valid.2 block (List.get_mem _ selectedId)
      exact
        (Lazy.Block.StructurallyValid.owner_eq_creator_of_growing
          structural growing).symm
          |>.trans blockOwner
    have freshFound :
        final.blocks[state.blocks.length]? =
          some (Lazy.Block.emptyGrowing owner childSide) := by
      rw [finalBlocks, convertedEq]
      change
        ((state.blocks.modify selectedId.val fun old =>
            old.converted intervalGap) ++
          [Lazy.Block.emptyGrowing block.creator block.side])[
            state.blocks.length]? =
          some (Lazy.Block.emptyGrowing owner childSide)
      rw [List.getElem?_append_right (by simp)]
      simp [creatorEq, blockSide]
    obtain ⟨freshLt, freshGet⟩ :=
      List.getElem?_eq_some_iff.mp freshFound
    let freshId : Fin final.blocks.length :=
      ⟨state.blocks.length, freshLt⟩
    have freshBlockEq :
        final.blocks.get freshId =
          Lazy.Block.emptyGrowing owner childSide := freshGet
    have freshProperty :
        let fresh := final.blocks.get freshId
        fresh.mode = .growing ∧
          fresh.owner = owner ∧ fresh.side = childSide := by
      dsimp only
      rw [freshBlockEq]
      simp [Lazy.Block.emptyGrowing]
    have targetEmpty : ArticleGrowingEmptyAt final owner childSide := by
      intro id
      dsimp only
      intro idGrowing idOwner idSide
      obtain ⟨canonicalId, _canonicalProperty, canonicalUnique⟩ :=
        finalStable.2.2.2.1 owner childSide
      have idEq : id = freshId :=
        (canonicalUnique id ⟨idGrowing, idOwner, idSide⟩).trans
          (canonicalUnique freshId freshProperty).symm
      subst id
      rw [freshBlockEq]
      rfl
    have preserveDifferent : ∀ otherOwner otherSide,
        (otherOwner ≠ owner ∨ otherSide ≠ childSide) →
        ArticleGrowingEmptyAt state otherOwner otherSide →
        ArticleGrowingEmptyAt final otherOwner otherSide := by
      intro otherOwner otherSide different alreadyEmpty
      obtain ⟨oldId, oldProperty, _oldUnique⟩ :=
        stable.2.2.2.1 otherOwner otherSide
      let oldBlock := state.blocks.get oldId
      have oldFound : state.blocks[oldId.val]? = some oldBlock := by
        exact List.getElem?_eq_some_iff.mpr ⟨oldId.isLt, rfl⟩
      have oldEmpty : oldBlock.elements = [] :=
        alreadyEmpty oldId oldProperty.1 oldProperty.2.1 oldProperty.2.2
      have oldNeSelected : oldId.val ≠ selectedId.val := by
        intro equal
        have idEq : oldId = selectedId := Fin.ext equal
        subst oldId
        rcases different with ownerNe | sideNe
        · exact ownerNe (oldProperty.2.1.symm.trans blockOwner)
        · exact sideNe (oldProperty.2.2.symm.trans blockSide)
      have oldFoundFinal : final.blocks[oldId.val]? = some oldBlock := by
        rw [finalBlocks, convertedEq]
        change
          ((state.blocks.modify selectedId.val fun old =>
              old.converted intervalGap) ++
            [Lazy.Block.emptyGrowing block.creator block.side])[oldId.val]? =
            some oldBlock
        rw [List.getElem?_append_left (by simp)]
        rw [List.getElem?_modify_ne _ _ oldNeSelected.symm]
        exact oldFound
      obtain ⟨oldFinalLt, oldFinalGet⟩ :=
        List.getElem?_eq_some_iff.mp oldFoundFinal
      let oldFinalId : Fin final.blocks.length :=
        ⟨oldId.val, oldFinalLt⟩
      have oldFinalProperty :
          let current := final.blocks.get oldFinalId
          current.mode = .growing ∧
            current.owner = otherOwner ∧ current.side = otherSide := by
        dsimp only
        change
          (final.blocks[oldId.val]).mode = .growing ∧
            (final.blocks[oldId.val]).owner = otherOwner ∧
            (final.blocks[oldId.val]).side = otherSide
        rw [oldFinalGet]
        exact oldProperty
      intro id
      dsimp only
      intro idGrowing idOwner idSide
      obtain ⟨canonicalId, _canonicalProperty, canonicalUnique⟩ :=
        finalStable.2.2.2.1 otherOwner otherSide
      have idEq : id = oldFinalId :=
        (canonicalUnique id ⟨idGrowing, idOwner, idSide⟩).trans
          (canonicalUnique oldFinalId oldFinalProperty).symm
      subst id
      change (final.blocks[oldId.val]).elements = []
      rw [oldFinalGet]
      exact oldEmpty
    have birthBound : final.blocks.length ≤ state.blocks.length + 1 := by
      simp [finalBlocks, convertedEq, State.create, State.convert]
    have preserveShrinking : ∀ (oldId : Interface.BlockId) (oldBlock : Lazy.Block n),
        state.blocks[oldId]? = some oldBlock → oldBlock.mode = .shrinking →
        final.blocks[oldId]? = some oldBlock := by
      intro oldId oldBlock oldFound shrinking
      have different : oldId ≠ selectedId.val := by
        intro equal
        subst oldId
        rw [found] at oldFound
        cases Option.some.inj oldFound
        rw [growing] at shrinking
        contradiction
      obtain ⟨oldLt, _⟩ := List.getElem?_eq_some_iff.mp oldFound
      rw [finalBlocks, convertedEq]
      change ((state.blocks.modify selectedId.val fun old => old.converted intervalGap) ++
        [Lazy.Block.emptyGrowing block.creator block.side])[oldId]? = some oldBlock
      rw [List.getElem?_append_left (by simpa using oldLt)]
      rw [List.getElem?_modify_ne _ _ different.symm]
      exact oldFound
    have refinement : state.PassRefinement final := by
      have convertedRefinement := (state.convert_passRefinement selectedId.val intervalGap).trans
        ((state.convert selectedId.val intervalGap).create_passRefinement block.creator block.side)
      apply convertedRefinement.trans
      apply State.PassRefinement.of_blocks_eq
      rw [finalBlocks, convertedEq]
    exact ⟨events, final, trace, birthBound, noInserts, noIncreases, finalStable,
      finalView, targetEmpty, preserveDifferent, preserveShrinking, refinement⟩


/-- Compatibility wrapper for the original preparation statement. -/
theorem exists_articleEmptyGrowingAtFramedTrace
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (stable : state.Stable params)
    (owner : Interface.Element n) (childSide : Lazy.Side) :
    ∃ (events : List (Event n)) (final : Lazy.State n),
      Trace params state events final ∧
      final.blocks.length ≤ state.blocks.length + 1 ∧
      Interface.totalInserts (eraseOperations events) = 0 ∧
      Interface.totalIncreases (eraseOperations events) = 0 ∧
      final.Stable params ∧
      final.view = state.view ∧
      ArticleGrowingEmptyAt final owner childSide ∧
      (∀ otherOwner otherSide,
        (otherOwner ≠ owner ∨ otherSide ≠ childSide) →
        ArticleGrowingEmptyAt state otherOwner otherSide →
        ArticleGrowingEmptyAt final otherOwner otherSide) ∧
      (∀ (oldId : Interface.BlockId) (oldBlock : Lazy.Block n), state.blocks[oldId]? = some oldBlock →
        oldBlock.mode = .shrinking → final.blocks[oldId]? = some oldBlock) := by
  obtain ⟨events, final, trace, births, noInserts, noIncreases, finalStable,
    viewEq, empty, preserves, frame, _⟩ := exists_articleEmptyGrowingAtFramedRefinedTrace stable owner childSide
  exact ⟨events, final, trace, births, noInserts, noIncreases, finalStable, viewEq, empty, preserves, frame⟩

/-- Compatibility wrapper retaining the original one-slot preparation API. -/
theorem exists_articleEmptyGrowingAtTrace
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (stable : state.Stable params)
    (owner : Interface.Element n) (childSide : Lazy.Side) :
    ∃ (events : List (Event n)) (final : Lazy.State n),
      Trace params state events final ∧
      final.blocks.length ≤ state.blocks.length + 1 ∧
      Interface.totalInserts (eraseOperations events) = 0 ∧
      Interface.totalIncreases (eraseOperations events) = 0 ∧
      final.Stable params ∧
      final.view = state.view ∧
      ArticleGrowingEmptyAt final owner childSide ∧
      (∀ otherOwner otherSide,
        (otherOwner ≠ owner ∨ otherSide ≠ childSide) →
        ArticleGrowingEmptyAt state otherOwner otherSide →
        ArticleGrowingEmptyAt final otherOwner otherSide) := by
  obtain ⟨events, final, trace, births, noInserts, noIncreases, finalStable,
    viewEq, empty, preserves, _⟩ := exists_articleEmptyGrowingAtFramedTrace stable owner childSide
  exact ⟨events, final, trace, births, noInserts, noIncreases, finalStable, viewEq, empty, preserves⟩

/-- Both mandatory growing slots of one heap owner are empty. -/
def ArticleGrowingOwnerEmpty {n : ℕ} (state : Lazy.State n)
    (owner : Interface.Element n) : Prop :=
  ArticleGrowingEmptyAt state owner .left ∧
    ArticleGrowingEmptyAt state owner .right

/-- Article Step 1 for one owner: empty its left and right growing intervals
by at most two convert/create macros. -/
theorem exists_articleEmptyGrowingOwnerTrace
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (stable : state.Stable params) (owner : Interface.Element n) :
    ∃ (events : List (Event n)) (final : Lazy.State n),
      Trace params state events final ∧
      final.blocks.length ≤ state.blocks.length + 2 ∧
      Interface.totalInserts (eraseOperations events) = 0 ∧
      Interface.totalIncreases (eraseOperations events) = 0 ∧
      final.Stable params ∧
      final.view = state.view ∧
      ArticleGrowingOwnerEmpty final owner ∧
      (∀ otherOwner,
        otherOwner ≠ owner →
        ArticleGrowingOwnerEmpty state otherOwner →
        ArticleGrowingOwnerEmpty final otherOwner) := by
  obtain ⟨leftEvents, leftFinal, leftTrace, leftBirth, leftNoInserts,
      leftNoIncreases, leftStable, leftView, leftEmpty, leftPreserve⟩ :=
    exists_articleEmptyGrowingAtTrace stable owner .left
  obtain ⟨rightEvents, final, rightTrace, rightBirth, rightNoInserts,
      rightNoIncreases, finalStable, rightView, rightEmpty, rightPreserve⟩ :=
    exists_articleEmptyGrowingAtTrace leftStable owner .right
  have leftEmptyFinal : ArticleGrowingEmptyAt final owner .left :=
    rightPreserve owner .left (Or.inr (by decide)) leftEmpty
  let events := leftEvents ++ rightEvents
  have fullTrace : Trace params state events final :=
    leftTrace.append rightTrace
  have noInserts : Interface.totalInserts (eraseOperations events) = 0 := by
    rw [show events = leftEvents ++ rightEvents by rfl,
      eraseOperations_append, articleTotalInserts_append,
      leftNoInserts, rightNoInserts, zero_add]
  have noIncreases :
      Interface.totalIncreases (eraseOperations events) = 0 := by
    rw [show events = leftEvents ++ rightEvents by rfl,
      eraseOperations_append, articleTotalIncreases_append,
      leftNoIncreases, rightNoIncreases, zero_add]
  have finalView : final.view = state.view := rightView.trans leftView
  have preserveOther : ∀ otherOwner,
      otherOwner ≠ owner →
      ArticleGrowingOwnerEmpty state otherOwner →
      ArticleGrowingOwnerEmpty final otherOwner := by
    intro otherOwner different alreadyEmpty
    have otherLeftAtMiddle :
        ArticleGrowingEmptyAt leftFinal otherOwner .left :=
      leftPreserve otherOwner .left (Or.inl different) alreadyEmpty.1
    have otherRightAtMiddle :
        ArticleGrowingEmptyAt leftFinal otherOwner .right :=
      leftPreserve otherOwner .right (Or.inl different) alreadyEmpty.2
    exact
      ⟨rightPreserve otherOwner .left (Or.inl different)
          otherLeftAtMiddle,
        rightPreserve otherOwner .right (Or.inl different)
          otherRightAtMiddle⟩
  exact ⟨events, final, fullTrace, by omega, noInserts, noIncreases, finalStable,
    finalView, ⟨leftEmptyFinal, rightEmpty⟩, preserveOther⟩

/-- Article Step 1 for the accessed owner and the two boundary owners.
Pairwise distinctness is exactly what lets each later owner preparation retain
the two empty growing slots prepared earlier. -/
theorem exists_articleEmptyGrowingThreeOwnersTrace
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (stable : state.Stable params)
    (first second third : Interface.Element n)
    (firstNeSecond : first ≠ second)
    (firstNeThird : first ≠ third)
    (secondNeThird : second ≠ third) :
    ∃ (events : List (Event n)) (final : Lazy.State n),
      Trace params state events final ∧
      final.blocks.length ≤ state.blocks.length + 6 ∧
      Interface.totalInserts (eraseOperations events) = 0 ∧
      Interface.totalIncreases (eraseOperations events) = 0 ∧
      final.Stable params ∧
      final.view = state.view ∧
      ArticleGrowingOwnerEmpty final first ∧
      ArticleGrowingOwnerEmpty final second ∧
      ArticleGrowingOwnerEmpty final third := by
  obtain ⟨firstEvents, firstFinal, firstTrace, firstBirth, firstNoInserts,
      firstNoIncreases, firstStable, firstView, firstEmpty,
      firstPreserve⟩ :=
    exists_articleEmptyGrowingOwnerTrace stable first
  obtain ⟨secondEvents, secondFinal, secondTrace, secondBirth, secondNoInserts,
      secondNoIncreases, secondStable, secondView, secondEmpty,
      secondPreserve⟩ :=
    exists_articleEmptyGrowingOwnerTrace firstStable second
  have firstEmptySecond : ArticleGrowingOwnerEmpty secondFinal first :=
    secondPreserve first firstNeSecond firstEmpty
  obtain ⟨thirdEvents, final, thirdTrace, thirdBirth, thirdNoInserts,
      thirdNoIncreases, finalStable, thirdView, thirdEmpty,
      thirdPreserve⟩ :=
    exists_articleEmptyGrowingOwnerTrace secondStable third
  have firstEmptyFinal : ArticleGrowingOwnerEmpty final first :=
    thirdPreserve first firstNeThird firstEmptySecond
  have secondEmptyFinal : ArticleGrowingOwnerEmpty final second :=
    thirdPreserve second secondNeThird secondEmpty
  let events := firstEvents ++ secondEvents ++ thirdEvents
  have fullTrace : Trace params state events final :=
    (firstTrace.append secondTrace).append thirdTrace
  have noInserts : Interface.totalInserts (eraseOperations events) = 0 := by
    rw [show events = (firstEvents ++ secondEvents) ++ thirdEvents by
      simp [events], eraseOperations_append, articleTotalInserts_append,
      eraseOperations_append, articleTotalInserts_append,
      firstNoInserts, secondNoInserts, thirdNoInserts]
  have noIncreases :
      Interface.totalIncreases (eraseOperations events) = 0 := by
    rw [show events = (firstEvents ++ secondEvents) ++ thirdEvents by
      simp [events], eraseOperations_append, articleTotalIncreases_append,
      eraseOperations_append, articleTotalIncreases_append,
      firstNoIncreases, secondNoIncreases, thirdNoIncreases]
  have finalView : final.view = state.view :=
    thirdView.trans (secondView.trans firstView)
  exact ⟨events, final, fullTrace, by omega, noInserts, noIncreases, finalStable,
    finalView, firstEmptyFinal, secondEmptyFinal, thirdEmpty⟩

/-- Empty growing payload survives any stable transition that preserves the
corresponding old empty block.  This packages the block-ID argument needed
when Step 2 splits shrinking boundary intervals. -/
theorem ArticleGrowingEmptyAt.of_preserved
    {n : ℕ} {params : Interface.Parameters}
    {before after : Lazy.State n}
    (beforeStable : before.Stable params)
    (afterStable : after.Stable params)
    {owner : Interface.Element n} {childSide : Lazy.Side}
    (empty : ArticleGrowingEmptyAt before owner childSide)
    (preserved : ∀ (oldId : Interface.BlockId) (oldBlock : Lazy.Block n),
      before.blocks[oldId]? = some oldBlock →
      oldBlock.elements = [] →
      after.blocks[oldId]? = some oldBlock) :
    ArticleGrowingEmptyAt after owner childSide := by
  obtain ⟨oldId, oldProperty, _oldUnique⟩ :=
    beforeStable.2.2.2.1 owner childSide
  let oldBlock := before.blocks.get oldId
  have oldFound : before.blocks[oldId.val]? = some oldBlock := by
    exact List.getElem?_eq_some_iff.mpr ⟨oldId.isLt, rfl⟩
  have oldEmpty : oldBlock.elements = [] :=
    empty oldId oldProperty.1 oldProperty.2.1 oldProperty.2.2
  have oldFoundAfter : after.blocks[oldId.val]? = some oldBlock :=
    preserved oldId.val oldBlock oldFound oldEmpty
  obtain ⟨oldAfterLt, oldAfterGet⟩ :=
    List.getElem?_eq_some_iff.mp oldFoundAfter
  let oldAfterId : Fin after.blocks.length := ⟨oldId.val, oldAfterLt⟩
  have oldAfterProperty :
      let current := after.blocks.get oldAfterId
      current.mode = .growing ∧
        current.owner = owner ∧ current.side = childSide := by
    dsimp only
    change
      (after.blocks[oldId.val]).mode = .growing ∧
        (after.blocks[oldId.val]).owner = owner ∧
        (after.blocks[oldId.val]).side = childSide
    rw [oldAfterGet]
    exact oldProperty
  intro id
  dsimp only
  intro idGrowing idOwner idSide
  obtain ⟨canonicalId, _canonicalProperty, canonicalUnique⟩ :=
    afterStable.2.2.2.1 owner childSide
  have idEq : id = oldAfterId :=
    (canonicalUnique id ⟨idGrowing, idOwner, idSide⟩).trans
      (canonicalUnique oldAfterId oldAfterProperty).symm
  subst id
  change (after.blocks[oldId.val]).elements = []
  rw [oldAfterGet]
  exact oldEmpty

/-- Canonical specialization of article Step 1.  The boundary ordering gives
the pairwise distinct owners `x`, `x⁻`, and `x⁺`; the resulting state still
represents the unchanged pre-splay canonical heap view. -/
theorem exists_articleEmptyCanonicalOwnersTrace
    {n : ℕ} (snapshot : Snapshot n) (before : BST 0 n)
    (key : Fin n)
    {params : Interface.Parameters} {state : Lazy.State n}
    (represents : state.Represents params snapshot before) :
    let selection :=
      WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
        snapshot before key
    ∃ (events : List (Event n)) (final : Lazy.State n),
      Trace params state events final ∧
      final.blocks.length ≤ state.blocks.length + 6 ∧
      Interface.totalInserts (eraseOperations events) = 0 ∧
      Interface.totalIncreases (eraseOperations events) = 0 ∧
      final.Represents params snapshot before ∧
      ArticleGrowingOwnerEmpty final (valuePos key) ∧
      ArticleGrowingOwnerEmpty final selection.left ∧
      ArticleGrowingOwnerEmpty final selection.right := by
  let selection :=
    WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
      snapshot before key
  have accessedNeLeft : valuePos key ≠ selection.left :=
    (ne_of_lt selection.ordered.1).symm
  have accessedNeRight : valuePos key ≠ selection.right :=
    ne_of_lt selection.ordered.2
  have leftNeRight : selection.left ≠ selection.right :=
    ne_of_lt (selection.ordered.1.trans selection.ordered.2)
  obtain ⟨events, final, trace, birthBound, noInserts, noIncreases, finalStable,
      finalView, accessedEmpty, leftEmpty, rightEmpty⟩ :=
    exists_articleEmptyGrowingThreeOwnersTrace represents.stable
      (valuePos key) selection.left selection.right
      accessedNeLeft accessedNeRight leftNeRight
  have finalRepresents : final.Represents params snapshot before :=
    ⟨finalStable, finalView.trans represents.view_eq⟩
  exact ⟨events, final, trace, birthBound, noInserts, noIncreases, finalRepresents,
    accessedEmpty, leftEmpty, rightEmpty⟩

/-- Target value after splitting a shrinking interval into its prefix and
suffix.  Membership in the prefix decides which recomputed attained minimum
is used. -/
def articleSplitGapTarget {n : ℕ} (view : Lazy.HeapView n)
    (prefixElements : List (Interface.Element n))
    (prefixGap suffixGap : ℤ) (element : Interface.Element n) : ℕ :=
  if element ∈ prefixElements then
    Analysis.transientContractedGap (view.rawGap element) prefixGap
  else
    Analysis.transientContractedGap (view.rawGap element) suffixGap

/-- Splitting a shrinking interval cannot disturb any growing top-most
interval: the modified source and both fresh descendants are shrinking, and
every other block is literally unchanged. -/
theorem articleSplit_growingTopmost
    {n : ℕ} (state : Lazy.State n)
    (sourceId : Interface.BlockId) (source : Lazy.Block n)
    (prefixLength : ℕ) (prefixGap suffixGap : ℤ)
    (found : state.blocks[sourceId]? = some source)
    (shrinking : source.mode = .shrinking)
    (topmost : state.GrowingTopmost) :
    (state.split sourceId source prefixLength
      prefixGap suffixGap).GrowingTopmost := by
  let afterState := state.split sourceId source prefixLength
    prefixGap suffixGap
  intro id
  let block := afterState.blocks.get id
  change block.mode = .growing → ∃ suffix,
    afterState.view.topDown block.owner block.side = block.elements ++ suffix
  intro growing
  have blockMember : block ∈ afterState.blocks := List.get_mem _ id
  change block ∈
      (state.blocks.modify sourceId Lazy.Block.emptiedAfterSplit) ++
        [source.splitPrefix prefixLength prefixGap,
          source.splitSuffix prefixLength suffixGap]
    at blockMember
  simp only [List.mem_append, List.mem_pair] at blockMember
  rcases blockMember with modifiedMember | prefixEq | suffixEq
  · obtain ⟨blockId, modifiedFound⟩ :=
      List.mem_iff_getElem?.mp modifiedMember
    rw [List.getElem?_modify] at modifiedFound
    split at modifiedFound
    next selected =>
      have sourceAt : state.blocks[blockId]? = some source := by
        simpa only [selected] using found
      rw [sourceAt] at modifiedFound
      have blockEq : source.emptiedAfterSplit = block := by
        simpa using modifiedFound
      rw [← blockEq] at growing
      simp [Lazy.Block.emptiedAfterSplit, shrinking] at growing
    next untouched =>
      have oldFound : state.blocks[blockId]? = some block := by
        simpa using modifiedFound
      obtain ⟨blockLt, blockEq⟩ := List.getElem?_eq_some_iff.mp oldFound
      let oldId : Fin state.blocks.length := ⟨blockId, blockLt⟩
      have oldGet : state.blocks.get oldId = block := blockEq
      have oldGrowing : (state.blocks.get oldId).mode = .growing := by
        rw [oldGet]
        exact growing
      obtain ⟨suffix, topDownEq⟩ := topmost oldId oldGrowing
      refine ⟨suffix, ?_⟩
      change state.view.topDown block.owner block.side =
        block.elements ++ suffix
      simpa only [oldGet] using topDownEq
  · rw [prefixEq] at growing
    simp [Lazy.Block.splitPrefix, shrinking] at growing
  · rw [suffixEq] at growing
    simp [Lazy.Block.splitSuffix, shrinking] at growing

/-- Checked interface translation of the article's `Split` setup step.

Both descendant interval gaps are recomputed as attained minima.  The source
payload is then normalized to the contracted point gaps of its descendant;
all those changes are decreases, exactly as claimed in the article. -/
theorem exists_articleSplitAdjustedTrace
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (stable : state.Stable params)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (found : state.blocks[sourceId]? = some source)
    (shrinking : source.mode = .shrinking)
    (prefixLength : ℕ) (prefixLe : prefixLength ≤ source.elements.length) :
    ∃ prefixGap suffixGap splitState events final,
      (source.splitPrefix prefixLength prefixGap).GapValid state.view ∧
      (source.splitSuffix prefixLength suffixGap).GapValid state.view ∧
      splitState = state.split sourceId source prefixLength
        prefixGap suffixGap ∧
      events = [.operation (.split sourceId prefixLength)] ++
        splitState.adjustValuesEvents
          (articleSplitGapTarget state.view
            (source.elements.take prefixLength) prefixGap suffixGap)
          source.elements ∧
      final = splitState.adjustValues
        (articleSplitGapTarget state.view
          (source.elements.take prefixLength) prefixGap suffixGap)
        source.elements ∧
      Trace params state events final ∧
      Interface.totalIncreases
          (eraseOperations
            (splitState.adjustValuesEvents
              (articleSplitGapTarget state.view
                (source.elements.take prefixLength) prefixGap suffixGap)
              source.elements)) = 0 ∧
      final.blocks = splitState.blocks ∧
      final.view = state.view ∧
      ∀ element ∈ source.elements,
        final.value element =
          articleSplitGapTarget state.view
            (source.elements.take prefixLength) prefixGap suffixGap element := by
  let prefixBase := source.splitPrefix prefixLength 0
  have prefixShrinking : prefixBase.mode = .shrinking := by
    simp [prefixBase, Lazy.Block.splitPrefix, shrinking]
  obtain ⟨prefixGap, prefixGapValid⟩ :=
    Lazy.Block.exists_gapValid_of_shrinking state.view prefixBase
      prefixShrinking
  change
    (source.splitPrefix prefixLength prefixGap).GapValid state.view
      at prefixGapValid
  let suffixBase := source.splitSuffix prefixLength 0
  have suffixShrinking : suffixBase.mode = .shrinking := by
    simp [suffixBase, Lazy.Block.splitSuffix, shrinking]
  obtain ⟨suffixGap, suffixGapValid⟩ :=
    Lazy.Block.exists_gapValid_of_shrinking state.view suffixBase
      suffixShrinking
  change
    (source.splitSuffix prefixLength suffixGap).GapValid state.view
      at suffixGapValid
  have sourceMember : source ∈ state.blocks := List.mem_of_getElem? found
  have sourceStructural := stable.valid.2 source sourceMember
  let splitState := state.split sourceId source prefixLength
    prefixGap suffixGap
  have splitTrace : Trace params state
      [.operation (.split sourceId prefixLength)] splitState := by
    exact Trace.singleton
      (state.split_step sourceId source prefixLength prefixGap suffixGap
        stable.valid found shrinking prefixLe prefixGapValid suffixGapValid)
  let target := articleSplitGapTarget state.view
    (source.elements.take prefixLength) prefixGap suffixGap
  have targetPositive : ∀ element ∈ source.elements,
      1 ≤ target element := by
    intro element elementMember
    by_cases inPrefix : element ∈ source.elements.take prefixLength
    · simp [target, articleSplitGapTarget, inPrefix,
        Analysis.transientContractedGap, Analysis.contractedGap]
    · simp [target, articleSplitGapTarget, inPrefix,
        Analysis.transientContractedGap, Analysis.contractedGap]
  have targetLeState : ∀ element ∈ source.elements,
      target element ≤ state.value element := by
    intro element elementMember
    rw [stable.value_eq_transientContractedGap sourceMember elementMember]
    have sourceNonempty : source.elements ≠ [] :=
      List.ne_nil_of_mem elementMember
    have sourceMinimum :
        Analysis.IsIntervalGap source.elements.toFinset state.view.rawGap
          source.intervalGap := by
      have gapCases := sourceStructural.2.2
      simp only [Lazy.Block.GapValid, shrinking] at gapCases
      exact (Or.resolve_left gapCases (by
        rintro ⟨empty, _⟩
        exact sourceNonempty empty)).2
    by_cases inPrefix : element ∈ source.elements.take prefixLength
    · rw [show target element =
          Analysis.transientContractedGap
            (state.view.rawGap element) prefixGap by
        simp [target, articleSplitGapTarget, inPrefix]]
      have prefixNonempty : source.elements.take prefixLength ≠ [] :=
        List.ne_nil_of_mem inPrefix
      have prefixMinimum :
          Analysis.IsIntervalGap
            (source.elements.take prefixLength).toFinset state.view.rawGap
            prefixGap := by
        have gapCases := prefixGapValid
        simp only [Lazy.Block.GapValid, Lazy.Block.splitPrefix, shrinking]
          at gapCases
        exact (Or.resolve_left gapCases (by
          rintro ⟨empty, _⟩
          exact prefixNonempty empty)).2
      have oldLePrefix : source.intervalGap ≤ prefixGap :=
        sourceMinimum.le_of_subset prefixMinimum (by
          intro candidate candidateMember
          apply List.mem_toFinset.mpr
          exact (List.take_sublist prefixLength source.elements).mem
            (List.mem_toFinset.mp candidateMember))
      exact Analysis.transientContractedGap_antitone_intervalGap
        oldLePrefix (prefixMinimum.interval_le (by
          simpa only [List.mem_toFinset] using inPrefix))
    · have inSuffix : element ∈ source.elements.drop prefixLength := by
        have inAppend : element ∈
            source.elements.take prefixLength ++
              source.elements.drop prefixLength := by
          simpa only [List.take_append_drop] using elementMember
        exact (List.mem_append.mp inAppend).resolve_left inPrefix
      rw [show target element =
          Analysis.transientContractedGap
            (state.view.rawGap element) suffixGap by
        simp [target, articleSplitGapTarget, inPrefix]]
      have suffixNonempty : source.elements.drop prefixLength ≠ [] :=
        List.ne_nil_of_mem inSuffix
      have suffixMinimum :
          Analysis.IsIntervalGap
            (source.elements.drop prefixLength).toFinset state.view.rawGap
            suffixGap := by
        have gapCases := suffixGapValid
        simp only [Lazy.Block.GapValid, Lazy.Block.splitSuffix, shrinking]
          at gapCases
        exact (Or.resolve_left gapCases (by
          rintro ⟨empty, _⟩
          exact suffixNonempty empty)).2
      have oldLeSuffix : source.intervalGap ≤ suffixGap :=
        sourceMinimum.le_of_subset suffixMinimum (by
          intro candidate candidateMember
          apply List.mem_toFinset.mpr
          exact (List.drop_sublist prefixLength source.elements).mem
            (List.mem_toFinset.mp candidateMember))
      exact Analysis.transientContractedGap_antitone_intervalGap
        oldLeSuffix (suffixMinimum.interval_le (by
          simpa only [List.mem_toFinset] using inSuffix))
  have targetBounded : ∀ element ∈ source.elements,
      target element ≤ params.valueBound := by
    intro element elementMember
    exact (targetLeState element elementMember).trans
      (stable.valid.toInterface.2.1 element).2
  let final := splitState.adjustValues target source.elements
  let adjustmentEvents := splitState.adjustValuesEvents target source.elements
  have adjustmentTrace : Trace params splitState adjustmentEvents final := by
    exact splitState.adjustValues_trace target source.elements
      splitTrace.final_valid targetPositive targetBounded
  have sourceNodup : source.elements.Nodup := by
    have interfaceFound : state.toInterface.block? sourceId =
        some source.toInterface := by
      unfold Interface.State.block? Lazy.State.toInterface
      simpa using congrArg (Option.map Lazy.Block.toInterface) found
    have interfaceNodup :=
      stable.valid.toInterface.block_elements_nodup interfaceFound
    change source.elements.Nodup at interfaceNodup
    exact interfaceNodup
  have splitValue : splitState.value = state.value := rfl
  have targetLeSplit : ∀ element ∈ source.elements,
      target element ≤ splitState.value element := by
    intro element elementMember
    rw [splitValue]
    exact targetLeState element elementMember
  have noIncreases : Interface.totalIncreases
      (eraseOperations adjustmentEvents) = 0 := by
    exact splitState.totalIncreases_adjustValuesEvents_eq_zero_of_le
      target source.elements sourceNodup targetLeSplit
  have finalBlocks : final.blocks = splitState.blocks := by
    simp [final]
  have finalView : final.view = state.view := by
    calc
      final.view = splitState.view := by simp [final]
      _ = state.view := rfl
  have finalSourceValues : ∀ element ∈ source.elements,
      final.value element = target element := by
    intro element elementMember
    exact splitState.adjustValues_value_of_mem target sourceNodup
      elementMember targetPositive
  refine ⟨prefixGap, suffixGap, splitState,
    [.operation (.split sourceId prefixLength)] ++ adjustmentEvents,
    final, prefixGapValid, suffixGapValid, rfl, rfl, rfl, ?_,
    noIncreases, finalBlocks, finalView, finalSourceValues⟩
  exact splitTrace.append adjustmentTrace

/-- The article split plus its downward value normalization returns to a
fully stable checkpoint, so another interval operation or a `Pass` can be
composed immediately. -/
theorem articleSplitAdjusted_stable
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (stable : state.Stable params)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (found : state.blocks[sourceId]? = some source)
    (shrinking : source.mode = .shrinking)
    (prefixLength : ℕ) (prefixGap suffixGap : ℤ)
    {splitState final : Lazy.State n} {events : List (Event n)}
    (splitStateEq : splitState = state.split sourceId source prefixLength
      prefixGap suffixGap)
    (finalEq : final = splitState.adjustValues
      (articleSplitGapTarget state.view
        (source.elements.take prefixLength) prefixGap suffixGap)
      source.elements)
    (trace : Trace params state events final)
    (finalSourceValues : ∀ element ∈ source.elements,
      final.value element =
        articleSplitGapTarget state.view
          (source.elements.take prefixLength) prefixGap suffixGap element) :
    final.Stable params := by
  let target := articleSplitGapTarget state.view
    (source.elements.take prefixLength) prefixGap suffixGap
  have sourceMember : source ∈ state.blocks := List.mem_of_getElem? found
  have sourceNodup : source.elements.Nodup := by
    have interfaceFound : state.toInterface.block? sourceId =
        some source.toInterface := by
      unfold Interface.State.block? Lazy.State.toInterface
      simpa using congrArg (Option.map Lazy.Block.toInterface) found
    have interfaceNodup :=
      stable.valid.toInterface.block_elements_nodup interfaceFound
    change source.elements.Nodup at interfaceNodup
    exact interfaceNodup
  have finalBlocks : final.blocks = splitState.blocks := by
    simp [finalEq]
  have finalView : final.view = state.view := by
    calc
      final.view = splitState.view := by simp [finalEq]
      _ = state.view := by rw [splitStateEq]; rfl
  have splitView : splitState.view = state.view := by
    rw [splitStateEq]
    rfl
  have assignedPerm : splitState.allElements.Perm state.allElements := by
    rw [splitStateEq]
    exact state.split_allElements_perm sourceId source prefixLength
      prefixGap suffixGap found
  have finalComplete : final.Complete := by
    intro element
    have assignedIff : element ∈ final.allElements ↔
        element ∈ state.allElements := by
      rw [show final.allElements = splitState.allElements by
        simp [Lazy.State.allElements, finalBlocks]]
      exact assignedPerm.mem_iff
    rw [assignedIff, stable.2.1 element, finalView]
  have splitOneGrowing : splitState.OneGrowingPerSide := by
    rw [splitStateEq]
    exact state.split_oneGrowingPerSide sourceId source prefixLength
      prefixGap suffixGap found shrinking stable.2.2.2.1
  have finalOneGrowing : final.OneGrowingPerSide := by
    rw [Lazy.State.OneGrowingPerSide, finalBlocks]
    exact splitOneGrowing
  have splitTopmost : splitState.GrowingTopmost := by
    rw [splitStateEq]
    exact articleSplit_growingTopmost state sourceId source prefixLength
      prefixGap suffixGap found shrinking stable.2.2.2.2.1
  have finalTopmost : final.GrowingTopmost := by
    rw [Lazy.State.GrowingTopmost, finalBlocks, finalView, ← splitView]
    exact splitTopmost
  have rootNotSource : state.view.root ∉ source.elements := by
    intro rootMember
    exact stable.valid.root_not_mem
      (Lazy.State.mem_allElements_iff.mpr
        ⟨source, sourceMember, rootMember⟩)
  have finalRootValue : final.value final.view.root = 1 := by
    rw [finalView]
    calc
      final.value state.view.root = splitState.value state.view.root := by
        rw [finalEq]
        exact splitState.adjustValues_value_of_not_mem target source.elements
          rootNotSource
      _ = state.value state.view.root := by rw [splitStateEq]; rfl
      _ = 1 := stable.2.2.2.2.2.1
  have finalBlockValues : ∀ block ∈ final.blocks,
      ∀ element ∈ block.elements,
        final.value element =
          Analysis.transientContractedGap
            (final.view.rawGap element) block.intervalGap := by
    intro block blockMember element elementMember
    have splitMember : block ∈ splitState.blocks := by
      simpa only [finalBlocks] using blockMember
    rw [splitStateEq] at splitMember
    change block ∈
        (state.blocks.modify sourceId Lazy.Block.emptiedAfterSplit) ++
          [source.splitPrefix prefixLength prefixGap,
            source.splitSuffix prefixLength suffixGap]
      at splitMember
    simp only [List.mem_append, List.mem_pair] at splitMember
    rcases splitMember with modifiedMember | prefixEq | suffixEq
    · obtain ⟨blockId, modifiedFound⟩ :=
        List.mem_iff_getElem?.mp modifiedMember
      rw [List.getElem?_modify] at modifiedFound
      split at modifiedFound
      next selected =>
        have sourceAt : state.blocks[blockId]? = some source := by
          simpa only [selected] using found
        rw [sourceAt] at modifiedFound
        have blockEq : source.emptiedAfterSplit = block := by
          simpa using modifiedFound
        rw [← blockEq] at elementMember
        simp [Lazy.Block.emptiedAfterSplit] at elementMember
      next untouched =>
        have oldFound : state.blocks[blockId]? = some block := by
          simpa using modifiedFound
        have elementNotSource : element ∉ source.elements := by
          intro sourceElement
          have idsEq := stable.valid.blockId_eq_of_element_mem
            oldFound elementMember found sourceElement
          exact untouched idsEq.symm
        calc
          final.value element = splitState.value element := by
            rw [finalEq]
            exact splitState.adjustValues_value_of_not_mem target
              source.elements elementNotSource
          _ = state.value element := by rw [splitStateEq]; rfl
          _ = Analysis.transientContractedGap
              (state.view.rawGap element) block.intervalGap :=
            stable.value_eq_transientContractedGap
              (List.mem_of_getElem? oldFound) elementMember
          _ = Analysis.transientContractedGap
              (final.view.rawGap element) block.intervalGap := by
            rw [finalView]
    · rw [prefixEq] at elementMember ⊢
      have prefixElement : element ∈ source.elements.take prefixLength := by
        simpa [Lazy.Block.splitPrefix] using elementMember
      have sourceElement : element ∈ source.elements :=
        (List.take_sublist prefixLength source.elements).mem
          prefixElement
      rw [finalSourceValues element sourceElement]
      simp [articleSplitGapTarget, Lazy.Block.splitPrefix, prefixElement,
        finalView]
    · rw [suffixEq] at elementMember ⊢
      have suffixElement : element ∈ source.elements.drop prefixLength := by
        simpa [Lazy.Block.splitSuffix] using elementMember
      have sourceElement : element ∈ source.elements :=
        (List.drop_sublist prefixLength source.elements).mem suffixElement
      have notPrefix : element ∉ source.elements.take prefixLength := by
        have splitNodup :
            (source.elements.take prefixLength ++
              source.elements.drop prefixLength).Nodup := by
          simpa only [List.take_append_drop] using sourceNodup
        have disjoint := (List.nodup_append.mp splitNodup).2.2
        intro prefixElement
        exact disjoint element prefixElement element suffixElement rfl
      rw [finalSourceValues element sourceElement]
      simp [articleSplitGapTarget, Lazy.Block.splitSuffix, notPrefix,
        finalView]
  have finalValues : final.ValuesRealizeGaps :=
    ⟨finalRootValue, finalBlockValues⟩
  have finalOrdered : final.view.HeapOrdered := by
    rw [finalView]
    exact stable.2.2.1
  exact ⟨trace.final_valid, finalComplete,
    finalOrdered,
    finalOneGrowing, finalTopmost, finalValues⟩

/-- The two descendants of a rich split have deterministic fresh block IDs.
These lookup facts let the article perform its second split without erasing
the persistent block identity of the first descendant. -/
@[simp]
theorem article_splitPrefix_found {n : ℕ} (state : Lazy.State n)
    (sourceId : Interface.BlockId) (source : Lazy.Block n)
    (prefixLength : ℕ) (prefixGap suffixGap : ℤ) :
    (state.split sourceId source prefixLength prefixGap suffixGap).blocks[
        state.blocks.length]? =
      some (source.splitPrefix prefixLength prefixGap) := by
  simp [Lazy.State.split, Lazy.State.splitBlocks]

@[simp]
theorem article_splitSuffix_found {n : ℕ} (state : Lazy.State n)
    (sourceId : Interface.BlockId) (source : Lazy.Block n)
    (prefixLength : ℕ) (prefixGap suffixGap : ℤ) :
    (state.split sourceId source prefixLength prefixGap suffixGap).blocks[
        state.blocks.length + 1]? =
      some (source.splitSuffix prefixLength suffixGap) := by
  simp [Lazy.State.split, Lazy.State.splitBlocks]

/-- Contracted-gap target for the three pieces produced while isolating one
interior element: the prefix, the singleton, and the suffix. -/
def articleIsolationGapTarget {n : ℕ} (view : Lazy.HeapView n)
    (before : List (Interface.Element n)) (isolated : Interface.Element n)
    (beforeGap afterGap : ℤ) (element : Interface.Element n) : ℕ :=
  if element ∈ before then
    Analysis.transientContractedGap (view.rawGap element) beforeGap
  else if element = isolated then
    Analysis.transientContractedGap
      (view.rawGap element) (view.rawGap isolated)
  else
    Analysis.transientContractedGap (view.rawGap element) afterGap

/-- Article Step 2 for one boundary child.

Two legal `Split`s isolate the selected child as a shrinking singleton.  The
only following value changes normalize the three descendants to their
attained interval minima; the complete macro performs neither an insert nor
a value increase. -/
theorem exists_articleIsolateElementRefinedTrace
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (stable : state.Stable params)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (found : state.blocks[sourceId]? = some source)
    (shrinking : source.mode = .shrinking)
    {before after : List (Interface.Element n)}
    {isolated : Interface.Element n}
    (decomposition : source.elements = before ++ isolated :: after) :
    ∃ beforeGap remainderGap afterGap firstState secondState
        isolatedId isolatedBlock events final,
      firstState = state.split sourceId source before.length
        beforeGap remainderGap ∧
      secondState = firstState.split (state.blocks.length + 1)
        (source.splitSuffix before.length remainderGap) 1
        (state.view.rawGap isolated) afterGap ∧
      isolatedId = firstState.blocks.length ∧
      isolatedBlock =
        (source.splitSuffix before.length remainderGap).splitPrefix 1
          (state.view.rawGap isolated) ∧
      events =
        [.operation (.split sourceId before.length),
          .operation (.split (state.blocks.length + 1) 1)] ++
          secondState.adjustValuesEvents
            (articleIsolationGapTarget state.view before isolated
              beforeGap afterGap) source.elements ∧
      final = secondState.adjustValues
        (articleIsolationGapTarget state.view before isolated
          beforeGap afterGap) source.elements ∧
      Trace params state events final ∧
      Interface.totalInserts (eraseOperations events) = 0 ∧
      Interface.totalIncreases (eraseOperations events) = 0 ∧
      final.view = state.view ∧
      final.blocks[isolatedId]? = some isolatedBlock ∧
      isolatedBlock.mode = .shrinking ∧
      isolatedBlock.elements = [isolated] ∧
      isolatedBlock.intervalGap = state.view.rawGap isolated ∧
      final.value isolated = 1 ∧
      (∀ element ∈ source.elements,
          final.value element =
            articleIsolationGapTarget state.view before isolated
              beforeGap afterGap element) ∧
      (∀ (oldId : Interface.BlockId) (oldBlock : Lazy.Block n),
        state.blocks[oldId]? = some oldBlock →
        oldId ≠ sourceId →
        final.blocks[oldId]? = some oldBlock) ∧
      final.Stable params ∧ state.PassRefinement final := by
  have takeEq : source.elements.take before.length = before := by
    simp [decomposition]
  have dropEq : source.elements.drop before.length = isolated :: after := by
    simp [decomposition]
  let beforeBase := source.splitPrefix before.length 0
  have beforeShrinking : beforeBase.mode = .shrinking := by
    simp [beforeBase, Lazy.Block.splitPrefix, shrinking]
  obtain ⟨beforeGap, beforeGapValid⟩ :=
    Lazy.Block.exists_gapValid_of_shrinking state.view beforeBase
      beforeShrinking
  change (source.splitPrefix before.length beforeGap).GapValid state.view
    at beforeGapValid
  let remainderBase := source.splitSuffix before.length 0
  have remainderShrinking : remainderBase.mode = .shrinking := by
    simp [remainderBase, Lazy.Block.splitSuffix, shrinking]
  obtain ⟨remainderGap, remainderGapValid⟩ :=
    Lazy.Block.exists_gapValid_of_shrinking state.view remainderBase
      remainderShrinking
  change (source.splitSuffix before.length remainderGap).GapValid state.view
    at remainderGapValid
  let remainder := source.splitSuffix before.length remainderGap
  have remainderMode : remainder.mode = .shrinking := by
    simp [remainder, Lazy.Block.splitSuffix, shrinking]
  have remainderElements : remainder.elements = isolated :: after := by
    simpa [remainder, Lazy.Block.splitSuffix] using dropEq
  let afterBase := remainder.splitSuffix 1 0
  have afterShrinking : afterBase.mode = .shrinking := by
    simp [afterBase, Lazy.Block.splitSuffix, remainderMode]
  obtain ⟨afterGap, afterGapValid⟩ :=
    Lazy.Block.exists_gapValid_of_shrinking state.view afterBase
      afterShrinking
  change (remainder.splitSuffix 1 afterGap).GapValid state.view
    at afterGapValid
  let isolatedBlock := remainder.splitPrefix 1 (state.view.rawGap isolated)
  have isolatedGapValid : isolatedBlock.GapValid state.view := by
    exact Lazy.Block.singleton_shrinking_gapValid state.view isolatedBlock
      (by simp [isolatedBlock, Lazy.Block.splitPrefix, remainderMode])
      isolated
      (by simp [isolatedBlock, Lazy.Block.splitPrefix, remainderElements])
      rfl
  let firstState := state.split sourceId source before.length
    beforeGap remainderGap
  have firstTrace : Trace params state
      [.operation (.split sourceId before.length)] firstState := by
    exact Trace.singleton
      (state.split_step sourceId source before.length beforeGap remainderGap
        stable.valid found shrinking (by simp [decomposition])
        beforeGapValid remainderGapValid)
  have remainderFound :
      firstState.blocks[state.blocks.length + 1]? = some remainder := by
    simp [firstState, remainder]
  let secondState := firstState.split (state.blocks.length + 1)
    remainder 1 (state.view.rawGap isolated) afterGap
  have secondBlocksEq : secondState.blocks =
      (state.blocks.modify sourceId Lazy.Block.emptiedAfterSplit) ++
        [source.splitPrefix before.length beforeGap,
          remainder.emptiedAfterSplit,
          remainder.splitPrefix 1 (state.view.rawGap isolated),
          remainder.splitSuffix 1 afterGap] := by
    dsimp [secondState, firstState]
    change
      (((state.blocks.modify sourceId Lazy.Block.emptiedAfterSplit) ++
          [source.splitPrefix before.length beforeGap,
            source.splitSuffix before.length remainderGap]).modify
          (state.blocks.length + 1) Lazy.Block.emptiedAfterSplit) ++
        [remainder.splitPrefix 1 (state.view.rawGap isolated),
          remainder.splitSuffix 1 afterGap] = _
    rw [show state.blocks.length =
        (state.blocks.modify sourceId Lazy.Block.emptiedAfterSplit).length by
      simp]
    rw [modify_second_appended]
    simp [remainder]
  have secondTrace : Trace params firstState
      [.operation (.split (state.blocks.length + 1) 1)] secondState := by
    exact Trace.singleton
      (firstState.split_step (state.blocks.length + 1) remainder 1
        (state.view.rawGap isolated) afterGap firstTrace.final_valid
        remainderFound remainderMode (by simp [remainderElements])
        (by simpa [firstState] using isolatedGapValid)
        (by simpa [firstState] using afterGapValid))
  let target := articleIsolationGapTarget state.view before isolated
    beforeGap afterGap
  have sourceMember : source ∈ state.blocks := List.mem_of_getElem? found
  have sourceStructural := stable.valid.2 source sourceMember
  have isolatedMember : isolated ∈ source.elements := by
    rw [decomposition]
    simp
  have sourceNonempty : source.elements ≠ [] :=
    List.ne_nil_of_mem isolatedMember
  have sourceMinimum :
      Analysis.IsIntervalGap source.elements.toFinset state.view.rawGap
        source.intervalGap := by
    have gapCases := sourceStructural.2.2
    simp only [Lazy.Block.GapValid, shrinking] at gapCases
    exact (Or.resolve_left gapCases (by
      rintro ⟨empty, _⟩
      exact sourceNonempty empty)).2
  have targetPositive : ∀ element ∈ source.elements,
      1 ≤ target element := by
    intro element elementMember
    by_cases inBefore : element ∈ before
    · simp [target, articleIsolationGapTarget, inBefore,
        Analysis.transientContractedGap, Analysis.contractedGap]
    · by_cases isIsolated : element = isolated
      · have isolatedNotBefore : isolated ∉ before := by
          simpa [isIsolated] using inBefore
        simp [target, articleIsolationGapTarget, isolatedNotBefore, isIsolated,
          Analysis.transientContractedGap, Analysis.contractedGap]
      · simp [target, articleIsolationGapTarget, inBefore, isIsolated,
          Analysis.transientContractedGap, Analysis.contractedGap]
  have targetLeState : ∀ element ∈ source.elements,
      target element ≤ state.value element := by
    intro element elementMember
    rw [stable.value_eq_transientContractedGap sourceMember elementMember]
    by_cases inBefore : element ∈ before
    · rw [show target element =
          Analysis.transientContractedGap
            (state.view.rawGap element) beforeGap by
        simp [target, articleIsolationGapTarget, inBefore]]
      have beforeNonempty : before ≠ [] := List.ne_nil_of_mem inBefore
      have beforeMinimum :
          Analysis.IsIntervalGap before.toFinset state.view.rawGap
            beforeGap := by
        have gapCases := beforeGapValid
        simp only [Lazy.Block.GapValid, Lazy.Block.splitPrefix, shrinking]
          at gapCases
        rw [takeEq] at gapCases
        exact (Or.resolve_left gapCases (by
          rintro ⟨empty, _⟩
          exact beforeNonempty empty)).2
      have oldLeBefore : source.intervalGap ≤ beforeGap :=
        sourceMinimum.le_of_subset beforeMinimum (by
          intro candidate candidateMember
          apply List.mem_toFinset.mpr
          rw [decomposition]
          exact List.mem_append_left _ (List.mem_toFinset.mp candidateMember))
      exact Analysis.transientContractedGap_antitone_intervalGap
        oldLeBefore (beforeMinimum.interval_le
          (List.mem_toFinset.mpr inBefore))
    · by_cases isIsolated : element = isolated
      · subst element
        rw [show target isolated =
            Analysis.transientContractedGap
              (state.view.rawGap isolated) (state.view.rawGap isolated) by
          simp [target, articleIsolationGapTarget, inBefore]]
        exact Analysis.transientContractedGap_antitone_intervalGap
          (sourceMinimum.interval_le
            (List.mem_toFinset.mpr isolatedMember)) le_rfl
      · have inAfter : element ∈ after := by
          rw [decomposition] at elementMember
          have inTail := (List.mem_append.mp elementMember).resolve_left inBefore
          exact (List.mem_cons.mp inTail).resolve_left isIsolated
        rw [show target element =
            Analysis.transientContractedGap
              (state.view.rawGap element) afterGap by
          simp [target, articleIsolationGapTarget, inBefore, isIsolated]]
        have afterNonempty : after ≠ [] := List.ne_nil_of_mem inAfter
        have afterMinimum :
            Analysis.IsIntervalGap after.toFinset state.view.rawGap
              afterGap := by
          have gapCases := afterGapValid
          simp only [Lazy.Block.GapValid, Lazy.Block.splitSuffix,
            remainderMode] at gapCases
          rw [remainderElements] at gapCases
          exact (Or.resolve_left gapCases (by
            rintro ⟨empty, _⟩
            exact afterNonempty empty)).2
        have oldLeAfter : source.intervalGap ≤ afterGap :=
          sourceMinimum.le_of_subset afterMinimum (by
            intro candidate candidateMember
            apply List.mem_toFinset.mpr
            rw [decomposition]
            simp [List.mem_toFinset.mp candidateMember])
        exact Analysis.transientContractedGap_antitone_intervalGap
          oldLeAfter (afterMinimum.interval_le
            (List.mem_toFinset.mpr inAfter))
  have targetBounded : ∀ element ∈ source.elements,
      target element ≤ params.valueBound := by
    intro element elementMember
    exact (targetLeState element elementMember).trans
      (stable.valid.toInterface.2.1 element).2
  let final := secondState.adjustValues target source.elements
  let adjustmentEvents := secondState.adjustValuesEvents target source.elements
  have structuralTrace : Trace params state
      [.operation (.split sourceId before.length),
        .operation (.split (state.blocks.length + 1) 1)] secondState :=
    firstTrace.append secondTrace
  have adjustmentTrace : Trace params secondState adjustmentEvents final := by
    exact secondState.adjustValues_trace target source.elements
      structuralTrace.final_valid targetPositive targetBounded
  have sourceNodup : source.elements.Nodup := by
    have interfaceFound : state.toInterface.block? sourceId =
        some source.toInterface := by
      unfold Interface.State.block? Lazy.State.toInterface
      simpa using congrArg (Option.map Lazy.Block.toInterface) found
    have interfaceNodup :=
      stable.valid.toInterface.block_elements_nodup interfaceFound
    change source.elements.Nodup at interfaceNodup
    exact interfaceNodup
  have secondValue : secondState.value = state.value := rfl
  have targetLeSecond : ∀ element ∈ source.elements,
      target element ≤ secondState.value element := by
    intro element elementMember
    rw [secondValue]
    exact targetLeState element elementMember
  have adjustmentNoIncreases : Interface.totalIncreases
      (eraseOperations adjustmentEvents) = 0 := by
    exact secondState.totalIncreases_adjustValuesEvents_eq_zero_of_le
      target source.elements sourceNodup targetLeSecond
  let events :=
    [.operation (.split sourceId before.length),
      .operation (.split (state.blocks.length + 1) 1)] ++ adjustmentEvents
  have fullTrace : Trace params state events final :=
    structuralTrace.append adjustmentTrace
  have noInserts : Interface.totalInserts (eraseOperations events) = 0 := by
    change Interface.totalInserts
      (eraseOperations
        ([.operation (.split sourceId before.length),
          .operation (.split (state.blocks.length + 1) 1)] ++
          adjustmentEvents)) = 0
    rw [eraseOperations_append]
    rw [articleTotalInserts_append]
    rw [secondState.totalInserts_adjustValuesEvents_eq_zero
      target source.elements]
    rfl
  have noIncreases : Interface.totalIncreases (eraseOperations events) = 0 := by
    change Interface.totalIncreases
      (eraseOperations
        ([.operation (.split sourceId before.length),
          .operation (.split (state.blocks.length + 1) 1)] ++
          adjustmentEvents)) = 0
    rw [eraseOperations_append]
    rw [articleTotalIncreases_append]
    rw [adjustmentNoIncreases]
    rfl
  let isolatedId : Interface.BlockId := firstState.blocks.length
  have isolatedFoundSecond :
      secondState.blocks[isolatedId]? = some isolatedBlock := by
    simp [secondState, isolatedId, isolatedBlock]
  have finalView : final.view = state.view := by
    calc
      final.view = secondState.view := by simp [final]
      _ = state.view := rfl
  have isolatedFoundFinal :
      final.blocks[isolatedId]? = some isolatedBlock := by
    simpa [final] using isolatedFoundSecond
  have isolatedMode : isolatedBlock.mode = .shrinking := by
    simp [isolatedBlock, Lazy.Block.splitPrefix, remainderMode]
  have isolatedElements : isolatedBlock.elements = [isolated] := by
    simp [isolatedBlock, Lazy.Block.splitPrefix, remainderElements]
  have isolatedIntervalGap :
      isolatedBlock.intervalGap = state.view.rawGap isolated := rfl
  have finalSourceValues : ∀ element ∈ source.elements,
      final.value element = target element := by
    intro element elementMember
    exact secondState.adjustValues_value_of_mem target sourceNodup
      elementMember targetPositive
  have isolatedNotBefore : isolated ∉ before := by
    have expandedNodup : (before ++ isolated :: after).Nodup := by
      rw [← decomposition]
      exact sourceNodup
    have disjoint := (List.nodup_append.mp expandedNodup).2.2
    intro inBefore
    exact disjoint isolated inBefore isolated (by simp) rfl
  have finalIsolatedValue : final.value isolated = 1 := by
    rw [finalSourceValues isolated isolatedMember]
    simp [target, articleIsolationGapTarget, isolatedNotBefore]
  have finalBlocks : final.blocks = secondState.blocks := by
    simp [final]
  have firstAssignedPerm : firstState.allElements.Perm state.allElements := by
    exact state.split_allElements_perm sourceId source before.length
      beforeGap remainderGap found
  have secondAssignedPerm :
      secondState.allElements.Perm firstState.allElements := by
    exact firstState.split_allElements_perm (state.blocks.length + 1)
      remainder 1 (state.view.rawGap isolated) afterGap remainderFound
  have finalComplete : final.Complete := by
    intro element
    have assignedIff : element ∈ final.allElements ↔
        element ∈ state.allElements := by
      rw [show final.allElements = secondState.allElements by
        simp [Lazy.State.allElements, finalBlocks]]
      exact (secondAssignedPerm.trans firstAssignedPerm).mem_iff
    rw [assignedIff, stable.2.1 element, finalView]
  have firstOneGrowing : firstState.OneGrowingPerSide :=
    state.split_oneGrowingPerSide sourceId source before.length
      beforeGap remainderGap found shrinking stable.2.2.2.1
  have secondOneGrowing : secondState.OneGrowingPerSide :=
    firstState.split_oneGrowingPerSide (state.blocks.length + 1)
      remainder 1 (state.view.rawGap isolated) afterGap remainderFound
      remainderMode firstOneGrowing
  have finalOneGrowing : final.OneGrowingPerSide := by
    rw [Lazy.State.OneGrowingPerSide, finalBlocks]
    exact secondOneGrowing
  have firstTopmost : firstState.GrowingTopmost :=
    articleSplit_growingTopmost state sourceId source before.length
      beforeGap remainderGap found shrinking stable.2.2.2.2.1
  have secondTopmost : secondState.GrowingTopmost :=
    articleSplit_growingTopmost firstState (state.blocks.length + 1)
      remainder 1 (state.view.rawGap isolated) afterGap remainderFound
      remainderMode firstTopmost
  have finalTopmost : final.GrowingTopmost := by
    rw [Lazy.State.GrowingTopmost, finalBlocks]
    intro id
    dsimp only
    intro growing
    obtain ⟨suffix, topDownEq⟩ := secondTopmost id growing
    refine ⟨suffix, ?_⟩
    rw [finalView]
    change secondState.view.topDown
      (secondState.blocks.get id).owner
      (secondState.blocks.get id).side =
        (secondState.blocks.get id).elements ++ suffix
    exact topDownEq
  have rootNotSource : state.view.root ∉ source.elements := by
    intro rootMember
    exact stable.valid.root_not_mem
      (Lazy.State.mem_allElements_iff.mpr
        ⟨source, sourceMember, rootMember⟩)
  have finalRootValue : final.value final.view.root = 1 := by
    rw [finalView]
    calc
      final.value state.view.root = secondState.value state.view.root := by
        rw [show final = secondState.adjustValues target source.elements by rfl]
        exact secondState.adjustValues_value_of_not_mem target
          source.elements rootNotSource
      _ = state.value state.view.root := rfl
      _ = 1 := stable.2.2.2.2.2.1
  have expandedNodup : (before ++ isolated :: after).Nodup := by
    rw [← decomposition]
    exact sourceNodup
  have beforeTailDisjoint := (List.nodup_append.mp expandedNodup).2.2
  have isolatedFresh : isolated ∉ after :=
    (List.nodup_cons.mp (List.nodup_append.mp expandedNodup).2.1).1
  have finalBlockValues : ∀ block ∈ final.blocks,
      ∀ element ∈ block.elements,
        final.value element =
          Analysis.transientContractedGap
            (final.view.rawGap element) block.intervalGap := by
    intro block blockMember element elementMember
    have secondMember : block ∈ secondState.blocks := by
      simpa only [finalBlocks] using blockMember
    rw [secondBlocksEq] at secondMember
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      at secondMember
    rcases secondMember with modifiedMember | beforeEq | emptyEq |
        singletonEq | afterEq
    · obtain ⟨blockId, modifiedFound⟩ :=
        List.mem_iff_getElem?.mp modifiedMember
      rw [List.getElem?_modify] at modifiedFound
      split at modifiedFound
      next selected =>
        have sourceAt : state.blocks[blockId]? = some source := by
          simpa only [selected] using found
        rw [sourceAt] at modifiedFound
        have blockEq : source.emptiedAfterSplit = block := by
          simpa using modifiedFound
        rw [← blockEq] at elementMember
        simp [Lazy.Block.emptiedAfterSplit] at elementMember
      next untouched =>
        have oldFound : state.blocks[blockId]? = some block := by
          simpa using modifiedFound
        have elementNotSource : element ∉ source.elements := by
          intro sourceElement
          have idsEq := stable.valid.blockId_eq_of_element_mem
            oldFound elementMember found sourceElement
          exact untouched idsEq.symm
        calc
          final.value element = secondState.value element := by
            rw [show final = secondState.adjustValues target source.elements by
              rfl]
            exact secondState.adjustValues_value_of_not_mem target
              source.elements elementNotSource
          _ = state.value element := rfl
          _ = Analysis.transientContractedGap
              (state.view.rawGap element) block.intervalGap :=
            stable.value_eq_transientContractedGap
              (List.mem_of_getElem? oldFound) elementMember
          _ = Analysis.transientContractedGap
              (final.view.rawGap element) block.intervalGap := by
            rw [finalView]
    · rw [beforeEq] at elementMember ⊢
      have inBefore : element ∈ before := by
        simpa [Lazy.Block.splitPrefix, takeEq] using elementMember
      have sourceElement : element ∈ source.elements := by
        rw [decomposition]
        exact List.mem_append_left _ inBefore
      rw [finalSourceValues element sourceElement]
      simp [target, articleIsolationGapTarget, inBefore,
        Lazy.Block.splitPrefix, finalView]
    · rw [emptyEq] at elementMember
      simp [Lazy.Block.emptiedAfterSplit] at elementMember
    · rw [singletonEq] at elementMember ⊢
      have elementEq : element = isolated := by
        simpa [isolatedBlock, Lazy.Block.splitPrefix, remainderElements]
          using elementMember
      subst element
      rw [finalIsolatedValue, finalView]
      simp [Lazy.Block.splitPrefix]
    · rw [afterEq] at elementMember ⊢
      have inAfter : element ∈ after := by
        simpa [Lazy.Block.splitSuffix, remainderElements]
          using elementMember
      have notBefore : element ∉ before := by
        intro inBefore
        exact beforeTailDisjoint element inBefore element
          (by simp [inAfter]) rfl
      have notIsolated : element ≠ isolated := by
        intro equal
        subst element
        exact isolatedFresh inAfter
      have sourceElement : element ∈ source.elements := by
        rw [decomposition]
        simp [inAfter]
      rw [finalSourceValues element sourceElement]
      simp [target, articleIsolationGapTarget, notBefore, notIsolated,
        Lazy.Block.splitSuffix, finalView]
  have finalValues : final.ValuesRealizeGaps :=
    ⟨finalRootValue, finalBlockValues⟩
  have finalOrdered : final.view.HeapOrdered := by
    rw [finalView]
    exact stable.2.2.1
  have finalStable : final.Stable params :=
    ⟨fullTrace.final_valid, finalComplete, finalOrdered,
      finalOneGrowing, finalTopmost, finalValues⟩
  have oldBlocksPreserved :
      ∀ (oldId : Interface.BlockId) (oldBlock : Lazy.Block n),
      state.blocks[oldId]? = some oldBlock →
      oldId ≠ sourceId →
      final.blocks[oldId]? = some oldBlock := by
    intro oldId oldBlock oldFound different
    obtain ⟨oldLt, _oldGet⟩ := List.getElem?_eq_some_iff.mp oldFound
    rw [finalBlocks, secondBlocksEq]
    rw [List.getElem?_append_left (by simpa using oldLt)]
    rw [List.getElem?_modify_ne _ _ (Ne.symm different)]
    exact oldFound
  refine ⟨beforeGap, remainderGap, afterGap, firstState, secondState,
    isolatedId, isolatedBlock, events, final, rfl, rfl, rfl, rfl, rfl,
    rfl, fullTrace, noInserts, noIncreases, finalView,
    isolatedFoundFinal, isolatedMode, isolatedElements,
    isolatedIntervalGap, finalIsolatedValue, finalSourceValues,
    oldBlocksPreserved, finalStable, ?_⟩
  exact ((state.split_passRefinement sourceId source before.length beforeGap remainderGap found).trans
    (firstState.split_passRefinement (state.blocks.length + 1) remainder 1
      (state.view.rawGap isolated) afterGap remainderFound)).trans
    (State.PassRefinement.of_blocks_eq finalBlocks)


/-- Compatibility wrapper for the original preparation statement. -/
theorem exists_articleIsolateElementTrace
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (stable : state.Stable params)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (found : state.blocks[sourceId]? = some source)
    (shrinking : source.mode = .shrinking)
    {before after : List (Interface.Element n)}
    {isolated : Interface.Element n}
    (decomposition : source.elements = before ++ isolated :: after) :
    ∃ beforeGap remainderGap afterGap firstState secondState
        isolatedId isolatedBlock events final,
      firstState = state.split sourceId source before.length
        beforeGap remainderGap ∧
      secondState = firstState.split (state.blocks.length + 1)
        (source.splitSuffix before.length remainderGap) 1
        (state.view.rawGap isolated) afterGap ∧
      isolatedId = firstState.blocks.length ∧
      isolatedBlock =
        (source.splitSuffix before.length remainderGap).splitPrefix 1
          (state.view.rawGap isolated) ∧
      events =
        [.operation (.split sourceId before.length),
          .operation (.split (state.blocks.length + 1) 1)] ++
          secondState.adjustValuesEvents
            (articleIsolationGapTarget state.view before isolated
              beforeGap afterGap) source.elements ∧
      final = secondState.adjustValues
        (articleIsolationGapTarget state.view before isolated
          beforeGap afterGap) source.elements ∧
      Trace params state events final ∧
      Interface.totalInserts (eraseOperations events) = 0 ∧
      Interface.totalIncreases (eraseOperations events) = 0 ∧
      final.view = state.view ∧
      final.blocks[isolatedId]? = some isolatedBlock ∧
      isolatedBlock.mode = .shrinking ∧
      isolatedBlock.elements = [isolated] ∧
      isolatedBlock.intervalGap = state.view.rawGap isolated ∧
      final.value isolated = 1 ∧
      (∀ element ∈ source.elements,
          final.value element =
            articleIsolationGapTarget state.view before isolated
              beforeGap afterGap element) ∧
      (∀ (oldId : Interface.BlockId) (oldBlock : Lazy.Block n),
        state.blocks[oldId]? = some oldBlock →
        oldId ≠ sourceId →
        final.blocks[oldId]? = some oldBlock) ∧
      final.Stable params := by
  obtain ⟨a, b, c, first, second, id, block, events, final, firstEq, secondEq, idEq, blockEq,
    eventsEq, finalEq, trace, noInserts, noIncreases, viewEq, found, mode, elements, gap, value,
    values, frame, stable, _⟩ := exists_articleIsolateElementRefinedTrace stable found shrinking decomposition
  exact ⟨a, b, c, first, second, id, block, events, final, firstEq, secondEq, idEq, blockEq,
    eventsEq, finalEq, trace, noInserts, noIncreases, viewEq, found, mode, elements, gap, value,
    values, frame, stable⟩

/-- Article Steps 1--2 for one boundary child, independent of the source
mode.  A growing source is first converted and replaced; a shrinking source
is split directly.  In both cases the result is a stable shrinking singleton,
with no interface insert and no value increase. -/
theorem exists_articlePrepareElementRefinedTrace
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (stable : state.Stable params)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (found : state.blocks[sourceId]? = some source)
    {before after : List (Interface.Element n)}
    {isolated : Interface.Element n}
    (decomposition : source.elements = before ++ isolated :: after) :
    ∃ (events : List (Event n)) (final : Lazy.State n)
        (isolatedId : Interface.BlockId) (isolatedBlock : Lazy.Block n),
      Trace params state events final ∧
      final.blocks.length ≤ state.blocks.length + 5 ∧
      Interface.totalInserts (eraseOperations events) = 0 ∧
      Interface.totalIncreases (eraseOperations events) = 0 ∧
      final.Stable params ∧
      final.view = state.view ∧
      final.blocks[isolatedId]? = some isolatedBlock ∧
      isolatedBlock.mode = .shrinking ∧
      isolatedBlock.elements = [isolated] ∧
      isolatedBlock.intervalGap = state.view.rawGap isolated ∧
      final.value isolated = 1 ∧
      (∀ oldId oldBlock,
        state.blocks[oldId]? = some oldBlock →
        oldId ≠ sourceId →
        final.blocks[oldId]? = some oldBlock) ∧ state.PassRefinement final := by
  cases modeEq : source.mode with
  | shrinking =>
      obtain ⟨_beforeGap, _remainderGap, _afterGap, _firstState,
          _secondState, isolatedId, isolatedBlock, events, final,
          _firstEq, _secondEq, _idEq, _blockEq, _eventsEq, _finalEq,
          trace, noInserts, noIncreases, finalView, isolatedFound,
          isolatedMode, isolatedElements, isolatedGap, isolatedValue,
          _sourceValues, oldBlocksPreserved, finalStable, refinement⟩ :=
        exists_articleIsolateElementRefinedTrace stable found modeEq decomposition
      have birthBound : final.blocks.length ≤ state.blocks.length + 5 := by
        simp [_finalEq, _secondEq, _firstEq, State.split, State.splitBlocks]
      exact ⟨events, final, isolatedId, isolatedBlock, trace, birthBound,
        noInserts, noIncreases, finalStable, finalView, isolatedFound,
        isolatedMode, isolatedElements, isolatedGap, isolatedValue,
        oldBlocksPreserved, refinement⟩
  | growing =>
      obtain ⟨intervalGap, converted, convertEvents, convertFinal,
          _gapValid, convertedEq, convertEventsEq, convertFinalEq,
          convertTrace, adjustmentNoIncreases, _convertBlocks,
          convertView, convertSourceValues⟩ :=
        exists_articleConvertAndCreateAdjustedTrace stable found modeEq
      have convertStable : convertFinal.Stable params :=
        articleConvertAndCreateAdjusted_stable stable found modeEq intervalGap
          convertedEq convertFinalEq convertTrace convertSourceValues
      let convertedBlock := source.converted intervalGap
      have convertedFound :
          converted.blocks[sourceId]? = some convertedBlock := by
        rw [convertedEq]
        obtain ⟨sourceLt, _sourceGet⟩ := List.getElem?_eq_some_iff.mp found
        change
          ((state.blocks.modify sourceId fun old => old.converted intervalGap) ++
              [Lazy.Block.emptyGrowing source.creator source.side])[sourceId]? =
            some convertedBlock
        rw [List.getElem?_append_left (by simpa using sourceLt)]
        rw [List.getElem?_modify_eq, found]
        rfl
      have convertFinalFound :
          convertFinal.blocks[sourceId]? = some convertedBlock := by
        simpa [convertFinalEq] using convertedFound
      have convertedShrinking : convertedBlock.mode = .shrinking := rfl
      have convertedDecomposition :
          convertedBlock.elements = before ++ isolated :: after := by
        simpa [convertedBlock, Lazy.Block.converted] using decomposition
      obtain ⟨_beforeGap, _remainderGap, _afterGap, _firstState,
          _secondState, isolatedId, isolatedBlock, isolateEvents, final,
          _firstEq, _secondEq, _idEq, _blockEq, _eventsEq, _finalEq,
          isolateTrace, isolateNoInserts, isolateNoIncreases,
          isolateView, isolatedFound, isolatedMode, isolatedElements,
          isolatedGap, isolatedValue, _sourceValues,
          isolatePreserved, finalStable, isolateRefinement⟩ :=
        exists_articleIsolateElementRefinedTrace convertStable convertFinalFound
          convertedShrinking convertedDecomposition
      have convertPreserved : ∀ oldId oldBlock,
          state.blocks[oldId]? = some oldBlock →
          oldId ≠ sourceId →
          convertFinal.blocks[oldId]? = some oldBlock := by
        intro oldId oldBlock oldFound different
        obtain ⟨oldLt, _oldGet⟩ := List.getElem?_eq_some_iff.mp oldFound
        rw [show convertFinal.blocks = converted.blocks by
          simp [convertFinalEq]]
        rw [convertedEq]
        change
          ((state.blocks.modify sourceId fun old => old.converted intervalGap) ++
              [Lazy.Block.emptyGrowing source.creator source.side])[oldId]? =
            some oldBlock
        rw [List.getElem?_append_left (by simpa using oldLt)]
        rw [List.getElem?_modify_ne _ _ (Ne.symm different)]
        exact oldFound
      have convertNoInserts :
          Interface.totalInserts (eraseOperations convertEvents) = 0 := by
        rw [convertEventsEq, eraseOperations_append,
          articleTotalInserts_append]
        rw [converted.totalInserts_adjustValuesEvents_eq_zero
          (articleConvertedGapTarget state.view intervalGap) source.elements]
        rfl
      have convertNoIncreases :
          Interface.totalIncreases (eraseOperations convertEvents) = 0 := by
        rw [convertEventsEq, eraseOperations_append,
          articleTotalIncreases_append, adjustmentNoIncreases]
        rfl
      let events := convertEvents ++ isolateEvents
      have fullTrace : Trace params state events final :=
        convertTrace.append isolateTrace
      have noInserts : Interface.totalInserts (eraseOperations events) = 0 := by
        rw [show events = convertEvents ++ isolateEvents by rfl,
          eraseOperations_append, articleTotalInserts_append,
          convertNoInserts, isolateNoInserts, zero_add]
      have noIncreases :
          Interface.totalIncreases (eraseOperations events) = 0 := by
        rw [show events = convertEvents ++ isolateEvents by rfl,
          eraseOperations_append, articleTotalIncreases_append,
          convertNoIncreases, isolateNoIncreases, zero_add]
      have finalView : final.view = state.view :=
        isolateView.trans convertView
      have isolatedGapAtInitial :
          isolatedBlock.intervalGap = state.view.rawGap isolated := by
        rw [isolatedGap, convertView]
      have oldBlocksPreserved : ∀ oldId oldBlock,
          state.blocks[oldId]? = some oldBlock →
          oldId ≠ sourceId →
          final.blocks[oldId]? = some oldBlock := by
        intro oldId oldBlock oldFound different
        exact isolatePreserved oldId oldBlock
          (convertPreserved oldId oldBlock oldFound different) different
      have birthBound : final.blocks.length ≤ state.blocks.length + 5 := by
        simp [_finalEq, _secondEq, _firstEq, State.split, State.splitBlocks,
          convertFinalEq, convertedEq, State.create, State.convert]
      have convertRefinement : state.PassRefinement convertFinal := by
        apply ((state.convert_passRefinement sourceId intervalGap).trans
          ((state.convert sourceId intervalGap).create_passRefinement source.creator source.side)).trans
        apply State.PassRefinement.of_blocks_eq
        simp [convertFinalEq, convertedEq]
      exact ⟨events, final, isolatedId, isolatedBlock, fullTrace, birthBound,
        noInserts, noIncreases, finalStable, finalView, isolatedFound,
        isolatedMode, isolatedElements, isolatedGapAtInitial, isolatedValue,
        oldBlocksPreserved, convertRefinement.trans isolateRefinement⟩


/-- Compatibility wrapper for the original preparation statement. -/
theorem exists_articlePrepareElementTrace
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (stable : state.Stable params)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (found : state.blocks[sourceId]? = some source)
    {before after : List (Interface.Element n)}
    {isolated : Interface.Element n}
    (decomposition : source.elements = before ++ isolated :: after) :
    ∃ (events : List (Event n)) (final : Lazy.State n)
        (isolatedId : Interface.BlockId) (isolatedBlock : Lazy.Block n),
      Trace params state events final ∧
      final.blocks.length ≤ state.blocks.length + 5 ∧
      Interface.totalInserts (eraseOperations events) = 0 ∧
      Interface.totalIncreases (eraseOperations events) = 0 ∧
      final.Stable params ∧
      final.view = state.view ∧
      final.blocks[isolatedId]? = some isolatedBlock ∧
      isolatedBlock.mode = .shrinking ∧
      isolatedBlock.elements = [isolated] ∧
      isolatedBlock.intervalGap = state.view.rawGap isolated ∧
      final.value isolated = 1 ∧
      ∀ oldId oldBlock,
        state.blocks[oldId]? = some oldBlock →
        oldId ≠ sourceId →
        final.blocks[oldId]? = some oldBlock := by
  obtain ⟨events, final, id, block, trace, births, noInserts, noIncreases, finalStable,
    viewEq, found, mode, elements, gap, value, frame, _⟩ :=
    exists_articlePrepareElementRefinedTrace stable found decomposition
  exact ⟨events, final, id, block, trace, births, noInserts, noIncreases, finalStable,
    viewEq, found, mode, elements, gap, value, frame⟩

/-- Article Steps 1--2 for both boundary children.  The theorem is geometric
only in requiring that both children are currently assigned and distinct;
it locates their blocks, converts if needed, isolates them successively, and
keeps the first singleton persistent while preparing the second. -/
theorem exists_articlePrepareTwoElementsTrace
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (stable : state.Stable params)
    {first second : Interface.Element n}
    (firstAssigned : first ∈ state.allElements)
    (secondAssigned : second ∈ state.allElements)
    (distinct : first ≠ second) :
    ∃ (events : List (Event n)) (final : Lazy.State n)
        (firstId secondId : Interface.BlockId)
        (firstBlock secondBlock : Lazy.Block n),
      Trace params state events final ∧
      final.blocks.length ≤ state.blocks.length + 10 ∧
      Interface.totalInserts (eraseOperations events) = 0 ∧
      Interface.totalIncreases (eraseOperations events) = 0 ∧
      final.Stable params ∧
      final.view = state.view ∧
      final.blocks[firstId]? = some firstBlock ∧
      firstBlock.mode = .shrinking ∧
      firstBlock.elements = [first] ∧
      firstBlock.intervalGap = state.view.rawGap first ∧
      final.value first = 1 ∧
      final.blocks[secondId]? = some secondBlock ∧
      secondBlock.mode = .shrinking ∧
      secondBlock.elements = [second] ∧
      secondBlock.intervalGap = state.view.rawGap second ∧
      final.value second = 1 ∧
      (∀ (oldId : Interface.BlockId) (oldBlock : Lazy.Block n),
        state.blocks[oldId]? = some oldBlock →
        first ∉ oldBlock.elements →
        second ∉ oldBlock.elements →
        final.blocks[oldId]? = some oldBlock) := by
  obtain ⟨firstSource, firstSourceMember, firstMember⟩ :=
    Lazy.State.mem_allElements_iff.mp firstAssigned
  obtain ⟨firstSourceId, firstFound⟩ :=
    List.mem_iff_getElem?.mp firstSourceMember
  obtain ⟨firstBefore, firstAfter, firstDecomposition⟩ :=
    List.mem_iff_append.mp firstMember
  obtain ⟨firstEvents, firstFinal, firstId, firstBlock, firstTrace, firstBirth,
      firstNoInserts, firstNoIncreases, firstStable, firstView,
      firstIsolatedFound, firstMode, firstElements, firstGap, firstValue,
      firstPreserved⟩ :=
    exists_articlePrepareElementTrace stable firstFound firstDecomposition
  have secondParented : state.view.parent second ≠ none :=
    (stable.2.1 second).mp secondAssigned
  have secondAssignedFirst : second ∈ firstFinal.allElements := by
    apply (firstStable.2.1 second).mpr
    rw [firstView]
    exact secondParented
  obtain ⟨secondSource, secondSourceMember, secondMember⟩ :=
    Lazy.State.mem_allElements_iff.mp secondAssignedFirst
  obtain ⟨secondSourceId, secondFound⟩ :=
    List.mem_iff_getElem?.mp secondSourceMember
  obtain ⟨secondBefore, secondAfter, secondDecomposition⟩ :=
    List.mem_iff_append.mp secondMember
  have secondSourceNeFirst : secondSourceId ≠ firstId := by
    intro equal
    subst secondSourceId
    rw [firstIsolatedFound] at secondFound
    have blockEq : firstBlock = secondSource := Option.some.inj secondFound
    rw [← blockEq, firstElements] at secondMember
    have secondEqFirst : second = first := by simpa using secondMember
    exact distinct secondEqFirst.symm
  obtain ⟨secondEvents, final, secondId, secondBlock, secondTrace, secondBirth,
      secondNoInserts, secondNoIncreases, finalStable, secondView,
      secondIsolatedFound, secondMode, secondElements, secondGap,
      secondValue, secondPreserved⟩ :=
    exists_articlePrepareElementTrace firstStable secondFound
      secondDecomposition
  have firstIsolatedFinal : final.blocks[firstId]? = some firstBlock :=
    secondPreserved firstId firstBlock firstIsolatedFound
      secondSourceNeFirst.symm
  let events := firstEvents ++ secondEvents
  have fullTrace : Trace params state events final :=
    firstTrace.append secondTrace
  have noInserts : Interface.totalInserts (eraseOperations events) = 0 := by
    rw [show events = firstEvents ++ secondEvents by rfl,
      eraseOperations_append, articleTotalInserts_append,
      firstNoInserts, secondNoInserts, zero_add]
  have noIncreases : Interface.totalIncreases (eraseOperations events) = 0 := by
    rw [show events = firstEvents ++ secondEvents by rfl,
      eraseOperations_append, articleTotalIncreases_append,
      firstNoIncreases, secondNoIncreases, zero_add]
  have finalView : final.view = state.view := secondView.trans firstView
  have firstValueFinal : final.value first = 1 := by
    rw [finalStable.value_eq_transientContractedGap
      (List.mem_of_getElem? firstIsolatedFinal) (by simp [firstElements])]
    rw [firstGap, finalView]
    exact Analysis.transientContractedGap_self _
  have secondGapAtInitial :
      secondBlock.intervalGap = state.view.rawGap second := by
    rw [secondGap, firstView]
  have oldBlocksPreserved :
      ∀ (oldId : Interface.BlockId) (oldBlock : Lazy.Block n),
      state.blocks[oldId]? = some oldBlock →
      first ∉ oldBlock.elements →
      second ∉ oldBlock.elements →
      final.blocks[oldId]? = some oldBlock := by
    intro oldId oldBlock oldFound firstFresh secondFresh
    have oldNeFirstSource : oldId ≠ firstSourceId := by
      intro equal
      subst oldId
      rw [firstFound] at oldFound
      have blockEq : oldBlock = firstSource :=
        (Option.some.inj oldFound).symm
      exact firstFresh (by simpa [blockEq] using firstMember)
    have oldFoundFirst : firstFinal.blocks[oldId]? = some oldBlock :=
      firstPreserved oldId oldBlock oldFound oldNeFirstSource
    have oldNeSecondSource : oldId ≠ secondSourceId := by
      intro equal
      subst oldId
      rw [secondFound] at oldFoundFirst
      have blockEq : oldBlock = secondSource :=
        (Option.some.inj oldFoundFirst).symm
      exact secondFresh (by simpa [blockEq] using secondMember)
    exact secondPreserved oldId oldBlock oldFoundFirst oldNeSecondSource
  exact ⟨events, final, firstId, secondId, firstBlock, secondBlock,
    fullTrace, by omega, noInserts, noIncreases, finalStable, finalView,
    firstIsolatedFinal, firstMode, firstElements, firstGap, firstValueFinal,
    secondIsolatedFound, secondMode, secondElements, secondGapAtInitial,
    secondValue, oldBlocksPreserved⟩

/-- Isolate the canonical boundary minima `x⁻` and `x⁺`, converting their
containing intervals on demand.  This is the local Step 2 macro; the complete
article-ordered Step 1 followed by Step 2 is packaged below in
`exists_articlePrepareCanonicalSetupTrace`.

Rank zero identifies the accessed value with the canonical root.  The strict
boundary ordering therefore makes both minima non-root elements, so
completeness assigns them to blocks and the generic two-element preparation
theorem applies. -/
theorem exists_articlePrepareCanonicalBoundariesTrace
    {n : ℕ} (snapshot : Snapshot n) (before : BST 0 n)
    (key : Fin n)
    (rankZero : snapshot.rank (valuePos key) = 0)
    {params : Interface.Parameters} {state : Lazy.State n}
    (represents : state.Represents params snapshot before) :
    let selection :=
      WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
        snapshot before key
    ∃ (events : List (Event n)) (final : Lazy.State n)
        (leftId rightId : Interface.BlockId)
        (leftBlock rightBlock : Lazy.Block n),
      Trace params state events final ∧
      final.blocks.length ≤ state.blocks.length + 10 ∧
      Interface.totalInserts (eraseOperations events) = 0 ∧
      Interface.totalIncreases (eraseOperations events) = 0 ∧
      final.Stable params ∧
      final.view = state.view ∧
      final.blocks[leftId]? = some leftBlock ∧
      leftBlock.mode = .shrinking ∧
      leftBlock.elements = [selection.left] ∧
      leftBlock.intervalGap = state.view.rawGap selection.left ∧
      final.value selection.left = 1 ∧
      final.blocks[rightId]? = some rightBlock ∧
      rightBlock.mode = .shrinking ∧
      rightBlock.elements = [selection.right] ∧
      rightBlock.intervalGap = state.view.rawGap selection.right ∧
      final.value selection.right = 1 ∧
      (∀ (oldId : Interface.BlockId) (oldBlock : Lazy.Block n),
        state.blocks[oldId]? = some oldBlock →
        selection.left ∉ oldBlock.elements →
        selection.right ∉ oldBlock.elements →
        final.blocks[oldId]? = some oldBlock) := by
  let selection :=
    WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
      snapshot before key
  have rootEq :
      Canonical.canonicalRoot snapshot before = valuePos key :=
    Canonical.canonicalRoot_eq_of_rank_eq_zero snapshot before rankZero
  have leftNeRoot :
      selection.left ≠ Canonical.canonicalRoot snapshot before := by
    rw [rootEq]
    exact ne_of_lt selection.ordered.1
  have rightNeRoot :
      selection.right ≠ Canonical.canonicalRoot snapshot before := by
    rw [rootEq]
    exact ne_of_gt selection.ordered.2
  have leftParented : state.view.parent selection.left ≠ none := by
    rw [represents.view_eq]
    exact
      (Canonical.canonicalHeapView snapshot before).parent_ne_none_of_ne_root
        leftNeRoot
  have rightParented : state.view.parent selection.right ≠ none := by
    rw [represents.view_eq]
    exact
      (Canonical.canonicalHeapView snapshot before).parent_ne_none_of_ne_root
        rightNeRoot
  have leftAssigned : selection.left ∈ state.allElements :=
    (represents.complete selection.left).2 leftParented
  have rightAssigned : selection.right ∈ state.allElements :=
    (represents.complete selection.right).2 rightParented
  have distinct : selection.left ≠ selection.right :=
    ne_of_lt (selection.ordered.1.trans selection.ordered.2)
  exact exists_articlePrepareTwoElementsTrace represents.stable
    leftAssigned rightAssigned distinct

/-- Complete article setup Steps 1--2 at the canonical boundaries.

First all growing intervals of `x`, `x⁻`, and `x⁺` are made empty by at
most six convert/create macros.  Then `x⁻` and `x⁺` are isolated as shrinking
singletons.  The split phase preserves every empty growing block, so the
whole endpoint is again a represented stable state with exactly the setup
claimed before the two pairing phases in the manuscript. -/
theorem exists_articlePrepareCanonicalSetupTrace
    {n : ℕ} (snapshot : Snapshot n) (before : BST 0 n)
    (key : Fin n)
    (rankZero : snapshot.rank (valuePos key) = 0)
    {params : Interface.Parameters} {state : Lazy.State n}
    (represents : state.Represents params snapshot before) :
    let selection :=
      WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
        snapshot before key
    ∃ (events : List (Event n)) (final : Lazy.State n)
        (leftId rightId : Interface.BlockId)
        (leftBlock rightBlock : Lazy.Block n),
      Trace params state events final ∧
      final.blocks.length ≤ state.blocks.length + 16 ∧
      Interface.totalInserts (eraseOperations events) = 0 ∧
      Interface.totalIncreases (eraseOperations events) = 0 ∧
      final.Represents params snapshot before ∧
      ArticleGrowingOwnerEmpty final (valuePos key) ∧
      ArticleGrowingOwnerEmpty final selection.left ∧
      ArticleGrowingOwnerEmpty final selection.right ∧
      final.blocks[leftId]? = some leftBlock ∧
      leftBlock.mode = .shrinking ∧
      leftBlock.elements = [selection.left] ∧
      leftBlock.intervalGap = state.view.rawGap selection.left ∧
      final.value selection.left = 1 ∧
      final.blocks[rightId]? = some rightBlock ∧
      rightBlock.mode = .shrinking ∧
      rightBlock.elements = [selection.right] ∧
      rightBlock.intervalGap = state.view.rawGap selection.right ∧
      final.value selection.right = 1 := by
  let selection :=
    WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
      snapshot before key
  obtain ⟨convertEvents, converted, convertTrace, convertBirth, convertNoInserts,
      convertNoIncreases, convertedRepresents, accessedEmpty, leftEmpty,
      rightEmpty⟩ :=
    exists_articleEmptyCanonicalOwnersTrace snapshot before key represents
  obtain ⟨isolateEvents, final, leftId, rightId, leftBlock, rightBlock,
      isolateTrace, isolateBirth, isolateNoInserts, isolateNoIncreases, finalStable,
      isolateView, leftFound, leftMode, leftElements, leftGap, leftValue,
      rightFound, rightMode, rightElements, rightGap, rightValue,
      boundaryPreserved⟩ :=
    exists_articlePrepareCanonicalBoundariesTrace snapshot before key rankZero
      convertedRepresents
  have convertedView : converted.view = state.view :=
    convertedRepresents.view_eq.trans represents.view_eq.symm
  have preserveEmpty :
      ∀ (oldId : Interface.BlockId) (oldBlock : Lazy.Block n),
        converted.blocks[oldId]? = some oldBlock →
        oldBlock.elements = [] →
        final.blocks[oldId]? = some oldBlock := by
    intro oldId oldBlock oldFound empty
    exact boundaryPreserved oldId oldBlock oldFound
      (by simp [empty]) (by simp [empty])
  have accessedLeftFinal :
      ArticleGrowingEmptyAt final (valuePos key) .left :=
    ArticleGrowingEmptyAt.of_preserved convertedRepresents.stable finalStable
      accessedEmpty.1 preserveEmpty
  have accessedRightFinal :
      ArticleGrowingEmptyAt final (valuePos key) .right :=
    ArticleGrowingEmptyAt.of_preserved convertedRepresents.stable finalStable
      accessedEmpty.2 preserveEmpty
  have leftLeftFinal :
      ArticleGrowingEmptyAt final selection.left .left :=
    ArticleGrowingEmptyAt.of_preserved convertedRepresents.stable finalStable
      leftEmpty.1 preserveEmpty
  have leftRightFinal :
      ArticleGrowingEmptyAt final selection.left .right :=
    ArticleGrowingEmptyAt.of_preserved convertedRepresents.stable finalStable
      leftEmpty.2 preserveEmpty
  have rightLeftFinal :
      ArticleGrowingEmptyAt final selection.right .left :=
    ArticleGrowingEmptyAt.of_preserved convertedRepresents.stable finalStable
      rightEmpty.1 preserveEmpty
  have rightRightFinal :
      ArticleGrowingEmptyAt final selection.right .right :=
    ArticleGrowingEmptyAt.of_preserved convertedRepresents.stable finalStable
      rightEmpty.2 preserveEmpty
  have finalRepresents : final.Represents params snapshot before :=
    ⟨finalStable, isolateView.trans convertedRepresents.view_eq⟩
  have leftGapInitial :
      leftBlock.intervalGap = state.view.rawGap selection.left := by
    rw [leftGap, convertedView]
  have rightGapInitial :
      rightBlock.intervalGap = state.view.rawGap selection.right := by
    rw [rightGap, convertedView]
  let events := convertEvents ++ isolateEvents
  have fullTrace : Trace params state events final :=
    convertTrace.append isolateTrace
  have noInserts : Interface.totalInserts (eraseOperations events) = 0 := by
    rw [show events = convertEvents ++ isolateEvents by rfl,
      eraseOperations_append, articleTotalInserts_append,
      convertNoInserts, isolateNoInserts, zero_add]
  have noIncreases :
      Interface.totalIncreases (eraseOperations events) = 0 := by
    rw [show events = convertEvents ++ isolateEvents by rfl,
      eraseOperations_append, articleTotalIncreases_append,
      convertNoIncreases, isolateNoIncreases, zero_add]
  exact ⟨events, final, leftId, rightId, leftBlock, rightBlock,
    fullTrace, by omega, noInserts, noIncreases, finalRepresents,
    ⟨accessedLeftFinal, accessedRightFinal⟩,
    ⟨leftLeftFinal, leftRightFinal⟩,
    ⟨rightLeftFinal, rightRightFinal⟩,
    leftFound, leftMode, leftElements, leftGapInitial, leftValue,
    rightFound, rightMode, rightElements, rightGapInitial, rightValue⟩

/-- Once Step 2 has isolated the two canonical boundary singletons, every
other block of the accessed owner has the exact erase witness required by the
article's internal-pairing lemma.  The removed element is `x⁻` on the left
and `x⁺` on the right. -/
theorem exists_articleIsolatedBoundariesWitness
    {n : ℕ} (snapshot : Snapshot n) (before : BST 0 n)
    (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    {params : Interface.Parameters} {state : Lazy.State n}
    (represents : state.Represents params snapshot before)
    {leftId rightId : Interface.BlockId}
    {leftBlock rightBlock : Lazy.Block n}
    (leftFound : state.blocks[leftId]? = some leftBlock)
    (leftElements :
      leftBlock.elements =
        [(WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
          snapshot before key).left])
    (rightFound : state.blocks[rightId]? = some rightBlock)
    (rightElements :
      rightBlock.elements =
        [(WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
          snapshot before key).right])
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (ownerEq : source.owner = valuePos key)
    (sourceNeLeft : sourceId ≠ leftId)
    (sourceNeRight : sourceId ≠ rightId) :
    ∃ removed : List (Interface.Element n),
      (rootHeavyPathCanonicalChildOrder
          snapshot before key.isLt rankZero).elements.filter
            (fun element => decide
              (canonicalSide snapshot before element = source.side)) =
        removed.foldl List.erase
          (state.view.attachedTopDown state.allElements
            source.owner source.side) ∧
      ∀ element ∈ removed, element ∉ source.elements := by
  let selection :=
    WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
      snapshot before key
  have attachedEq :=
    Lazy.State.Complete.attachedTopDown_eq_topDown represents.complete
      source.owner source.side
  cases sideEq : source.side with
  | left =>
      refine ⟨[selection.left], ?_, ?_⟩
      · rw [sideEq] at attachedEq
        rw [attachedEq, ownerEq, represents.view_eq]
        simpa only [selection, sideEq] using
          proper_filter_eq_erase_boundary_canonicalTopDown
            snapshot before key rankZero .left
      · intro element member
        have elementEq : element = selection.left := by
          simpa only [List.mem_singleton] using member
        subst element
        intro sourceMember
        apply sourceNeLeft
        exact represents.valid.blockId_eq_of_element_mem
          sourceFound sourceMember leftFound (by simp [leftElements, selection])
  | right =>
      refine ⟨[selection.right], ?_, ?_⟩
      · rw [sideEq] at attachedEq
        rw [attachedEq, ownerEq, represents.view_eq]
        simpa only [selection, sideEq] using
          proper_filter_eq_erase_boundary_canonicalTopDown
            snapshot before key rankZero .right
      · intro element member
        have elementEq : element = selection.right := by
          simpa only [List.mem_singleton] using member
        subst element
        intro sourceMember
        apply sourceNeRight
        exact represents.valid.blockId_eq_of_element_mem
          sourceFound sourceMember rightFound (by simp [rightElements, selection])

/-- End-to-end local article lemma from one already isolated unbroken lazy
interval.  It constructs the constant-six fraction certificate, both retained
endpoint batches, and either proves that there is no internal batch or emits
the complete legal two-pass rich trace. -/
theorem article_internalPairingExecution
    {n key : ℕ} (snapshot : Snapshot n)
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    {params : Interface.Parameters} {state : Lazy.State n}
    (represents : state.Represents params snapshot before)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceShrinking : source.mode = .shrinking)
    (ownerEq : source.owner = valuePos ⟨key, key_lt_n⟩)
    (unbroken : canonicalBlockCrossSideUnbroken snapshot before source)
    (sideSegment :
      IsSegment source.elements
        ((rootHeavyPathCanonicalChildOrder snapshot before key_lt_n rankZero).elements.filter
          (fun element => decide
            (canonicalSide snapshot before element = source.side))))
    (articleFraction :
      10 * params.matchingNumerator ≤ params.matchingDenominator) :
    Nonempty
      (Σ certificate :
          ArticleInternalPairingFractionCertificate kinds source.elements
            (rootHeavyPathChildrenBottomUp
              snapshot before (Nat.le_refl n) key 0),
        { batches : ArticleRetainedPairingBatches snapshot before
            (Nat.le_refl n) key certificate.fraction.groups //
          certificate.fraction.groups = [] ∨
            ∃ firstAllocation :
                ArticleBatchDestinationAllocation .first batches state,
              certificate.RestoredTwoPhaseRichPassTrace batches params state
                sourceId source firstAllocation }) := by
  obtain ⟨certificate⟩ :=
    article_internalPairingFractionCertificate snapshot transcript key_lt_n
      rankZero source ownerEq unbroken sideSegment
  obtain ⟨batches⟩ :=
    certificate.exists_retainedPairingBatches transcript key_lt_n rankZero
  refine ⟨⟨certificate, ⟨batches, ?_⟩⟩⟩
  by_cases empty : certificate.fraction.groups = []
  · exact Or.inl empty
  · obtain ⟨firstAllocation, twoPhase⟩ :=
      certificate.exists_twoPhaseRichPassTrace batches represents sourceFound
        rfl sourceShrinking articleFraction empty
    exact Or.inr ⟨firstAllocation,
      twoPhase.with_loserRestoration represents sourceFound rfl
        sourceShrinking⟩

/-- Article Step 2 may isolate boundary children without unassigning them.
The exact useful witness is therefore an erase relation: deleting only
elements outside the source interval from its current attached side yields
the proper-ancestor projection.  Consecutiveness survives those deletions. -/
theorem article_internalPairingExecution_of_isolatedBoundaries
    {n key : ℕ} (snapshot : Snapshot n)
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    {params : Interface.Parameters} {state : Lazy.State n}
    (represents : state.Represents params snapshot before)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceShrinking : source.mode = .shrinking)
    (ownerEq : source.owner = valuePos ⟨key, key_lt_n⟩)
    (unbroken : canonicalBlockCrossSideUnbroken snapshot before source)
    (isolatedBoundaries : ∃ removed : List (Interface.Element n),
      (rootHeavyPathCanonicalChildOrder
          snapshot before key_lt_n rankZero).elements.filter
            (fun element => decide
              (canonicalSide snapshot before element = source.side)) =
        removed.foldl List.erase
          (state.view.attachedTopDown state.allElements
            source.owner source.side) ∧
      ∀ element ∈ removed, element ∉ source.elements)
    (articleFraction :
      10 * params.matchingNumerator ≤ params.matchingDenominator) :
    Nonempty
      (Σ certificate :
          ArticleInternalPairingFractionCertificate kinds source.elements
            (rootHeavyPathChildrenBottomUp
              snapshot before (Nat.le_refl n) key 0),
        { batches : ArticleRetainedPairingBatches snapshot before
            (Nat.le_refl n) key certificate.fraction.groups //
          certificate.fraction.groups = [] ∨
            ∃ firstAllocation :
                ArticleBatchDestinationAllocation .first batches state,
              certificate.RestoredTwoPhaseRichPassTrace batches params state
                sourceId source firstAllocation }) := by
  obtain ⟨removed, erasedEq, fresh⟩ := isolatedBoundaries
  apply article_internalPairingExecution snapshot transcript key_lt_n rankZero
    represents sourceFound sourceShrinking ownerEq unbroken
  · rw [erasedEq]
    exact
      (represents.valid.2 source (List.mem_of_getElem? sourceFound)).isSegment
        |>.foldl_erase_ambient_of_fresh fresh
  · exact articleFraction

/-- Article Steps 1--2 now discharge the formerly external geometry premise
of the internal pairing execution automatically for every non-boundary source
block of the accessed owner. -/
theorem article_internalPairingExecution_of_preparedCanonicalBoundaries
    {n : ℕ} (snapshot : Snapshot n)
    {before after : BST 0 n} (key : Fin n)
    {execution : SplayExecution key.val before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (rankZero : snapshot.rank (valuePos key) = 0)
    {params : Interface.Parameters} {state : Lazy.State n}
    (represents : state.Represents params snapshot before)
    {leftId rightId : Interface.BlockId}
    {leftBlock rightBlock : Lazy.Block n}
    (leftFound : state.blocks[leftId]? = some leftBlock)
    (leftElements :
      leftBlock.elements =
        [(WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
          snapshot before key).left])
    (rightFound : state.blocks[rightId]? = some rightBlock)
    (rightElements :
      rightBlock.elements =
        [(WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
          snapshot before key).right])
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceShrinking : source.mode = .shrinking)
    (ownerEq : source.owner = valuePos key)
    (sourceNeLeft : sourceId ≠ leftId)
    (sourceNeRight : sourceId ≠ rightId)
    (unbroken : canonicalBlockCrossSideUnbroken snapshot before source)
    (articleFraction :
      10 * params.matchingNumerator ≤ params.matchingDenominator) :
    Nonempty
      (Σ certificate :
          ArticleInternalPairingFractionCertificate kinds source.elements
            (rootHeavyPathChildrenBottomUp snapshot before
              (Nat.le_refl n) key.val 0),
        { batches : ArticleRetainedPairingBatches snapshot before
            (Nat.le_refl n) key.val certificate.fraction.groups //
          certificate.fraction.groups = [] ∨
            ∃ firstAllocation :
                ArticleBatchDestinationAllocation .first batches state,
              certificate.RestoredTwoPhaseRichPassTrace batches params state
                sourceId source firstAllocation }) := by
  have isolatedBoundaries :=
    exists_articleIsolatedBoundariesWitness snapshot before key rankZero
      represents leftFound leftElements rightFound rightElements sourceFound
      ownerEq sourceNeLeft sourceNeRight
  exact article_internalPairingExecution_of_isolatedBoundaries snapshot
    transcript key.isLt rankZero represents sourceFound sourceShrinking ownerEq
    unbroken isolatedBoundaries articleFraction

/-- The post-isolation geometric obligation can be stated as the exact
equality between the current attached side and the proper-ancestor child
projection.  Structural validity of the source then supplies the side segment
required above automatically. -/
theorem article_internalPairingExecution_of_isolatedAttachment
    {n key : ℕ} (snapshot : Snapshot n)
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    {params : Interface.Parameters} {state : Lazy.State n}
    (represents : state.Represents params snapshot before)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceShrinking : source.mode = .shrinking)
    (ownerEq : source.owner = valuePos ⟨key, key_lt_n⟩)
    (unbroken : canonicalBlockCrossSideUnbroken snapshot before source)
    (isolatedAttachment :
      state.view.attachedTopDown state.allElements source.owner source.side =
        (rootHeavyPathCanonicalChildOrder
          snapshot before key_lt_n rankZero).elements.filter
            (fun element => decide
              (canonicalSide snapshot before element = source.side)))
    (articleFraction :
      10 * params.matchingNumerator ≤ params.matchingDenominator) :
    Nonempty
      (Σ certificate :
          ArticleInternalPairingFractionCertificate kinds source.elements
            (rootHeavyPathChildrenBottomUp
              snapshot before (Nat.le_refl n) key 0),
        { batches : ArticleRetainedPairingBatches snapshot before
            (Nat.le_refl n) key certificate.fraction.groups //
          certificate.fraction.groups = [] ∨
            ∃ firstAllocation :
                ArticleBatchDestinationAllocation .first batches state,
              certificate.RestoredTwoPhaseRichPassTrace batches params state
                sourceId source firstAllocation }) := by
  apply article_internalPairingExecution snapshot transcript key_lt_n rankZero
    represents sourceFound sourceShrinking ownerEq unbroken
  · rw [← isolatedAttachment]
    exact represents.valid.2 source (List.mem_of_getElem? sourceFound) |>.isSegment
  · exact articleFraction

end Splay.Accounting
