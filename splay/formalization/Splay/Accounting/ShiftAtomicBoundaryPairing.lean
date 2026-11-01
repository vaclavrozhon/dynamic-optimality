import Splay.Accounting.PairingEventAlignment
import Splay.Lazy.ComparisonRootSwapComplete

namespace Splay.Accounting

open Splay.Rank
open Splay.Tree.BST
open Splay.Lazy
open Splay.Lazy.Canonical

namespace ShiftAtomicBoundaryPairing

private theorem singleton_isSegment_of_mem
    {α : Type*} {element : α} {whole : List α}
    (member : element ∈ whole) :
    IsSegment [element] whole := by
  rw [List.mem_iff_append] at member
  obtain ⟨front, back, rfl⟩ := member
  exact ⟨front, back, by simp⟩

/--
The structural half of safe insertion with the value-order premise exposed.

The existing `exists_safeInsert_trace_of_emptyGrowing` also manufactures
value changes.  The pairing macro needs the insertion event at a literal
known position, so this specialization proves the one visible insertion step
after the caller has prepared the values explicitly.
-/
theorem insert_step_of_emptyGrowing
    {n : ℕ} {params : Interface.Parameters} {state : State n}
    (atomic : state.ShiftAtomic)
    (valid : state.Valid params)
    (blockId : Interface.BlockId) (block : Block n)
    (element : Element n)
    (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing)
    (empty : block.elements = [])
    (unassigned : element ∉ state.allElements)
    (parent : state.view.parent element = some block.owner)
    (side : state.view.side element = block.side)
    (valueOrder :
      state.value block.creator + 1 ≤ state.value element)
    (elementGap : 0 ≤ state.view.rawGap element) :
    Step params state (.operation (.insert blockId element))
      (state.insert blockId element) := by
  have blockMember : block ∈ state.blocks :=
    List.mem_iff_getElem?.2 ⟨blockId, found⟩
  have afterAssigned :
      element ∈ (state.insert blockId element).allElements := by
    rw [Canonical.mem_insert_allElements_iff
      state blockId block element element found]
    exact Or.inl rfl
  have topDownMember :
      element ∈ state.view.topDown block.owner block.side :=
    state.view.mem_topDown_iff.mpr ⟨parent, side⟩
  have attachedMember :
      element ∈
        state.view.attachedTopDown
          (state.insert blockId element).allElements
          block.owner block.side :=
    state.view.mem_attachedTopDown_iff.mpr
      ⟨topDownMember, afterAssigned⟩
  have afterSegment :
      IsSegment (block.inserted element).elements
        (state.view.attachedTopDown
          (state.insert blockId element).allElements
          block.owner block.side) := by
    rw [show (block.inserted element).elements = [element] by
      simp [Block.inserted, empty]]
    exact singleton_isSegment_of_mem attachedMember
  have otherValid :
      ∀ id : Fin state.blocks.length, blockId ≠ id.val →
        (state.blocks.get id).StructurallyValid state.view
          (state.insert blockId element).allElements := by
    intro id _different
    let other := state.blocks.get id
    have otherMember : other ∈ state.blocks :=
      List.get_mem state.blocks id
    have oldStructural :
        other.StructurallyValid state.view state.allElements :=
      valid.2 other otherMember
    rcases atomic other otherMember with growingCase | shrinkingCase
    · exact
        ⟨by rw [growingCase.2]; exact IsSegment.nil _,
          oldStructural.2⟩
    · rcases shrinkingCase.2 with otherEmpty |
        ⟨otherElement, elementsEq⟩
      · exact
          ⟨by rw [otherEmpty]; exact IsSegment.nil _,
            oldStructural.2⟩
      · have oldAssigned : otherElement ∈ state.allElements :=
          State.mem_allElements_iff.mpr
            ⟨other, otherMember, by simp [elementsEq]⟩
        have newAssigned :
            otherElement ∈
              (state.insert blockId element).allElements := by
          rw [Canonical.mem_insert_allElements_iff
            state blockId block element otherElement found]
          exact Or.inr oldAssigned
        have oldTopDown :
            otherElement ∈
              state.view.topDown other.owner other.side :=
          state.view.mem_topDown_iff.mpr
            ⟨oldStructural.parent_eq (by simp [elementsEq]),
              oldStructural.side_eq (by simp [elementsEq])⟩
        have newAttached :
            otherElement ∈
              state.view.attachedTopDown
                (state.insert blockId element).allElements
                other.owner other.side :=
          state.view.mem_attachedTopDown_iff.mpr
            ⟨oldTopDown, newAssigned⟩
        refine ⟨?_, oldStructural.2⟩
        rw [elementsEq]
        exact singleton_isSegment_of_mem newAttached
  exact
    state.insert_step blockId block element valid found growing
      unassigned valueOrder elementGap afterSegment otherValid

/-- Every value of a stable shift-atomic state is exactly one. -/
theorem value_eq_one
    {n : ℕ} {params : Interface.Parameters} {state : State n}
    (atomic : state.ShiftAtomic)
    (stable : state.Stable params)
    (element : Element n) :
    state.value element = 1 := by
  by_cases root : element = state.view.root
  · subst element
    exact stable.2.2.2.2.2.1
  · have parent :
        state.view.parent element ≠ none :=
      state.view.parent_ne_none_of_ne_root root
    have assigned : element ∈ state.allElements :=
      (stable.2.1 element).2 parent
    exact atomic.value_eq_one_of_mem stable assigned

/--
One fully concrete boundary-pairing transition.

The loser starts in its shift-atomic shrinking singleton.  It is visibly
deleted, the remaining atomic block list is silently rebased to the target
canonical heap view, and the loser is visibly inserted into the empty growing
block of its new winner.  The explicit increase/decrease pair satisfies the
interface value order while restoring value one.  Finally the destination is
converted and replaced, restoring shift atomicity before the checked
value-normalization suffix.

The two visible pairing events occur at rich-event indices `0` and `3`, and
at erased-operation indices `0` and `2`.
-/
structure Certificate
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {beforeTree afterTree : BST 0 n}
    (initial : State n)
    (slot : PairingSlot)
    (winner loser : Element n) where
  transition :
    RepresentedTransition params
      snapshot beforeTree snapshot afterTree initial
  finalAtomic : transition.final.ShiftAtomic
  move : BoundaryPairingMove transition.trace
  move_slot : move.slot = slot
  move_winner : move.winner = winner
  move_loser : move.loser = loser
  delete_event_index : move.deleteEventIndex = 0
  insert_event_index : move.insertEventIndex = 3
  delete_operation_index : move.deleteOperationIndex = 0
  insert_operation_index : move.insertOperationIndex = 2
  events_eq :
    transition.events =
      [.operation (.delete move.source loser),
        .silent,
        .operation (.valueChange loser .increase),
        .operation (.insert move.destination loser),
        .operation (.valueChange loser .decrease),
        .operation (.convert move.destination),
        .operation (.create move.destinationBlock.creator)]

/--
Construct a concrete boundary pairing for any endpoint that has the supplied
winner as parent in the target canonical heap.
-/
theorem exists_certificate
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {beforeTree afterTree : BST 0 n}
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree)
    (initialAtomic : initial.ShiftAtomic)
    (slot : PairingSlot)
    (winner loser : Element n)
    (afterParent :
      canonicalParent snapshot afterTree loser = some winner) :
    Nonempty
      (Certificate (params := params) (snapshot := snapshot)
        (beforeTree := beforeTree) (afterTree := afterTree)
        initial slot winner loser) := by
  let afterView := canonicalHeapView snapshot afterTree
  have afterOrdered : afterView.HeapOrdered :=
    canonicalHeapView_heapOrdered snapshot afterTree
  have rootEq :
      afterView.root = initial.view.root := by
    change canonicalRoot snapshot afterTree = initial.view.root
    rw [initialRepresents.view_eq]
    exact canonicalRoot_eq snapshot afterTree beforeTree
  have afterParentView :
      afterView.parent loser = some winner :=
    afterParent
  have loserNotRootAfter : loser ≠ afterView.root := by
    intro equal
    subst loser
    rw [afterView.root_parent] at afterParentView
    contradiction
  have loserNotRootBefore : loser ≠ initial.view.root := by
    intro equal
    apply loserNotRootAfter
    exact equal.trans rootEq.symm
  have loserAssigned : loser ∈ initial.allElements := by
    exact
      (initialRepresents.complete loser).2
        (initial.view.parent_ne_none_of_ne_root loserNotRootBefore)
  obtain ⟨sourceBlock, sourceMember, loserMember⟩ :=
    State.mem_allElements_iff.mp loserAssigned
  have sourceShape := initialAtomic sourceBlock sourceMember
  have sourceShrinking : sourceBlock.mode = .shrinking := by
    rcases sourceShape with growing | shrinking
    · rw [growing.2] at loserMember
      simp at loserMember
    · exact shrinking.1
  have sourceSingleton : sourceBlock.elements = [loser] := by
    rcases sourceShape with growing | shrinking
    · rw [growing.2] at loserMember
      simp at loserMember
    · rcases shrinking.2 with empty | ⟨singleton, elementsEq⟩
      · rw [empty] at loserMember
        simp at loserMember
      · have equal : loser = singleton := by
          simpa [elementsEq] using loserMember
        simpa [equal] using elementsEq
  obtain ⟨sourceId, sourceFound⟩ :=
    List.mem_iff_getElem?.mp sourceMember
  let detached := initial.delete sourceId loser 0
  have deleteTrace :
      Trace params initial
        [.operation (.delete sourceId loser)] detached := by
    exact
      initialAtomic.deleteSingleton_trace initialRepresents.stable
        sourceId sourceBlock loser sourceFound sourceShrinking
        sourceSingleton
  have deleteStep :
      Step params initial (.operation (.delete sourceId loser))
        detached := by
    cases deleteTrace with
    | cons head tail =>
        cases tail
        exact head
  have detachedValid : detached.Valid params :=
    deleteTrace.final_valid
  have detachedAtomic : detached.ShiftAtomic := by
    exact
      initialAtomic.deleteSingleton sourceId sourceBlock loser 0
        sourceFound sourceShrinking sourceSingleton
  have detachedRootNotMem :
      afterView.root ∉ detached.allElements := by
    intro assigned
    have beforeAndDifferent :=
      (State.mem_deleteSingleton_allElements_iff
        sourceId sourceBlock loser afterView.root 0 sourceFound
        sourceSingleton initialRepresents.valid.allElements_nodup).mp
        assigned
    apply initialRepresents.valid.root_not_mem
    simpa only [rootEq] using beforeAndDifferent.1
  let rebased := detached.rebaseShiftAtomic afterView
  have rebasedValid : rebased.Valid params := by
    exact
      detachedAtomic.rebase_valid_of_root_not_mem
        detachedValid detachedRootNotMem
  have rebaseStep :
      Step params detached .silent rebased := by
    exact
      Step.silent detachedValid rebasedValid
        (detached.rebaseShiftAtomic_toInterface afterView).symm
  have rebasedAtomic : rebased.ShiftAtomic :=
    detachedAtomic.rebase afterView
  have detachedOneGrowing : detached.OneGrowingPerSide := by
    exact
      initialRepresents.stable.2.2.2.1.delete sourceId loser 0
  have rebasedOneGrowing : rebased.OneGrowingPerSide := by
    exact
      State.ShiftAtomic.rebase_oneGrowingPerSide
        afterView detachedOneGrowing
  obtain ⟨destinationId, destinationProperty, _destinationUnique⟩ :=
    rebasedOneGrowing winner (afterView.side loser)
  let destinationBlock := rebased.blocks.get destinationId
  have destinationMode : destinationBlock.mode = .growing :=
    destinationProperty.1
  have destinationOwner : destinationBlock.owner = winner :=
    destinationProperty.2.1
  have destinationSide :
      destinationBlock.side = afterView.side loser :=
    destinationProperty.2.2
  have destinationFound :
      rebased.blocks[destinationId.val]? = some destinationBlock := by
    apply List.getElem?_eq_some_iff.mpr
    exact
      ⟨destinationId.isLt, by
        simp [destinationBlock, List.get_eq_getElem]⟩
  have destinationMember : destinationBlock ∈ rebased.blocks :=
    List.get_mem rebased.blocks destinationId
  have destinationEmpty : destinationBlock.elements = [] := by
    rcases rebasedAtomic destinationBlock destinationMember with
        growing | shrinking
    · exact growing.2
    · rw [destinationMode] at shrinking
      simp at shrinking
  have destinationStructural :
      destinationBlock.StructurallyValid
        rebased.view rebased.allElements :=
    rebasedValid.2 destinationBlock destinationMember
  have destinationCreator :
      destinationBlock.creator = winner := by
    exact
      (destinationStructural.owner_eq_creator_of_growing
        destinationMode).symm.trans destinationOwner
  have loserUnassigned : loser ∉ rebased.allElements := by
    rw [show rebased.allElements = detached.allElements by
      exact State.rebaseShiftAtomic_allElements detached afterView]
    intro assigned
    exact
      ((State.mem_deleteSingleton_allElements_iff
        sourceId sourceBlock loser loser 0 sourceFound
        sourceSingleton initialRepresents.valid.allElements_nodup).mp
        assigned).2 rfl
  have rebasedParent :
      rebased.view.parent loser = some destinationBlock.owner := by
    change afterView.parent loser = some destinationBlock.owner
    change canonicalParent snapshot afterTree loser =
      some destinationBlock.owner
    rw [afterParent, destinationOwner]
  have rebasedSide :
      rebased.view.side loser = destinationBlock.side := by
    change afterView.side loser = destinationBlock.side
    exact destinationSide.symm
  have loserGap : 0 ≤ rebased.view.rawGap loser := by
    change 0 ≤ afterView.rawGap loser
    exact le_of_lt
      (afterView.rawGap_pos_of_heapOrdered afterOrdered afterParent)
  have loserValueOne : rebased.value loser = 1 := by
    change initial.value loser = 1
    exact value_eq_one initialAtomic initialRepresents.stable loser
  have winnerValueOne : rebased.value winner = 1 := by
    change initial.value winner = 1
    exact value_eq_one initialAtomic initialRepresents.stable winner
  have winnerNeLoser : winner ≠ loser := by
    intro equal
    have levels := afterView.parent_level_lt afterParentView
    have levelEq :
        afterView.level winner = afterView.level loser :=
      congrArg afterView.level equal
    omega
  let prepared := rebased.increaseValue loser
  have canIncrease :
      rebased.value loser < params.valueBound := by
    rw [loserValueOne]
    exact params.valueBound_ge_two
  have increaseStep :
      Step params rebased
        (.operation (.valueChange loser .increase)) prepared := by
    exact rebased.increaseValue_step loser rebasedValid canIncrease
  have preparedValid : prepared.Valid params :=
    increaseStep.after_valid
  have preparedAtomic : prepared.ShiftAtomic := by
    change rebased.ShiftAtomic
    exact rebasedAtomic
  have preparedFound :
      prepared.blocks[destinationId.val]? =
        some destinationBlock := by
    simpa [prepared, State.increaseValue] using destinationFound
  have preparedUnassigned : loser ∉ prepared.allElements := by
    simpa [prepared, State.increaseValue, State.allElements] using
      loserUnassigned
  have preparedParent :
      prepared.view.parent loser = some destinationBlock.owner := by
    simpa [prepared, State.increaseValue] using rebasedParent
  have preparedSide :
      prepared.view.side loser = destinationBlock.side := by
    simpa [prepared, State.increaseValue] using rebasedSide
  have preparedGap :
      0 ≤ prepared.view.rawGap loser := by
    simpa [prepared, State.increaseValue] using loserGap
  have preparedLoserValue : prepared.value loser = 2 := by
    simp [prepared, State.increaseValue, loserValueOne]
  have preparedWinnerValue : prepared.value winner = 1 := by
    simp [prepared, State.increaseValue, winnerNeLoser,
      winnerValueOne]
  have preparedValueOrder :
      prepared.value destinationBlock.creator + 1 ≤
        prepared.value loser := by
    rw [destinationCreator, preparedWinnerValue,
      preparedLoserValue]
  let inserted := prepared.insert destinationId.val loser
  have insertStep :
      Step params prepared
        (.operation (.insert destinationId.val loser)) inserted := by
    exact
      insert_step_of_emptyGrowing
        preparedAtomic preparedValid destinationId.val
        destinationBlock loser preparedFound destinationMode
        destinationEmpty preparedUnassigned preparedParent preparedSide
        preparedValueOrder preparedGap
  have insertedValid : inserted.Valid params :=
    insertStep.after_valid
  have insertedLoserValue : inserted.value loser = 2 := by
    exact preparedLoserValue
  let restored := inserted.decreaseValue loser
  have decreaseStep :
      Step params inserted
        (.operation (.valueChange loser .decrease)) restored := by
    exact
      inserted.decreaseValue_step loser insertedValid (by
        rw [insertedLoserValue]
        omega)
  have restoredValid : restored.Valid params :=
    decreaseStep.after_valid
  let insertedBlock := destinationBlock.inserted loser
  have insertedFound :
      restored.blocks[destinationId.val]? = some insertedBlock := by
    apply List.getElem?_eq_some_iff.mpr
    refine ⟨by simp [restored, inserted, prepared, State.decreaseValue,
      State.insert, State.increaseValue], ?_⟩
    change
      (rebased.blocks.modify destinationId.val
        (fun current => current.inserted loser))[destinationId.val] =
          insertedBlock
    rw [List.getElem_modify, if_pos rfl]
    have selected :
        rebased.blocks[destinationId.val] = destinationBlock := by
      simp [destinationBlock, List.get_eq_getElem]
    rw [selected]
  have insertedMode : insertedBlock.mode = .growing := by
    simp [insertedBlock, Block.inserted, destinationMode]
  have insertedGapValid :
      (insertedBlock.converted
        (afterView.rawGap loser)).GapValid restored.view := by
    simp [Block.GapValid, Block.converted, insertedBlock,
      Block.inserted, destinationEmpty, restored, inserted,
      prepared, State.decreaseValue, State.insert,
      State.increaseValue]
    change
      Analysis.IsIntervalGap {loser} afterView.rawGap
        (afterView.rawGap loser)
    simp [Analysis.IsIntervalGap]
  let structural :=
    (restored.convert destinationId.val (afterView.rawGap loser)).create
      insertedBlock.creator insertedBlock.side
  have structuralTrace :
      Trace params restored
        [.operation (.convert destinationId.val),
          .operation (.create insertedBlock.creator)]
        structural := by
    exact
      restored.convertAndCreate_trace
        destinationId.val insertedBlock (afterView.rawGap loser)
        restoredValid insertedFound insertedMode insertedGapValid
  have structuralValid : structural.Valid params :=
    structuralTrace.final_valid
  have structuralAtomic : structural.ShiftAtomic := by
    change
      (((rebased.insert destinationId.val loser).convert
          destinationId.val (afterView.rawGap loser)).create
        destinationBlock.creator destinationBlock.side).ShiftAtomic
    exact
      rebasedAtomic.insertConvertCreate
        destinationId.val destinationBlock loser
          (afterView.rawGap loser) destinationFound destinationMode
          destinationEmpty
  have preparedOneGrowing : prepared.OneGrowingPerSide := by
    change rebased.OneGrowingPerSide
    exact rebasedOneGrowing
  have insertedOneGrowing : inserted.OneGrowingPerSide := by
    exact preparedOneGrowing.insert destinationId.val loser
  have restoredOneGrowing : restored.OneGrowingPerSide := by
    change inserted.OneGrowingPerSide
    exact insertedOneGrowing
  have structuralOneGrowing : structural.OneGrowingPerSide := by
    exact
      restoredOneGrowing.convertAndCreate restoredValid
        destinationId.val insertedBlock (afterView.rawGap loser)
        insertedFound insertedMode
  have structuralView : structural.view = afterView := by
    rfl
  have structuralComplete : structural.Complete := by
    intro queried
    have structuralElements :
        structural.allElements = inserted.allElements := by
      calc
        structural.allElements = restored.allElements := by
          simp [structural]
        _ = inserted.allElements := rfl
    rw [structuralElements]
    rw [Canonical.mem_insert_allElements_iff
      prepared destinationId.val destinationBlock loser queried
      preparedFound]
    have preparedElements :
        prepared.allElements = detached.allElements := by
      calc
        prepared.allElements = rebased.allElements := rfl
        _ = detached.allElements :=
          State.rebaseShiftAtomic_allElements detached afterView
    rw [preparedElements]
    rw [State.mem_deleteSingleton_allElements_iff
      sourceId sourceBlock loser queried 0 sourceFound
      sourceSingleton initialRepresents.valid.allElements_nodup]
    constructor
    · rintro (queriedLoser | ⟨_beforeAssigned, queriedNeLoser⟩)
      · subst queried
        change afterView.parent loser ≠ none
        rw [afterParentView]
        simp
      · exact afterView.parent_ne_none_of_ne_root (by
          intro queriedRoot
          have rootAssigned :
              initial.view.root ∈ initial.allElements := by
            simpa only [queriedRoot, rootEq] using _beforeAssigned
          exact
            initialRepresents.valid.root_not_mem rootAssigned)
    · intro afterParentNe
      have queriedNotRoot : queried ≠ afterView.root := by
        intro queriedRoot
        subst queried
        exact afterParentNe afterView.root_parent
      by_cases queriedLoser : queried = loser
      · exact Or.inl queriedLoser
      · refine Or.inr ⟨?_, queriedLoser⟩
        apply
          (initialRepresents.complete queried).2
        exact
          initial.view.parent_ne_none_of_ne_root
            (fun queriedInitialRoot =>
              queriedNotRoot (queriedInitialRoot.trans rootEq.symm))
  have structuralRootValue :
      structural.value structural.view.root = 1 := by
    change
      (inserted.decreaseValue loser).value afterView.root = 1
    simp [inserted, prepared, State.insert, State.decreaseValue,
      State.increaseValue]
    change initial.value afterView.root = 1
    rw [rootEq]
    exact initialRepresents.stable.2.2.2.2.2.1
  have structuralValueOne :
      ∀ queried, structural.value queried = 1 := by
    intro queried
    change (inserted.decreaseValue loser).value queried = 1
    by_cases queriedLoser : queried = loser
    · subst queried
      simp [inserted, prepared, rebased, detached,
        State.insert, State.decreaseValue, State.increaseValue,
        State.rebaseShiftAtomic, State.delete]
      exact
        value_eq_one initialAtomic initialRepresents.stable loser
    · simp [inserted, prepared, rebased, detached,
        State.insert, State.decreaseValue, State.increaseValue,
        State.rebaseShiftAtomic, State.delete, queriedLoser]
      exact
        value_eq_one initialAtomic initialRepresents.stable queried
  have structuralGrowingTopmost : structural.GrowingTopmost := by
    intro id
    dsimp only
    intro growingMode
    have blockMember :
        structural.blocks.get id ∈ structural.blocks :=
      List.get_mem _ id
    rcases structuralAtomic (structural.blocks.get id) blockMember with
        growingCase | shrinkingCase
    · refine
        ⟨structural.view.topDown
            (structural.blocks.get id).owner
            (structural.blocks.get id).side, ?_⟩
      rw [growingCase.2]
      simp
    · rw [growingMode] at shrinkingCase
      simp at shrinkingCase
  have structuralValues : structural.ValuesRealizeGaps := by
    exact
      State.valuesRealizeGaps_of_shiftAtomic_of_values_eq_one
        structuralAtomic structuralValid structuralRootValue
        (fun queried _member => structuralValueOne queried)
  have structuralPrepared : structural.RankPrepared params :=
    ⟨structuralValid, structuralComplete, structuralOneGrowing,
      structuralGrowingTopmost, structuralValues⟩
  have structuralStable : structural.Stable params := by
    exact structuralPrepared.stable (by
      rw [structuralView]
      exact afterOrdered)
  have structuralRepresents :
      structural.Represents params snapshot afterTree := by
    exact ⟨structuralStable, structuralView⟩
  have tailAfterInsert :
      Trace params inserted
        [.operation (.valueChange loser .decrease),
          .operation (.convert destinationId.val),
          .operation (.create insertedBlock.creator)]
        structural := by
    exact
      (Trace.singleton decreaseStep).append
        structuralTrace
  have tailAtInsert :
      Trace params prepared
        (.operation (.insert destinationId.val loser) ::
          [.operation (.valueChange loser .decrease),
            .operation (.convert destinationId.val),
            .operation (.create insertedBlock.creator)])
        structural :=
    Trace.cons insertStep tailAfterInsert
  have tailAtIncrease :
      Trace params rebased
        (.operation (.valueChange loser .increase) ::
          .operation (.insert destinationId.val loser) ::
          [.operation (.valueChange loser .decrease),
            .operation (.convert destinationId.val),
            .operation (.create insertedBlock.creator)])
        structural :=
    Trace.cons increaseStep tailAtInsert
  have tailAtRebase :
      Trace params detached
        (.silent ::
          .operation (.valueChange loser .increase) ::
          .operation (.insert destinationId.val loser) ::
          [.operation (.valueChange loser .decrease),
            .operation (.convert destinationId.val),
            .operation (.create insertedBlock.creator)])
        structural :=
    Trace.cons rebaseStep tailAtIncrease
  have fullTrace :
      Trace params initial
        (.operation (.delete sourceId loser) ::
          .silent ::
          .operation (.valueChange loser .increase) ::
          .operation (.insert destinationId.val loser) ::
          [.operation (.valueChange loser .decrease),
            .operation (.convert destinationId.val),
            .operation (.create insertedBlock.creator)])
        structural :=
    Trace.cons deleteStep tailAtRebase
  let transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial := {
    initial_represents := initialRepresents
    final := structural
    events :=
      .operation (.delete sourceId loser) ::
        .silent ::
        .operation (.valueChange loser .increase) ::
        .operation (.insert destinationId.val loser) ::
        [.operation (.valueChange loser .decrease),
          .operation (.convert destinationId.val),
          .operation (.create insertedBlock.creator)]
    trace := fullTrace
    final_represents := structuralRepresents
  }
  have deleteAt :
      Trace.VisibleStepAt transition.trace 0 0 initial
        (.delete sourceId loser) detached := by
    exact .head deleteStep tailAtRebase
  have insertLocal :
      Trace.VisibleStepAt tailAtInsert 0 0 prepared
        (.insert destinationId.val loser) inserted :=
    .head insertStep tailAfterInsert
  have insertAfterIncrease :
      Trace.VisibleStepAt tailAtIncrease 1 1 prepared
        (.insert destinationId.val loser) inserted :=
    .visibleTail increaseStep tailAtInsert insertLocal
  have insertAfterRebase :
      Trace.VisibleStepAt tailAtRebase 1 2 prepared
        (.insert destinationId.val loser) inserted :=
    .silentTail rebaseStep tailAtIncrease insertAfterIncrease
  have insertAt :
      Trace.VisibleStepAt transition.trace 2 3 prepared
        (.insert destinationId.val loser) inserted :=
    .visibleTail deleteStep tailAtRebase insertAfterRebase
  have destinationFoundInterface :
      prepared.toInterface.block? destinationId.val =
        some destinationBlock.toInterface := by
    unfold Interface.State.block? State.toInterface
    rw [List.getElem?_map, preparedFound]
    rfl
  let move : BoundaryPairingMove transition.trace := {
    slot := slot
    winner := winner
    loser := loser
    source := sourceId
    deleteOperationIndex := 0
    deleteEventIndex := 0
    deleteBefore := initial
    deleteAfter := detached
    deleteAt := deleteAt
    destination := destinationId.val
    insertOperationIndex := 2
    insertEventIndex := 3
    insertBefore := prepared
    insertAfter := inserted
    insertAt := insertAt
    delete_before_insert := by omega
    destinationBlock := destinationBlock.toInterface
    destinationFound := destinationFoundInterface
    destinationCreator := by
      exact destinationCreator
  }
  exact
    ⟨{
      transition := transition
      finalAtomic := structuralAtomic
      move := move
      move_slot := rfl
      move_winner := rfl
      move_loser := rfl
      delete_event_index := rfl
      insert_event_index := rfl
      delete_operation_index := rfl
      insert_operation_index := rfl
      events_eq := rfl
    }⟩

end ShiftAtomicBoundaryPairing

end Splay.Accounting
