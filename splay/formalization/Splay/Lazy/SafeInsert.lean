import Splay.Lazy.ValueTrace

namespace Splay.Lazy

private theorem State.eq_of_fields {n : ℕ} {first second : State n}
    (view : first.view = second.view)
    (blocks : first.blocks = second.blocks)
    (value : first.value = second.value) :
    first = second := by
  cases first
  cases second
  simp_all

namespace State

/-- Exact event sequence of the safe insertion macro, including the temporary
creator normalization and restoration of both original values. -/
def safeInsertEvents {n : ℕ} (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (element : Element n) : List (Event n) :=
  let creatorPrepared := state.adjustValue block.creator 1
  let insertPrepared := creatorPrepared.adjustValue element 2
  let inserted := insertPrepared.insert blockId element
  let elementRestored := inserted.adjustValue element (state.value element)
  state.adjustValueEvents block.creator 1 ++
    creatorPrepared.adjustValueEvents element 2 ++
    [.operation (.insert blockId element)] ++
    inserted.adjustValueEvents element (state.value element) ++
    elementRestored.adjustValueEvents block.creator (state.value block.creator)

/--
Every structurally legal insertion can satisfy the interface value-order
precondition by a finite value-change prefix and suffix.

The creator is temporarily set to `1` and the inserted element to `2`; after
the insertion both original values are restored.  Thus `valueBound ≥ 2` is
enough, independently of the two original values.
-/
theorem safeInsert_trace {n : ℕ}
    {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (element : Element n)
    (valid : state.Valid params)
    (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing)
    (unassigned : element ∉ state.allElements)
    (elementGap : 0 ≤ state.view.rawGap element)
    (afterSegment :
      IsSegment (block.inserted element).elements
        (state.view.attachedTopDown
          (state.insert blockId element).allElements
          block.owner block.side))
    (otherValid :
      ∀ id : Fin state.blocks.length, blockId ≠ id.val →
        (state.blocks.get id).StructurallyValid state.view
          (state.insert blockId element).allElements) :
    Trace params state (state.safeInsertEvents blockId block element) (state.insert blockId element) := by
  have blockMember : block ∈ state.blocks :=
    List.mem_iff_getElem?.2 ⟨blockId, found⟩
  have ownerCreator :
      block.owner = block.creator :=
    (valid.2 block blockMember).owner_eq_creator_of_growing growing
  have insertedMember :
      element ∈ (block.inserted element).elements := by
    simp [Block.inserted]
  have attachedMember :=
    afterSegment.mem insertedMember
  have topDownMember :=
    (state.view.mem_attachedTopDown_iff.mp attachedMember).1
  have parentOwner :=
    state.view.mem_topDown_parent topDownMember
  have parentCreator :
      state.view.parent element = some block.creator := by
    simpa [ownerCreator] using parentOwner
  have element_ne_creator : element ≠ block.creator := by
    intro equal
    subst element
    have levelLt := state.view.parent_level_lt parentCreator
    omega
  have creator_ne_element : block.creator ≠ element :=
    Ne.symm element_ne_creator

  let creatorPrepared := state.adjustValue block.creator 1
  let insertPrepared := creatorPrepared.adjustValue element 2
  let inserted := insertPrepared.insert blockId element
  let elementRestored :=
    inserted.adjustValue element (state.value element)
  let restored :=
    elementRestored.adjustValue block.creator
      (state.value block.creator)

  have creatorTrace :
      Trace params state
        (state.adjustValueEvents block.creator 1) creatorPrepared := by
    exact
      state.adjustValue_trace block.creator 1 valid (by omega)
        (by exact le_trans (by omega) params.valueBound_ge_two)
  have creatorPreparedValid : creatorPrepared.Valid params :=
    creatorTrace.final_valid
  have elementTrace :
      Trace params creatorPrepared
        (creatorPrepared.adjustValueEvents element 2)
        insertPrepared := by
    exact
      creatorPrepared.adjustValue_trace element 2
        creatorPreparedValid (by omega) params.valueBound_ge_two
  have insertPreparedValid : insertPrepared.Valid params :=
    elementTrace.final_valid
  have preparedFound :
      insertPrepared.blocks[blockId]? = some block := by
    simpa [insertPrepared, creatorPrepared] using found
  have preparedUnassigned :
      element ∉ insertPrepared.allElements := by
    simpa [State.allElements, insertPrepared, creatorPrepared] using
      unassigned
  have preparedGap :
      0 ≤ insertPrepared.view.rawGap element := by
    simpa [insertPrepared, creatorPrepared] using elementGap
  have preparedInsertBlocks :
      (insertPrepared.insert blockId element).blocks =
        (state.insert blockId element).blocks := by
    simp [State.insert, insertPrepared, creatorPrepared]
  have preparedInsertAllElements :
      (insertPrepared.insert blockId element).allElements =
        (state.insert blockId element).allElements := by
    unfold State.allElements
    rw [preparedInsertBlocks]
  have preparedSegment :
      IsSegment (block.inserted element).elements
        (insertPrepared.view.attachedTopDown
          (insertPrepared.insert blockId element).allElements
          block.owner block.side) := by
    rw [preparedInsertAllElements]
    simpa [insertPrepared, creatorPrepared] using afterSegment
  have preparedOtherValid :
      ∀ id : Fin insertPrepared.blocks.length,
        blockId ≠ id.val →
          (insertPrepared.blocks.get id).StructurallyValid
            insertPrepared.view
            (insertPrepared.insert blockId element).allElements := by
    intro id different
    let oldId : Fin state.blocks.length :=
      ⟨id.val, by
        simpa [insertPrepared, creatorPrepared] using id.isLt⟩
    have old := otherValid oldId different
    rw [preparedInsertAllElements]
    simpa [insertPrepared, creatorPrepared, oldId] using old
  have preparedValueOrder :
      insertPrepared.value block.creator + 1 ≤
        insertPrepared.value element := by
    have creatorOne :
        creatorPrepared.value block.creator = 1 := by
      exact adjustValue_value_self state block.creator 1 (by omega)
    have creatorStillOne :
        insertPrepared.value block.creator = 1 := by
      calc
        insertPrepared.value block.creator =
            creatorPrepared.value block.creator := by
          exact
            adjustValue_value_of_ne creatorPrepared
              creator_ne_element 2
        _ = 1 := creatorOne
    have elementTwo :
        insertPrepared.value element = 2 := by
      exact
        adjustValue_value_self creatorPrepared element 2 (by omega)
    omega
  have insertionStep :
      Step params insertPrepared
        (.operation (.insert blockId element)) inserted := by
    exact
      insertPrepared.insert_step blockId block element
        insertPreparedValid preparedFound growing preparedUnassigned
        preparedValueOrder preparedGap preparedSegment preparedOtherValid
  have insertionTrace :
      Trace params insertPrepared
        [.operation (.insert blockId element)] inserted :=
    Trace.singleton insertionStep
  have insertedValid : inserted.Valid params :=
    insertionStep.after_valid

  have originalElementBounds :=
    valid.toInterface.2.1 element
  have restoreElementTrace :
      Trace params inserted
        (inserted.adjustValueEvents element (state.value element))
        elementRestored := by
    exact
      inserted.adjustValue_trace element (state.value element)
        insertedValid originalElementBounds.1 originalElementBounds.2
  have elementRestoredValid : elementRestored.Valid params :=
    restoreElementTrace.final_valid
  have originalCreatorBounds :=
    valid.toInterface.2.1 block.creator
  have restoreCreatorTrace :
      Trace params elementRestored
        (elementRestored.adjustValueEvents
          block.creator (state.value block.creator))
        restored := by
    exact
      elementRestored.adjustValue_trace block.creator
        (state.value block.creator) elementRestoredValid
        originalCreatorBounds.1 originalCreatorBounds.2

  have restored_eq : restored = state.insert blockId element := by
    apply State.eq_of_fields
    · simp [restored, elementRestored, inserted, insertPrepared,
        creatorPrepared, State.insert]
    · simp [restored, elementRestored, inserted, insertPrepared,
        creatorPrepared, State.insert]
    · funext queried
      by_cases queriedCreator : queried = block.creator
      · subst queried
        rw [show restored.value block.creator =
          state.value block.creator by
            exact adjustValue_value_self elementRestored block.creator
              (state.value block.creator) originalCreatorBounds.1]
        rfl
      · by_cases queriedElement : queried = element
        · subst queried
          have restoredElement :
              restored.value element = elementRestored.value element := by
            exact
              adjustValue_value_of_ne elementRestored
                element_ne_creator (state.value block.creator)
          rw [restoredElement]
          exact
            adjustValue_value_self inserted element
              (state.value element) originalElementBounds.1
        · have restoredOther :
              restored.value queried = elementRestored.value queried := by
            exact
              adjustValue_value_of_ne elementRestored
                queriedCreator (state.value block.creator)
          rw [restoredOther]
          have elementRestoredOther :
              elementRestored.value queried = inserted.value queried := by
            exact
              adjustValue_value_of_ne inserted
                queriedElement (state.value element)
          rw [elementRestoredOther]
          change insertPrepared.value queried = state.value queried
          have afterElement :
              insertPrepared.value queried =
                creatorPrepared.value queried := by
            exact
              adjustValue_value_of_ne creatorPrepared
                queriedElement 2
          rw [afterElement]
          exact adjustValue_value_of_ne state queriedCreator 1

  let events :=
    state.adjustValueEvents block.creator 1 ++
      creatorPrepared.adjustValueEvents element 2 ++
      [.operation (.insert blockId element)] ++
      inserted.adjustValueEvents element (state.value element) ++
      elementRestored.adjustValueEvents
        block.creator (state.value block.creator)
  have completeTrace :=
    creatorTrace.append
      (elementTrace.append
        (insertionTrace.append
          (restoreElementTrace.append restoreCreatorTrace)))
  simpa [safeInsertEvents, events, creatorPrepared, insertPrepared, inserted, elementRestored,
    List.append_assoc, restored_eq] using completeTrace

/-- Compatibility form of the exact safe insertion trace. -/
theorem exists_safeInsert_trace {n : ℕ}
    {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (element : Element n)
    (valid : state.Valid params)
    (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing)
    (unassigned : element ∉ state.allElements)
    (elementGap : 0 ≤ state.view.rawGap element)
    (afterSegment :
      IsSegment (block.inserted element).elements
        (state.view.attachedTopDown
          (state.insert blockId element).allElements
          block.owner block.side))
    (otherValid :
      ∀ id : Fin state.blocks.length, blockId ≠ id.val →
        (state.blocks.get id).StructurallyValid state.view
          (state.insert blockId element).allElements) :
    ∃ events : List (Event n),
      Trace params state events (state.insert blockId element) := by
  exact ⟨state.safeInsertEvents blockId block element,
    state.safeInsert_trace blockId block element valid found growing unassigned
      elementGap afterSegment otherValid⟩

end State

end Splay.Lazy
