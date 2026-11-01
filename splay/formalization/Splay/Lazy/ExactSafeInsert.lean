import Splay.Lazy.CanonicalInitializationTrace
import Splay.Lazy.ShiftAtomicizationComplete

namespace Splay.Lazy

private theorem singleton_isSegment_of_mem
    {α : Type*} {element : α} {whole : List α}
    (member : element ∈ whole) :
    IsSegment [element] whole := by
  rw [List.mem_iff_append] at member
  obtain ⟨front, back, rfl⟩ := member
  exact ⟨front, back, by simp⟩

namespace State

/--
The three-operation specialization of `exists_safeInsert_trace`.

When an empty growing destination, its creator, and the new element all
start at value one, no general value-normalization macro is needed: raise the
new element once, insert it, and immediately lower it again.  The endpoint
therefore has exactly the original value function and exactly two productive
operations (`increase` and `insert`).
-/
theorem ShiftAtomic.oneIncreaseInsertDecrease_trace_of_emptyGrowing
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
    (elementGap : 0 ≤ state.view.rawGap element)
    (creatorOne : state.value block.creator = 1)
    (elementOne : state.value element = 1) :
    Trace params state
      [.operation (.valueChange element .increase),
        .operation (.insert blockId element),
        .operation (.valueChange element .decrease)]
      (state.insert blockId element) := by
  have blockMember : block ∈ state.blocks :=
    List.mem_iff_getElem?.2 ⟨blockId, found⟩
  have ownerCreator :
      block.owner = block.creator :=
    (valid.2 block blockMember).owner_eq_creator_of_growing growing
  have parentCreator :
      state.view.parent element = some block.creator := by
    simpa [ownerCreator] using parent
  have element_ne_creator : element ≠ block.creator := by
    intro equal
    subst element
    have levelLt := state.view.parent_level_lt parentCreator
    omega
  have creator_ne_element : block.creator ≠ element :=
    Ne.symm element_ne_creator

  let raised := state.increaseValue element
  have canIncrease : state.value element < params.valueBound := by
    rw [elementOne]
    exact params.valueBound_ge_two
  have raiseStep :
      Step params state
        (.operation (.valueChange element .increase)) raised :=
    state.increaseValue_step element valid canIncrease
  have raisedValid : raised.Valid params :=
    raiseStep.after_valid

  have afterAssigned :
      element ∈ (raised.insert blockId element).allElements := by
    rw [Canonical.mem_insert_allElements_iff
      raised blockId block element element (by
        simpa [raised, State.increaseValue] using found)]
    exact Or.inl rfl
  have topDownMember :
      element ∈ state.view.topDown block.owner block.side :=
    state.view.mem_topDown_iff.mpr ⟨parent, side⟩
  have attachedMember :
      element ∈
        raised.view.attachedTopDown
          (raised.insert blockId element).allElements
          block.owner block.side := by
    apply raised.view.mem_attachedTopDown_iff.mpr
    constructor
    · simpa [raised, State.increaseValue] using topDownMember
    · exact afterAssigned
  have afterSegment :
      IsSegment (block.inserted element).elements
        (raised.view.attachedTopDown
          (raised.insert blockId element).allElements
          block.owner block.side) := by
    rw [show (block.inserted element).elements = [element] by
      simp [Block.inserted, empty]]
    exact singleton_isSegment_of_mem attachedMember
  have otherValid :
      ∀ id : Fin raised.blocks.length, blockId ≠ id.val →
        (raised.blocks.get id).StructurallyValid raised.view
          (raised.insert blockId element).allElements := by
    intro id _different
    let oldId : Fin state.blocks.length :=
      ⟨id.val, by
        have idLt : id.val < raised.blocks.length := id.isLt
        simpa [raised, State.increaseValue] using idLt⟩
    let other := state.blocks.get oldId
    have otherMember : other ∈ state.blocks :=
      List.get_mem state.blocks oldId
    have oldStructural :
        other.StructurallyValid state.view state.allElements :=
      valid.2 other otherMember
    have selectedEq :
        raised.blocks.get id = other := by
      change state.blocks.get oldId = other
      rfl
    rcases atomic other otherMember with growingCase | shrinkingCase
    ·
      rw [selectedEq]
      refine
        ⟨by
          rw [growingCase.2]
          exact IsSegment.nil _,
         oldStructural.2⟩
    · rcases shrinkingCase.2 with otherEmpty |
        ⟨otherElement, elementsEq⟩
      ·
        rw [selectedEq]
        refine
          ⟨by
            rw [otherEmpty]
            exact IsSegment.nil _,
           oldStructural.2⟩
      · have oldAssigned : otherElement ∈ state.allElements :=
          State.mem_allElements_iff.mpr
            ⟨other, otherMember, by simp [elementsEq]⟩
        have newAssigned :
            otherElement ∈
            (raised.insert blockId element).allElements := by
          rw [Canonical.mem_insert_allElements_iff
            raised blockId block element otherElement (by
              simpa [raised, State.increaseValue] using found)]
          exact Or.inr (by
            simpa [raised, State.increaseValue] using oldAssigned)
        have oldTopDown :
            otherElement ∈
              state.view.topDown other.owner other.side :=
          state.view.mem_topDown_iff.mpr
            ⟨oldStructural.parent_eq (by simp [elementsEq]),
              oldStructural.side_eq (by simp [elementsEq])⟩
        have newAttached :
            otherElement ∈
              raised.view.attachedTopDown
                (raised.insert blockId element).allElements
                other.owner other.side :=
          raised.view.mem_attachedTopDown_iff.mpr
            ⟨by
              simpa [raised, State.increaseValue] using oldTopDown,
              newAssigned⟩
        rw [selectedEq]
        refine ⟨?_, oldStructural.2⟩
        rw [elementsEq]
        exact singleton_isSegment_of_mem newAttached

  have raisedFound :
      raised.blocks[blockId]? = some block := by
    simpa [raised, State.increaseValue] using found
  have raisedUnassigned :
      element ∉ raised.allElements := by
    simpa [raised, State.increaseValue] using unassigned
  have raisedGap :
      0 ≤ raised.view.rawGap element := by
    simpa [raised, State.increaseValue] using elementGap
  have raisedValueOrder :
      raised.value block.creator + 1 ≤ raised.value element := by
    have creatorStillOne :
        raised.value block.creator = 1 := by
      simp [raised, State.increaseValue, creator_ne_element, creatorOne]
    have elementTwo :
        raised.value element = 2 := by
      simp [raised, State.increaseValue, elementOne]
    omega
  let inserted := raised.insert blockId element
  have insertStep :
      Step params raised (.operation (.insert blockId element))
        inserted := by
    exact
      raised.insert_step blockId block element raisedValid
        raisedFound growing raisedUnassigned raisedValueOrder raisedGap
        afterSegment otherValid
  have insertedValid : inserted.Valid params :=
    insertStep.after_valid
  have insertedValueTwo :
      inserted.value element = 2 := by
    simp [inserted, raised, State.insert, State.increaseValue, elementOne]
  have decreaseStep :
      Step params inserted
        (.operation (.valueChange element .decrease))
        (inserted.decreaseValue element) :=
    inserted.decreaseValue_step element insertedValid (by
      rw [insertedValueTwo]
      omega)
  have restored :
      inserted.decreaseValue element =
        state.insert blockId element := by
    cases state
    simp [inserted, raised, State.insert, State.increaseValue,
      State.decreaseValue]
  rw [← restored]
  exact
    Trace.cons raiseStep
      (Trace.cons insertStep (Trace.singleton decreaseStep))

end State

end Splay.Lazy
