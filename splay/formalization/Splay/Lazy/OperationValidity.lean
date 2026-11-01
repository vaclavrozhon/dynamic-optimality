import Splay.Interface.Decay
import Splay.Lazy.Operations

namespace Splay.Lazy

private theorem flatMap_modify_eq_of_preserves {α β : Type*}
    (values : List α) (index : ℕ) (update : α → α)
    (payload : α → List β)
    (preserves : ∀ value, payload (update value) = payload value) :
    (values.modify index update).flatMap payload =
      values.flatMap payload := by
  induction values generalizing index with
  | nil =>
      cases index <;> rfl
  | cons head tail ih =>
      cases index with
      | zero =>
          simp [preserves]
      | succ index =>
          rw [List.modify_succ_cons]
          simp [ih]

private theorem modify_get_eq_of_getElem?_eq_some
    {α : Type*} (values : List α) (index : ℕ) (foundValue : α)
    (update : α → α) (found : values[index]? = some foundValue)
    (queried : Fin (values.modify index update).length) :
    (values.modify index update).get queried =
      if index = queried.val then update foundValue
      else
        values.get
          ⟨queried.val, by simpa using queried.isLt⟩ := by
  obtain ⟨indexLt, getEq⟩ :=
    List.getElem?_eq_some_iff.mp found
  rw [List.get_eq_getElem, List.getElem_modify]
  split
  next indexEq =>
    have queriedEq : values[queried.val] = foundValue := by
      simpa only [indexEq] using getEq
    exact congrArg update queriedEq
  next _ =>
    rfl

private theorem converted_growingCount_le {n : ℕ}
    (blocks : List (Block n)) (index : ℕ) (intervalGap : ℤ)
    (creator : Element n) :
    ((blocks.modify index fun block =>
          block.converted intervalGap).map Block.toInterface |>.filter
        fun block =>
          decide
            (block.mode = .growing ∧ block.creator = creator)).length ≤
      (blocks.map Block.toInterface |>.filter fun block =>
        decide
          (block.mode = .growing ∧ block.creator = creator)).length := by
  induction blocks generalizing index with
  | nil =>
      simp
  | cons head tail ih =>
      cases index with
      | zero =>
          rw [List.modify_zero_cons]
          by_cases selected :
              head.mode = .growing ∧ head.creator = creator
          · simp [Block.converted, Block.toInterface, selected]
          · simp [Block.converted, Block.toInterface, selected]
      | succ index =>
          rw [List.modify_succ_cons]
          simp only [List.map_cons, List.filter_cons]
          split <;> simp_all

private theorem inserted_allElements_perm {n : ℕ}
    (blocks : List (Block n)) (index : ℕ) (block : Block n)
    (element : Element n) (found : blocks[index]? = some block) :
    ((blocks.modify index fun current =>
          current.inserted element).flatMap fun current =>
        current.elements).Perm
      (element :: blocks.flatMap fun current => current.elements) := by
  induction blocks generalizing index block with
  | nil =>
      simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only
            [List.getElem?_cons_zero, Option.some.injEq] at found
          subst block
          rw [List.modify_zero_cons]
          simp [Block.inserted]
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          rw [List.modify_succ_cons]
          simp only [List.flatMap_cons]
          exact
            ((ih index block found).append_left head.elements).trans
              List.perm_middle

private theorem inserted_growingCount_eq {n : ℕ}
    (blocks : List (Block n)) (index : ℕ) (element : Element n)
    (creator : Element n) :
    ((blocks.modify index fun block =>
          block.inserted element).map Block.toInterface |>.filter
        fun block =>
          decide
            (block.mode = .growing ∧ block.creator = creator)).length =
      (blocks.map Block.toInterface |>.filter fun block =>
        decide
          (block.mode = .growing ∧ block.creator = creator)).length := by
  induction blocks generalizing index with
  | nil =>
      simp
  | cons head tail ih =>
      cases index with
      | zero =>
          rw [List.modify_zero_cons]
          by_cases selected :
              head.mode = .growing ∧ head.creator = creator
          <;> simp [Block.inserted, Block.toInterface, selected]
      | succ index =>
          rw [List.modify_succ_cons]
          simp only [List.map_cons, List.filter_cons]
          split <;> simp_all

private theorem deleted_allElements_sublist {n : ℕ}
    (blocks : List (Block n)) (index : ℕ) (element : Element n)
    (intervalGap : ℤ) :
    ((blocks.modify index fun current =>
          current.deleted element intervalGap).flatMap fun current =>
        current.elements).Sublist
      (blocks.flatMap fun current => current.elements) := by
  induction blocks generalizing index with
  | nil =>
      simp
  | cons head tail ih =>
      cases index with
      | zero =>
          rw [List.modify_zero_cons]
          simp only [List.flatMap_cons, Block.deleted]
          exact List.erase_sublist.append (List.Sublist.refl _)
      | succ index =>
          rw [List.modify_succ_cons]
          simp only [List.flatMap_cons]
          exact (List.Sublist.refl _).append (ih index)

private theorem deleted_growingCount_eq {n : ℕ}
    (blocks : List (Block n)) (index : ℕ) (element : Element n)
    (intervalGap : ℤ) (creator : Element n) :
    ((blocks.modify index fun block =>
          block.deleted element intervalGap).map Block.toInterface |>.filter
        fun block =>
          decide
            (block.mode = .growing ∧ block.creator = creator)).length =
      (blocks.map Block.toInterface |>.filter fun block =>
        decide
          (block.mode = .growing ∧ block.creator = creator)).length := by
  induction blocks generalizing index with
  | nil =>
      simp
  | cons head tail ih =>
      cases index with
      | zero =>
          rw [List.modify_zero_cons]
          by_cases selected :
              head.mode = .growing ∧ head.creator = creator
          <;>
            simp
              [Block.deleted, Block.toInterface, selected]
      | succ index =>
          rw [List.modify_succ_cons]
          simp only [List.map_cons, List.filter_cons]
          split <;> simp_all

private theorem split_allElements_perm {n : ℕ}
    (blocks : List (Block n)) (sourceId : Interface.BlockId)
    (source : Block n) (prefixLength : ℕ)
    (prefixGap suffixGap : ℤ)
    (found : blocks[sourceId]? = some source) :
    ((State.splitBlocks blocks sourceId source prefixLength
          prefixGap suffixGap).flatMap fun current =>
        current.elements).Perm
      (blocks.flatMap fun current => current.elements) := by
  induction blocks generalizing sourceId source with
  | nil =>
      simp at found
  | cons head tail ih =>
      cases sourceId with
      | zero =>
          simp only
            [List.getElem?_cons_zero, Option.some.injEq] at found
          subst source
          simp
            [State.splitBlocks, Block.emptiedAfterSplit,
              Block.splitPrefix, Block.splitSuffix,
              List.take_append_drop]
          exact List.perm_append_comm
      | succ sourceId =>
          simp only [List.getElem?_cons_succ] at found
          rw [State.splitBlocks, List.modify_succ_cons]
          simp only
            [List.append_assoc, List.flatMap_append,
              List.flatMap_cons, List.flatMap_nil, List.append_nil]
          simpa [State.splitBlocks] using
            (ih sourceId source found).append_left head.elements

private theorem split_growingCount_eq {n : ℕ}
    (blocks : List (Block n)) (sourceId : Interface.BlockId)
    (source : Block n) (prefixLength : ℕ)
    (prefixGap suffixGap : ℤ)
    (found : blocks[sourceId]? = some source)
    (shrinking : source.mode = .shrinking)
    (creator : Element n) :
    ((State.splitBlocks blocks sourceId source prefixLength
          prefixGap suffixGap).map Block.toInterface |>.filter
        fun block =>
          decide
            (block.mode = .growing ∧ block.creator = creator)).length =
      (blocks.map Block.toInterface |>.filter fun block =>
        decide
          (block.mode = .growing ∧ block.creator = creator)).length := by
  induction blocks generalizing sourceId source with
  | nil =>
      simp at found
  | cons head tail ih =>
      cases sourceId with
      | zero =>
          simp only
            [List.getElem?_cons_zero, Option.some.injEq] at found
          subst source
          simp
            [State.splitBlocks, Block.emptiedAfterSplit,
              Block.splitPrefix, Block.splitSuffix,
              Block.toInterface, shrinking]
      | succ sourceId =>
          simp only [List.getElem?_cons_succ] at found
          have tailEq :=
            ih sourceId source found shrinking
          have tailEq' :
              (List.filter
                (fun block : Interface.Block n =>
                  decide
                    (block.mode = .growing ∧
                      block.creator = creator))
                (List.map Block.toInterface
                  ((tail.modify sourceId fun current =>
                      current.emptiedAfterSplit) ++
                    [source.splitPrefix prefixLength prefixGap,
                      source.splitSuffix prefixLength suffixGap]))).length =
                (List.filter
                  (fun block : Interface.Block n =>
                    decide
                      (block.mode = .growing ∧
                        block.creator = creator))
                  (List.map Block.toInterface tail)).length := by
            simpa [State.splitBlocks] using tailEq
          rw [State.splitBlocks, List.modify_succ_cons]
          simp only
            [List.cons_append, List.map_cons, List.filter_cons]
          by_cases selected :
              decide
                (head.toInterface.mode = .growing ∧
                  head.toInterface.creator = creator) = true
          · simp only [selected, if_true, List.length_cons]
            exact congrArg Nat.succ tailEq'
          · simp only [selected]
            exact tailEq'

namespace State

/-- Decrease one interface value without changing the rich heap structure. -/
def decreaseValue {n : ℕ} (state : State n)
    (element : Element n) : State n :=
  { state with
    value :=
      Function.update state.value element
        (state.value element - 1) }

/-- Increase one interface value without changing the rich heap structure. -/
def increaseValue {n : ℕ} (state : State n)
    (element : Element n) : State n :=
  { state with
    value :=
      Function.update state.value element
        (state.value element + 1) }

@[simp]
theorem decreaseValue_toInterface {n : ℕ} (state : State n)
    (element : Element n) :
    (state.decreaseValue element).toInterface =
      { state.toInterface with
        value :=
          Function.update state.value element
            (state.value element - 1) } :=
  rfl

@[simp]
theorem increaseValue_toInterface {n : ℕ} (state : State n)
    (element : Element n) :
    (state.increaseValue element).toInterface =
      { state.toInterface with
        value :=
          Function.update state.value element
            (state.value element + 1) } :=
  rfl

/-- Exact abstract effect of one permitted unit decrease. -/
theorem decreaseValue_effect {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (element : Element n) (canDecrease : 1 < state.value element) :
    Interface.Effect params state.toInterface
      (.valueChange element .decrease)
      (state.decreaseValue element).toInterface := by
  exact Interface.Effect.decrease canDecrease rfl rfl

/-- Exact abstract effect of one permitted unit increase. -/
theorem increaseValue_effect {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (element : Element n)
    (canIncrease : state.value element < params.valueBound) :
    Interface.Effect params state.toInterface
      (.valueChange element .increase)
      (state.increaseValue element).toInterface := by
  exact Interface.Effect.increase canIncrease rfl rfl

/-- A permitted unit decrease preserves the full rich transient invariant. -/
theorem decreaseValue_valid {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (element : Element n) (valid : state.Valid params)
    (canDecrease : 1 < state.value element) :
    (state.decreaseValue element).Valid params := by
  have beforeValid := valid.toInterface
  refine ⟨?_, ?_⟩
  · refine ⟨beforeValid.1, ?_, beforeValid.2.2⟩
    intro queried
    by_cases queriedEq : queried = element
    · subst queried
      rw [decreaseValue_toInterface]
      simp only [Function.update_self]
      have bounds := beforeValid.2.1 element
      change
        1 ≤ state.value element ∧
          state.value element ≤ params.valueBound
        at bounds
      omega
    · rw [decreaseValue_toInterface]
      simp only [Function.update_apply, if_neg queriedEq]
      exact beforeValid.2.1 queried
  · intro block member
    exact valid.2 block member

/-- A permitted unit increase preserves the full rich transient invariant. -/
theorem increaseValue_valid {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (element : Element n) (valid : state.Valid params)
    (canIncrease : state.value element < params.valueBound) :
    (state.increaseValue element).Valid params := by
  have beforeValid := valid.toInterface
  refine ⟨?_, ?_⟩
  · refine ⟨beforeValid.1, ?_, beforeValid.2.2⟩
    intro queried
    by_cases queriedEq : queried = element
    · subst queried
      rw [increaseValue_toInterface]
      simp only [Function.update_self]
      have bounds := beforeValid.2.1 element
      change
        1 ≤ state.value element ∧
          state.value element ≤ params.valueBound
        at bounds
      omega
    · rw [increaseValue_toInterface]
      simp only [Function.update_apply, if_neg queriedEq]
      exact beforeValid.2.1 queried
  · intro block member
    exact valid.2 block member

/-- A permitted unit decrease is one visible rich value-change step. -/
theorem decreaseValue_step {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (element : Element n) (valid : state.Valid params)
    (canDecrease : 1 < state.value element) :
    Step params state (.operation (.valueChange element .decrease))
      (state.decreaseValue element) := by
  exact
    Step.operation valid
      (decreaseValue_valid state element valid canDecrease)
      (decreaseValue_effect state element canDecrease)

/-- A permitted unit increase is one visible rich value-change step. -/
theorem increaseValue_step {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (element : Element n) (valid : state.Valid params)
    (canIncrease : state.value element < params.valueBound) :
    Step params state (.operation (.valueChange element .increase))
      (state.increaseValue element) := by
  exact
    Step.operation valid
      (increaseValue_valid state element valid canIncrease)
      (increaseValue_effect state element canIncrease)

private theorem valid_of_modify {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (blockId : Interface.BlockId) (block : Block n)
    (update : Block n → Block n)
    (found : state.blocks[blockId]? = some block)
    (interfaceValid :
      ({ state with
        blocks := state.blocks.modify blockId update }).toInterface.Valid
        params)
    (selectedValid :
      (update block).StructurallyValid state.view
        ((state.blocks.modify blockId update).flatMap fun current =>
          current.elements))
    (otherValid :
      ∀ id : Fin state.blocks.length, blockId ≠ id.val →
        (state.blocks.get id).StructurallyValid state.view
          ((state.blocks.modify blockId update).flatMap fun current =>
            current.elements)) :
    ({ state with
      blocks := state.blocks.modify blockId update }).Valid params := by
  refine ⟨interfaceValid, ?_⟩
  intro afterBlock afterMember
  change
    afterBlock.StructurallyValid state.view
      ((state.blocks.modify blockId update).flatMap fun current =>
        current.elements)
  obtain ⟨afterIndex, afterGet⟩ :=
    List.mem_iff_get.mp afterMember
  have getCase :=
    modify_get_eq_of_getElem?_eq_some
      state.blocks blockId block update found afterIndex
  change
    (state.blocks.modify blockId update).get afterIndex = afterBlock
    at afterGet
  rw [getCase] at afterGet
  split at afterGet
  next selected =>
    simpa only [← afterGet] using selectedValid
  next unselected =>
    let oldIndex : Fin state.blocks.length :=
      ⟨afterIndex.val, by
        have indexLt := afterIndex.isLt
        change
          afterIndex.val <
            (state.blocks.modify blockId update).length
          at indexLt
        simpa only [List.length_modify] using indexLt⟩
    have oldGet :
        state.blocks.get oldIndex = afterBlock := by
      have indexEq :
          oldIndex =
            ⟨afterIndex.val, by
              have indexLt := afterIndex.isLt
              change
                afterIndex.val <
                  (state.blocks.modify blockId update).length
                at indexLt
              simpa only [List.length_modify] using indexLt⟩ :=
        Fin.ext rfl
      rw [indexEq]
      exact afterGet
    rw [← oldGet]
    exact otherValid oldIndex unselected

/-- Conversion changes no block membership. -/
@[simp]
theorem convert_allElements {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (intervalGap : ℤ) :
    (state.convert blockId intervalGap).allElements =
      state.allElements := by
  cases state with
  | mk view blocks value =>
      simp only [convert, allElements]
      exact
        flatMap_modify_eq_of_preserves blocks blockId
          (fun block => block.converted intervalGap)
          (fun block : Block n => block.elements)
          (fun _ => rfl)

/--
Conversion preserves abstract-interface validity.  It can only remove one
growing block and changes neither membership nor values.
-/
theorem convert_interfaceValid {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (blockId : Interface.BlockId) (intervalGap : ℤ)
    (valid : state.Valid params) :
    (state.convert blockId intervalGap).toInterface.Valid params := by
  have beforeValid := valid.toInterface
  refine ⟨?_, ?_, ?_⟩
  · rw [State.toInterface_allElements, convert_allElements]
    exact valid.allElements_nodup
  · intro element
    exact beforeValid.2.1 element
  · intro creator
    have countLe :=
      converted_growingCount_le state.blocks blockId intervalGap creator
    have beforeBound := beforeValid.2.2 creator
    exact countLe.trans beforeBound

/--
Rich conversion preserves transient validity when the selected rich block is
found and the caller supplies the recomputed signed interval minimum.
-/
theorem convert_valid {n : ℕ} {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId) (block : Block n)
    (intervalGap : ℤ) (valid : state.Valid params)
    (found : state.blocks[blockId]? = some block)
    (gapValid : (block.converted intervalGap).GapValid state.view) :
    (state.convert blockId intervalGap).Valid params := by
  refine
    ⟨convert_interfaceValid state blockId intervalGap valid, ?_⟩
  intro afterBlock afterMember
  obtain ⟨afterIndex, afterGet⟩ :=
    List.mem_iff_get.mp afterMember
  have selectedValid :
      (block.converted intervalGap).StructurallyValid
        state.view state.allElements := by
    have blockMember : block ∈ state.blocks :=
      List.mem_iff_getElem?.2 ⟨blockId, found⟩
    exact
      Block.converted_structurallyValid
        (valid.2 block blockMember).isSegment gapValid
  have getCase :=
    modify_get_eq_of_getElem?_eq_some
      state.blocks blockId block
      (fun current => current.converted intervalGap)
      found afterIndex
  change
    afterBlock.StructurallyValid state.view
      (state.convert blockId intervalGap).allElements
  rw [convert_allElements]
  change
    (state.blocks.modify blockId fun current =>
      current.converted intervalGap).get afterIndex = afterBlock
    at afterGet
  rw [getCase] at afterGet
  split at afterGet
  · simpa only [← afterGet] using selectedValid
  · let oldIndex :
        Fin state.blocks.length :=
      ⟨afterIndex.val, by
        have indexLt := afterIndex.isLt
        change
          afterIndex.val <
            (state.blocks.modify blockId fun current =>
              current.converted intervalGap).length
          at indexLt
        simpa only [List.length_modify] using indexLt⟩
    have oldMember :
        state.blocks.get oldIndex ∈ state.blocks :=
      List.get_mem _ oldIndex
    have oldGet :
        state.blocks.get oldIndex = afterBlock := by
      have indexEq :
          oldIndex =
            ⟨afterIndex.val, by
              have indexLt := afterIndex.isLt
              change
                afterIndex.val <
                  (state.blocks.modify blockId fun current =>
                    current.converted intervalGap).length
                at indexLt
              simpa only [List.length_modify] using indexLt⟩ :=
        Fin.ext rfl
      rw [indexEq]
      exact afterGet
    rw [← oldGet]
    exact valid.2 (state.blocks.get oldIndex) oldMember

/--
A conversion with a valid recomputed interval gap is a visible rich step.
-/
theorem convert_step {n : ℕ} {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId) (block : Block n)
    (intervalGap : ℤ) (valid : state.Valid params)
    (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing)
    (gapValid : (block.converted intervalGap).GapValid state.view) :
    Step params state (.operation (.convert blockId))
      (state.convert blockId intervalGap) := by
  apply Step.operation valid
    (convert_valid state blockId block intervalGap valid found gapValid)
  apply convert_effect state blockId block intervalGap
  · simp [Interface.State.block?, State.toInterface, found]
  · exact growing

/--
Creating an empty growing block is a visible rich step whenever the creator
still has room under the interface limit.
-/
theorem create_step {n : ℕ} {params : Interface.Parameters}
    (state : State n) (creator : Element n) (side : Side)
    (valid : state.Valid params)
    (room :
      state.toInterface.growingCount creator < params.growingLimit) :
    Step params state (.operation (.create creator))
      (state.create creator side) := by
  exact
    Step.operation valid
      (create_valid state creator side valid room)
      (create_effect state creator side room)

/--
Insertion preserves abstract validity when it targets a found rich block and
the inserted element was globally unassigned.  Mode and creator metadata are
unchanged, so every growing-count bound is preserved exactly.
-/
theorem insert_interfaceValid {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (blockId : Interface.BlockId) (block : Block n)
    (element : Element n) (valid : state.Valid params)
    (found : state.blocks[blockId]? = some block)
    (unassigned : element ∉ state.allElements) :
    (state.insert blockId element).toInterface.Valid params := by
  have beforeValid := valid.toInterface
  refine ⟨?_, ?_, ?_⟩
  · rw [State.toInterface_allElements]
    change
      ((state.blocks.modify blockId fun current =>
          current.inserted element).flatMap fun current =>
        current.elements).Nodup
    have insertedNodup :
        (element :: state.allElements).Nodup :=
      valid.allElements_nodup.cons unassigned
    exact
      (inserted_allElements_perm
        state.blocks blockId block element found).symm.nodup
        insertedNodup
  · intro queried
    exact beforeValid.2.1 queried
  · intro creator
    rw [Interface.State.growingCount]
    change
      ((state.blocks.modify blockId fun current =>
          current.inserted element).map Block.toInterface |>.filter
        fun current =>
          decide
            (current.mode = .growing ∧
              current.creator = creator)).length ≤
        params.growingLimit
    rw [inserted_growingCount_eq]
    exact beforeValid.2.2 creator

/--
Rich insertion preserves transient validity under the exact local placement
condition for the enlarged growing block and explicit compatibility of every
unmodified block with the enlarged assigned set.
-/
theorem insert_valid {n : ℕ} {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId) (block : Block n)
    (element : Element n) (valid : state.Valid params)
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
    (state.insert blockId element).Valid params := by
  apply
    valid_of_modify state blockId block
      (fun current => current.inserted element) found
  · exact
      insert_interfaceValid
        state blockId block element valid found unassigned
  · have blockMember : block ∈ state.blocks :=
      List.mem_iff_getElem?.2 ⟨blockId, found⟩
    have selected :=
      Block.inserted_structurallyValid
        (valid.2 block blockMember) growing element elementGap
        afterSegment
    simpa [State.insert, State.allElements] using selected
  · intro id notSelected
    simpa [State.insert, State.allElements] using
      otherValid id notSelected

/--
An insertion satisfying the interface value order and the rich local
placement conditions is a visible rich step.
-/
theorem insert_step {n : ℕ} {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId) (block : Block n)
    (element : Element n) (valid : state.Valid params)
    (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing)
    (unassigned : element ∉ state.allElements)
    (valueOrder :
      state.value block.creator + 1 ≤ state.value element)
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
    Step params state (.operation (.insert blockId element))
      (state.insert blockId element) := by
  apply Step.operation valid
    (insert_valid state blockId block element valid found growing
      unassigned elementGap afterSegment otherValid)
  apply insert_effect state blockId block element
  · simp [Interface.State.block?, State.toInterface, found]
  · exact growing
  · simpa only [State.toInterface_allElements] using unassigned
  · exact valueOrder

/--
Deletion preserves abstract validity: it only removes an occurrence from the
assigned list and leaves values, creators, and modes unchanged.
-/
theorem delete_interfaceValid {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (blockId : Interface.BlockId) (element : Element n)
    (intervalGap : ℤ) (valid : state.Valid params) :
    (state.delete blockId element intervalGap).toInterface.Valid params := by
  have beforeValid := valid.toInterface
  refine ⟨?_, ?_, ?_⟩
  · rw [State.toInterface_allElements]
    change
      ((state.blocks.modify blockId fun current =>
          current.deleted element intervalGap).flatMap fun current =>
        current.elements).Nodup
    exact
      (deleted_allElements_sublist
        state.blocks blockId element intervalGap).nodup
        valid.allElements_nodup
  · intro queried
    exact beforeValid.2.1 queried
  · intro creator
    rw [Interface.State.growingCount]
    change
      ((state.blocks.modify blockId fun current =>
          current.deleted element intervalGap).map Block.toInterface |>.filter
        fun current =>
          decide
            (current.mode = .growing ∧
              current.creator = creator)).length ≤
        params.growingLimit
    rw [deleted_growingCount_eq]
    exact beforeValid.2.2 creator

/--
Rich deletion preserves transient validity under the recomputed gap and
segment conditions for the shrinking source, plus compatibility of every
unmodified block with the reduced assigned set.
-/
theorem delete_valid {n : ℕ} {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId) (block : Block n)
    (element : Element n) (intervalGap : ℤ)
    (valid : state.Valid params)
    (found : state.blocks[blockId]? = some block)
    (shrinking : block.mode = .shrinking)
    (afterSegment :
      IsSegment (block.deleted element intervalGap).elements
        (state.view.attachedTopDown
          (state.delete blockId element intervalGap).allElements
          block.owner block.side))
    (gapValid :
      (block.deleted element intervalGap).GapValid state.view)
    (otherValid :
      ∀ id : Fin state.blocks.length, blockId ≠ id.val →
        (state.blocks.get id).StructurallyValid state.view
          (state.delete blockId element intervalGap).allElements) :
    (state.delete blockId element intervalGap).Valid params := by
  apply
    valid_of_modify state blockId block
      (fun current => current.deleted element intervalGap) found
  · exact
      delete_interfaceValid
        state blockId element intervalGap valid
  · have selected :=
      Block.deleted_structurallyValid shrinking element intervalGap
        afterSegment gapValid
    simpa [State.delete, State.allElements] using selected
  · intro id notSelected
    simpa [State.delete, State.allElements] using
      otherValid id notSelected

/--
A legal deletion from a shrinking rich block is a visible rich step.
-/
theorem delete_step {n : ℕ} {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId) (block : Block n)
    (element : Element n) (intervalGap : ℤ)
    (valid : state.Valid params)
    (found : state.blocks[blockId]? = some block)
    (shrinking : block.mode = .shrinking)
    (present : element ∈ block.elements)
    (afterSegment :
      IsSegment (block.deleted element intervalGap).elements
        (state.view.attachedTopDown
          (state.delete blockId element intervalGap).allElements
          block.owner block.side))
    (gapValid :
      (block.deleted element intervalGap).GapValid state.view)
    (otherValid :
      ∀ id : Fin state.blocks.length, blockId ≠ id.val →
        (state.blocks.get id).StructurallyValid state.view
          (state.delete blockId element intervalGap).allElements) :
    Step params state (.operation (.delete blockId element))
      (state.delete blockId element intervalGap) := by
  apply Step.operation valid
    (delete_valid state blockId block element intervalGap valid found
      shrinking afterSegment gapValid otherValid)
  apply
    delete_effect state blockId block element intervalGap
  · simp [Interface.State.block?, State.toInterface, found]
  · exact shrinking
  · exact present

/-- Transferring placement metadata changes no block membership. -/
@[simp]
theorem transfer_allElements {n : ℕ} (state : State n)
    (afterView : HeapView n) (blockId : Interface.BlockId)
    (owner : Element n) (side : Side) (shift : ℤ) :
    (state.transfer afterView blockId owner side shift).allElements =
      state.allElements := by
  cases state with
  | mk view blocks value =>
      simp only [transfer, allElements]
      exact
        flatMap_modify_eq_of_preserves blocks blockId
          (fun block => block.transferred owner side shift)
          (fun block : Block n => block.elements)
          (fun _ => rfl)

/--
A nonempty shrinking interval can be transferred silently when its raw gaps
share the advertised shift, its new placement is a segment, and all
unmodified blocks remain structurally valid in the new heap view.
-/
theorem transfer_valid {n : ℕ} {params : Interface.Parameters}
    (state : State n) (afterView : HeapView n)
    (blockId : Interface.BlockId) (block : Block n)
    (owner : Element n) (side : Side) (shift : ℤ)
    (valid : state.Valid params)
    (found : state.blocks[blockId]? = some block)
    (shrinking : block.mode = .shrinking)
    (nonempty : block.elements ≠ [])
    (rawGapEq :
      ∀ element ∈ block.elements,
        afterView.rawGap element =
          state.view.rawGap element + shift)
    (afterSegment :
      IsSegment (block.transferred owner side shift).elements
        (afterView.attachedTopDown
          (state.transfer afterView blockId owner side shift).allElements
          owner side))
    (otherValid :
      ∀ id : Fin state.blocks.length, blockId ≠ id.val →
        (state.blocks.get id).StructurallyValid afterView
          (state.transfer afterView blockId owner side shift).allElements) :
    (state.transfer afterView blockId owner side shift).Valid params := by
  let base : State n := { state with view := afterView }
  have baseFound : base.blocks[blockId]? = some block := by
    simpa [base] using found
  have interfaceValid : base.toInterface.Valid params := by
    simpa [base, State.toInterface] using valid.toInterface
  have blockMember : block ∈ state.blocks :=
    List.mem_iff_getElem?.2 ⟨blockId, found⟩
  have transferSpec :=
    Block.transferred_isTransfer
      state.view afterView block owner side shift shrinking rawGapEq
  have selected :=
    transferSpec.after_structurallyValid
      (valid.2 block blockMember) nonempty afterSegment
  have modifiedInterfaceValid :
      ({ base with
        blocks :=
          base.blocks.modify blockId fun current =>
            current.transferred owner side shift }).toInterface.Valid
        params := by
    have transferredInterfaceValid :
        (base.transfer base.view blockId owner side shift).toInterface.Valid
          params := by
      rw [transfer_toInterface]
      exact interfaceValid
    simpa [State.transfer] using transferredInterfaceValid
  have modifiedValid :
      ({ base with
        blocks :=
          base.blocks.modify blockId fun current =>
            current.transferred owner side shift }).Valid params := by
    apply
      valid_of_modify base blockId block
        (fun current => current.transferred owner side shift)
        baseFound modifiedInterfaceValid
    · simpa [base, State.transfer, State.allElements] using selected
    · intro id notSelected
      simpa [base, State.transfer, State.allElements] using
        otherValid id notSelected
  simpa [base, State.transfer] using modifiedValid

/-- A valid rich interval transfer is one interface-invisible rich step. -/
theorem transfer_step {n : ℕ} {params : Interface.Parameters}
    (state : State n) (afterView : HeapView n)
    (blockId : Interface.BlockId) (block : Block n)
    (owner : Element n) (side : Side) (shift : ℤ)
    (valid : state.Valid params)
    (found : state.blocks[blockId]? = some block)
    (shrinking : block.mode = .shrinking)
    (nonempty : block.elements ≠ [])
    (rawGapEq :
      ∀ element ∈ block.elements,
        afterView.rawGap element =
          state.view.rawGap element + shift)
    (afterSegment :
      IsSegment (block.transferred owner side shift).elements
        (afterView.attachedTopDown
          (state.transfer afterView blockId owner side shift).allElements
          owner side))
    (otherValid :
      ∀ id : Fin state.blocks.length, blockId ≠ id.val →
        (state.blocks.get id).StructurallyValid afterView
          (state.transfer afterView blockId owner side shift).allElements) :
    Step params state .silent
      (state.transfer afterView blockId owner side shift) := by
  apply Step.silent valid
    (transfer_valid state afterView blockId block owner side shift
      valid found shrinking nonempty rawGapEq afterSegment otherValid)
  exact
    (transfer_toInterface
      state afterView blockId owner side shift).symm

/--
The abstract part of pass validity follows from the two exact global facts
about a pass block rearrangement: assigned elements are permuted and no
creator's growing-block count changes.  Values are definitionally unchanged.
-/
theorem pass_interfaceValid {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (sourceId : Interface.BlockId) (source : Block n)
    (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ) (valid : state.Valid params)
    (assignedPerm :
      (state.pass sourceId source matching
        sourceIntervalGap).allElements.Perm state.allElements)
    (growingCountEq :
      ∀ creator,
        (state.pass sourceId source matching
          sourceIntervalGap).toInterface.growingCount creator =
          state.toInterface.growingCount creator) :
    (state.pass sourceId source matching
      sourceIntervalGap).toInterface.Valid params := by
  have beforeValid := valid.toInterface
  refine ⟨?_, ?_, ?_⟩
  · rw [State.toInterface_allElements]
    exact assignedPerm.symm.nodup valid.allElements_nodup
  · intro element
    exact beforeValid.2.1 element
  · intro creator
    rw [growingCountEq creator]
    exact beforeValid.2.2 creator

/--
Pass preservation with transparent list-level side conditions.

`sourceFoundAfter` identifies the recomputed shrinking source after the fold;
`otherValid` states the local placement invariant for every result block
changed as a destination or left untouched.  The source invariant itself and
the complete abstract validity are derived here rather than assumed.
-/
theorem pass_valid {n : ℕ} {params : Interface.Parameters}
    (state : State n) (sourceId : Interface.BlockId)
    (source : Block n) (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ) (valid : state.Valid params)
    (shrinking : source.mode = .shrinking)
    (sourceFoundAfter :
      (state.pass sourceId source matching sourceIntervalGap).blocks[
          sourceId]? =
        some (source.afterPassSource matching sourceIntervalGap))
    (sourceSegment :
      IsSegment
        (source.afterPassSource matching sourceIntervalGap).elements
        (state.view.attachedTopDown
          (state.pass sourceId source matching
            sourceIntervalGap).allElements
          source.owner source.side))
    (sourceGapValid :
      (source.afterPassSource matching
        sourceIntervalGap).GapValid state.view)
    (assignedPerm :
      (state.pass sourceId source matching
        sourceIntervalGap).allElements.Perm state.allElements)
    (growingCountEq :
      ∀ creator,
        (state.pass sourceId source matching
          sourceIntervalGap).toInterface.growingCount creator =
          state.toInterface.growingCount creator)
    (otherValid :
      ∀ id :
          Fin
            (state.pass sourceId source matching
              sourceIntervalGap).blocks.length,
        sourceId ≠ id.val →
          ((state.pass sourceId source matching
            sourceIntervalGap).blocks.get id).StructurallyValid
              state.view
              (state.pass sourceId source matching
                sourceIntervalGap).allElements) :
    (state.pass sourceId source matching
      sourceIntervalGap).Valid params := by
  let after :=
    state.pass sourceId source matching sourceIntervalGap
  have sourceValid :
      (source.afterPassSource matching
        sourceIntervalGap).StructurallyValid
          state.view after.allElements := by
    exact
      Block.afterPassSource_structurallyValid shrinking matching
        sourceIntervalGap sourceSegment sourceGapValid
  refine
    ⟨pass_interfaceValid state sourceId source matching
        sourceIntervalGap valid assignedPerm growingCountEq,
      ?_⟩
  intro afterBlock afterMember
  change
    afterBlock.StructurallyValid state.view after.allElements
  obtain ⟨id, getEq⟩ := List.mem_iff_get.mp afterMember
  by_cases selected : sourceId = id.val
  · obtain ⟨sourceLt, sourceGet⟩ :=
      List.getElem?_eq_some_iff.mp sourceFoundAfter
    have idEq :
        id = ⟨sourceId, sourceLt⟩ :=
      Fin.ext selected.symm
    subst id
    change
      (state.pass sourceId source matching sourceIntervalGap).blocks[
        sourceId] = afterBlock
      at getEq
    rw [sourceGet] at getEq
    simpa only [← getEq] using sourceValid
  · rw [← getEq]
    exact otherValid id selected

/--
A pass satisfying the abstract matching rule and the explicit rich
rearrangement conditions is a visible rich step.
-/
theorem pass_step {n : ℕ} {params : Interface.Parameters}
    (state : State n) (sourceId : Interface.BlockId)
    (source : Block n) (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ) (valid : state.Valid params)
    (found : state.blocks[sourceId]? = some source)
    (validMatching :
      Interface.MatchingValid params state.toInterface sourceId
        source.toInterface matching)
    (sourceFoundAfter :
      (state.pass sourceId source matching sourceIntervalGap).blocks[
          sourceId]? =
        some (source.afterPassSource matching sourceIntervalGap))
    (sourceSegment :
      IsSegment
        (source.afterPassSource matching sourceIntervalGap).elements
        (state.view.attachedTopDown
          (state.pass sourceId source matching
            sourceIntervalGap).allElements
          source.owner source.side))
    (sourceGapValid :
      (source.afterPassSource matching
        sourceIntervalGap).GapValid state.view)
    (assignedPerm :
      (state.pass sourceId source matching
        sourceIntervalGap).allElements.Perm state.allElements)
    (growingCountEq :
      ∀ creator,
        (state.pass sourceId source matching
          sourceIntervalGap).toInterface.growingCount creator =
          state.toInterface.growingCount creator)
    (otherValid :
      ∀ id :
          Fin
            (state.pass sourceId source matching
              sourceIntervalGap).blocks.length,
        sourceId ≠ id.val →
          ((state.pass sourceId source matching
            sourceIntervalGap).blocks.get id).StructurallyValid
              state.view
              (state.pass sourceId source matching
                sourceIntervalGap).allElements) :
    Step params state (.operation (.pass sourceId matching))
      (state.pass sourceId source matching sourceIntervalGap) := by
  apply Step.operation valid
    (pass_valid state sourceId source matching sourceIntervalGap valid
      validMatching.1 sourceFoundAfter sourceSegment sourceGapValid
      assignedPerm growingCountEq otherValid)
  apply
    pass_effect state sourceId source matching sourceIntervalGap
  · simp [Interface.State.block?, State.toInterface, found]
  · exact validMatching

/--
Rich pass preservation while installing the heap view induced by the
pairings.

The abstract interface projection is definitionally the ordinary pass
projection, so its validity follows from `pass_interfaceValid`.  The rich
placement and gap obligations are instead stated in the new view.  This is
the preservation theorem needed by the article's pair-up interpretation: a
loser leaves the shrinking source, joins the winner's growing block, and at
the same time acquires the winner as its new heap parent.
-/
theorem passAtView_valid {n : ℕ} {params : Interface.Parameters}
    (state : State n) (afterView : HeapView n)
    (sourceId : Interface.BlockId) (source : Block n)
    (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ) (valid : state.Valid params)
    (shrinking : source.mode = .shrinking)
    (sourceFoundAfter :
      (state.passAtView afterView sourceId source matching
        sourceIntervalGap).blocks[sourceId]? =
      some (source.afterPassSource matching sourceIntervalGap))
    (sourceSegment :
      IsSegment
        (source.afterPassSource matching sourceIntervalGap).elements
        (afterView.attachedTopDown
          (state.passAtView afterView sourceId source matching
            sourceIntervalGap).allElements
          source.owner source.side))
    (sourceGapValid :
      (source.afterPassSource matching
        sourceIntervalGap).GapValid afterView)
    (assignedPerm :
      (state.passAtView afterView sourceId source matching
        sourceIntervalGap).allElements.Perm state.allElements)
    (growingCountEq :
      ∀ creator,
        (state.passAtView afterView sourceId source matching
          sourceIntervalGap).toInterface.growingCount creator =
        state.toInterface.growingCount creator)
    (otherValid :
      ∀ id : Fin
          (state.passAtView afterView sourceId source matching
            sourceIntervalGap).blocks.length,
        sourceId ≠ id.val →
          ((state.passAtView afterView sourceId source matching
            sourceIntervalGap).blocks.get id).StructurallyValid
              afterView
              (state.passAtView afterView sourceId source matching
                sourceIntervalGap).allElements) :
    (state.passAtView afterView sourceId source matching
      sourceIntervalGap).Valid params := by
  let after :=
    state.passAtView afterView sourceId source matching sourceIntervalGap
  have assignedPermPass :
      (state.pass sourceId source matching
        sourceIntervalGap).allElements.Perm state.allElements := by
    simpa only [passAtView_allElements] using assignedPerm
  have growingCountEqPass : ∀ creator,
      (state.pass sourceId source matching
        sourceIntervalGap).toInterface.growingCount creator =
      state.toInterface.growingCount creator := by
    intro creator
    simpa only [passAtView_toInterface] using growingCountEq creator
  have interfaceValid : after.toInterface.Valid params := by
    change
      (state.passAtView afterView sourceId source matching
        sourceIntervalGap).toInterface.Valid params
    simpa only [passAtView_toInterface] using
      pass_interfaceValid state sourceId source matching sourceIntervalGap
        valid assignedPermPass growingCountEqPass
  have sourceValid :
      (source.afterPassSource matching
        sourceIntervalGap).StructurallyValid
          afterView after.allElements := by
    exact
      Block.afterPassSource_structurallyValid shrinking matching
        sourceIntervalGap sourceSegment sourceGapValid
  refine ⟨interfaceValid, ?_⟩
  intro afterBlock afterMember
  change afterBlock.StructurallyValid afterView after.allElements
  obtain ⟨id, getEq⟩ := List.mem_iff_get.mp afterMember
  by_cases selected : sourceId = id.val
  · obtain ⟨sourceLt, sourceGet⟩ :=
      List.getElem?_eq_some_iff.mp sourceFoundAfter
    have idEq : id = ⟨sourceId, sourceLt⟩ :=
      Fin.ext selected.symm
    subst id
    change after.blocks[sourceId] = afterBlock at getEq
    rw [sourceGet] at getEq
    simpa only [← getEq] using sourceValid
  · rw [← getEq]
    exact otherValid id selected

/--
The streamlined article-facing pass preservation theorem.

For a legal matching, global assigned-element permutation and preservation of
the growing-block bounds are already consequences of the abstract interface
pass theorem.  Consequently the rich caller only supplies the structural
placement and signed-gap facts in the new heap view.
-/
theorem passAtView_valid_of_matching
    {n : ℕ} {params : Interface.Parameters}
    (state : State n) (afterView : HeapView n)
    (sourceId : Interface.BlockId) (source : Block n)
    (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ) (valid : state.Valid params)
    (found : state.blocks[sourceId]? = some source)
    (validMatching :
      Interface.MatchingValid params state.toInterface sourceId
        source.toInterface matching)
    (sourceFoundAfter :
      (state.passAtView afterView sourceId source matching
        sourceIntervalGap).blocks[sourceId]? =
      some (source.afterPassSource matching sourceIntervalGap))
    (sourceSegment :
      IsSegment
        (source.afterPassSource matching sourceIntervalGap).elements
        (afterView.attachedTopDown
          (state.passAtView afterView sourceId source matching
            sourceIntervalGap).allElements
          source.owner source.side))
    (sourceGapValid :
      (source.afterPassSource matching
        sourceIntervalGap).GapValid afterView)
    (otherValid :
      ∀ id : Fin
          (state.passAtView afterView sourceId source matching
            sourceIntervalGap).blocks.length,
        sourceId ≠ id.val →
          ((state.passAtView afterView sourceId source matching
            sourceIntervalGap).blocks.get id).StructurallyValid
              afterView
              (state.passAtView afterView sourceId source matching
                sourceIntervalGap).allElements) :
    (state.passAtView afterView sourceId source matching
      sourceIntervalGap).Valid params := by
  let after :=
    state.passAtView afterView sourceId source matching sourceIntervalGap
  have projectedFound :
      state.toInterface.block? sourceId = some source.toInterface := by
    simp [Interface.State.block?, State.toInterface, found]
  have interfaceValid : after.toInterface.Valid params := by
    have abstractValid :=
      validMatching.afterPass_valid valid.toInterface projectedFound
    change
      (state.passAtView afterView sourceId source matching
        sourceIntervalGap).toInterface.Valid params
    rw [passAtView_toInterface, pass_toInterface]
    simpa only [Interface.MatchingValid.afterPass] using abstractValid
  have sourceValid :
      (source.afterPassSource matching
        sourceIntervalGap).StructurallyValid
          afterView after.allElements := by
    exact
      Block.afterPassSource_structurallyValid validMatching.1 matching
        sourceIntervalGap sourceSegment sourceGapValid
  refine ⟨interfaceValid, ?_⟩
  intro afterBlock afterMember
  change afterBlock.StructurallyValid afterView after.allElements
  obtain ⟨id, getEq⟩ := List.mem_iff_get.mp afterMember
  by_cases selected : sourceId = id.val
  · obtain ⟨sourceLt, sourceGet⟩ :=
      List.getElem?_eq_some_iff.mp sourceFoundAfter
    have idEq : id = ⟨sourceId, sourceLt⟩ :=
      Fin.ext selected.symm
    subst id
    change after.blocks[sourceId] = afterBlock at getEq
    rw [sourceGet] at getEq
    simpa only [← getEq] using sourceValid
  · rw [← getEq]
    exact otherValid id selected

/-- A structurally sound `passAtView` with a legal interface matching is one
visible rich step; no separate global list/count premises are required. -/
theorem passAtView_step_of_matching
    {n : ℕ} {params : Interface.Parameters}
    (state : State n) (afterView : HeapView n)
    (sourceId : Interface.BlockId) (source : Block n)
    (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ) (valid : state.Valid params)
    (found : state.blocks[sourceId]? = some source)
    (validMatching :
      Interface.MatchingValid params state.toInterface sourceId
        source.toInterface matching)
    (sourceFoundAfter :
      (state.passAtView afterView sourceId source matching
        sourceIntervalGap).blocks[sourceId]? =
      some (source.afterPassSource matching sourceIntervalGap))
    (sourceSegment :
      IsSegment
        (source.afterPassSource matching sourceIntervalGap).elements
        (afterView.attachedTopDown
          (state.passAtView afterView sourceId source matching
            sourceIntervalGap).allElements
          source.owner source.side))
    (sourceGapValid :
      (source.afterPassSource matching
        sourceIntervalGap).GapValid afterView)
    (otherValid :
      ∀ id : Fin
          (state.passAtView afterView sourceId source matching
            sourceIntervalGap).blocks.length,
        sourceId ≠ id.val →
          ((state.passAtView afterView sourceId source matching
            sourceIntervalGap).blocks.get id).StructurallyValid
              afterView
              (state.passAtView afterView sourceId source matching
                sourceIntervalGap).allElements) :
    Step params state (.operation (.pass sourceId matching))
      (state.passAtView afterView sourceId source matching
        sourceIntervalGap) := by
  apply Step.operation valid
    (passAtView_valid_of_matching state afterView sourceId source matching
      sourceIntervalGap valid found validMatching sourceFoundAfter
      sourceSegment sourceGapValid otherValid)
  apply passAtView_effect state afterView sourceId source matching
    sourceIntervalGap
  · simp [Interface.State.block?, State.toInterface, found]
  · exact validMatching

/-- A legal rich pass, in any installed heap view, merely permutes the global
assigned-element list. -/
theorem passAtView_allElements_perm_of_matching
    {n : ℕ} {params : Interface.Parameters}
    (state : State n) (afterView : HeapView n)
    (sourceId : Interface.BlockId) (source : Block n)
    (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ)
    (found : state.blocks[sourceId]? = some source)
    (validMatching :
      Interface.MatchingValid params state.toInterface sourceId
        source.toInterface matching) :
    (state.passAtView afterView sourceId source matching
      sourceIntervalGap).allElements.Perm state.allElements := by
  have projectedFound :
      state.toInterface.block? sourceId = some source.toInterface := by
    simp [Interface.State.block?, State.toInterface, found]
  have projected :=
    Interface.MatchingValid.passBlocks_allElements_perm projectedFound
      validMatching
  have projectedRich :
      (state.passAtView afterView sourceId source matching
        sourceIntervalGap).toInterface.allElements.Perm
          state.toInterface.allElements := by
    rw [passAtView_toInterface, pass_toInterface]
    simpa only [Interface.MatchingValid.afterPass,
      Interface.State.allElements] using projected
  simpa only [State.toInterface_allElements] using projectedRich

/--
A pass that simultaneously installs its post-pairing heap view is one visible
rich `Pass` step.  Its erased operation is exactly the ordinary interface
pass; no silent rebase is hidden in this theorem.
-/
theorem passAtView_step {n : ℕ} {params : Interface.Parameters}
    (state : State n) (afterView : HeapView n)
    (sourceId : Interface.BlockId) (source : Block n)
    (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ) (valid : state.Valid params)
    (found : state.blocks[sourceId]? = some source)
    (validMatching :
      Interface.MatchingValid params state.toInterface sourceId
        source.toInterface matching)
    (sourceFoundAfter :
      (state.passAtView afterView sourceId source matching
        sourceIntervalGap).blocks[sourceId]? =
      some (source.afterPassSource matching sourceIntervalGap))
    (sourceSegment :
      IsSegment
        (source.afterPassSource matching sourceIntervalGap).elements
        (afterView.attachedTopDown
          (state.passAtView afterView sourceId source matching
            sourceIntervalGap).allElements
          source.owner source.side))
    (sourceGapValid :
      (source.afterPassSource matching
        sourceIntervalGap).GapValid afterView)
    (assignedPerm :
      (state.passAtView afterView sourceId source matching
        sourceIntervalGap).allElements.Perm state.allElements)
    (growingCountEq :
      ∀ creator,
        (state.passAtView afterView sourceId source matching
          sourceIntervalGap).toInterface.growingCount creator =
        state.toInterface.growingCount creator)
    (otherValid :
      ∀ id : Fin
          (state.passAtView afterView sourceId source matching
            sourceIntervalGap).blocks.length,
        sourceId ≠ id.val →
          ((state.passAtView afterView sourceId source matching
            sourceIntervalGap).blocks.get id).StructurallyValid
              afterView
              (state.passAtView afterView sourceId source matching
                sourceIntervalGap).allElements) :
    Step params state (.operation (.pass sourceId matching))
      (state.passAtView afterView sourceId source matching
        sourceIntervalGap) := by
  apply Step.operation valid
    (passAtView_valid state afterView sourceId source matching
      sourceIntervalGap valid validMatching.1 sourceFoundAfter sourceSegment
      sourceGapValid assignedPerm growingCountEq otherValid)
  apply passAtView_effect state afterView sourceId source matching
    sourceIntervalGap
  · simp [Interface.State.block?, State.toInterface, found]
  · exact validMatching

/--
Splitting a found shrinking source preserves abstract validity.  The assigned
sequence is merely permuted, and all three source-derived blocks remain
shrinking, so growing counts are unchanged.
-/
theorem split_interfaceValid {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (sourceId : Interface.BlockId) (source : Block n)
    (prefixLength : ℕ) (prefixGap suffixGap : ℤ)
    (valid : state.Valid params)
    (found : state.blocks[sourceId]? = some source)
    (shrinking : source.mode = .shrinking) :
    (state.split sourceId source prefixLength
      prefixGap suffixGap).toInterface.Valid params := by
  have beforeValid := valid.toInterface
  refine ⟨?_, ?_, ?_⟩
  · rw [State.toInterface_allElements]
    change
      ((State.splitBlocks state.blocks sourceId source prefixLength
          prefixGap suffixGap).flatMap fun current =>
        current.elements).Nodup
    exact
      (split_allElements_perm state.blocks sourceId source
        prefixLength prefixGap suffixGap found).symm.nodup
        valid.allElements_nodup
  · intro queried
    exact beforeValid.2.1 queried
  · intro creator
    rw [Interface.State.growingCount]
    change
      ((State.splitBlocks state.blocks sourceId source prefixLength
          prefixGap suffixGap).map Block.toInterface |>.filter
        fun current =>
          decide
            (current.mode = .growing ∧
              current.creator = creator)).length ≤
        params.growingLimit
    rw [split_growingCount_eq state.blocks sourceId source
      prefixLength prefixGap suffixGap found shrinking]
    exact beforeValid.2.2 creator

/--
Rich split validity follows from valid signed minima for the new prefix and
suffix.  No side condition is needed for other blocks because splitting only
permutes the globally assigned sequence.
-/
theorem split_valid {n : ℕ} {params : Interface.Parameters}
    (state : State n) (sourceId : Interface.BlockId)
    (source : Block n) (prefixLength : ℕ)
    (prefixGap suffixGap : ℤ)
    (valid : state.Valid params)
    (found : state.blocks[sourceId]? = some source)
    (shrinking : source.mode = .shrinking)
    (prefixGapValid :
      (source.splitPrefix prefixLength prefixGap).GapValid state.view)
    (suffixGapValid :
      (source.splitSuffix prefixLength suffixGap).GapValid state.view) :
    (state.split sourceId source prefixLength
      prefixGap suffixGap).Valid params := by
  refine
    ⟨split_interfaceValid state sourceId source prefixLength
        prefixGap suffixGap valid found shrinking,
      ?_⟩
  let after :=
    state.split sourceId source prefixLength prefixGap suffixGap
  have assignedPerm :
      after.allElements.Perm state.allElements := by
    exact
      split_allElements_perm state.blocks sourceId source
        prefixLength prefixGap suffixGap found
  have assignedMembership :
      ∀ element,
        element ∈ state.allElements ↔ element ∈ after.allElements := by
    intro element
    exact assignedPerm.mem_iff.symm
  have sourceMember : source ∈ state.blocks :=
    List.mem_iff_getElem?.2 ⟨sourceId, found⟩
  have sourceValid := valid.2 source sourceMember
  have emptiedValid :
      source.emptiedAfterSplit.StructurallyValid
        state.view after.allElements :=
    Block.emptiedAfterSplit_structurallyValid shrinking
  have prefixValidBefore :=
    Block.splitPrefix_structurallyValid
      sourceValid shrinking prefixLength prefixGap prefixGapValid
  have prefixValid :
      (source.splitPrefix prefixLength prefixGap).StructurallyValid
        state.view after.allElements :=
    Block.structurallyValid_assigned_congr prefixValidBefore
      assignedMembership
  have suffixValidBefore :=
    Block.splitSuffix_structurallyValid
      sourceValid shrinking prefixLength suffixGap suffixGapValid
  have suffixValid :
      (source.splitSuffix prefixLength suffixGap).StructurallyValid
        state.view after.allElements :=
    Block.structurallyValid_assigned_congr suffixValidBefore
      assignedMembership
  intro afterBlock afterMember
  change
    afterBlock.StructurallyValid state.view after.allElements
  change
    afterBlock ∈
      (state.blocks.modify sourceId fun current =>
        current.emptiedAfterSplit) ++
        [source.splitPrefix prefixLength prefixGap,
          source.splitSuffix prefixLength suffixGap]
    at afterMember
  rw [List.mem_append, List.mem_pair] at afterMember
  rcases afterMember with modifiedMember | rfl | rfl
  · obtain ⟨afterIndex, afterGet⟩ :=
      List.mem_iff_get.mp modifiedMember
    have getCase :=
      modify_get_eq_of_getElem?_eq_some
        state.blocks sourceId source Block.emptiedAfterSplit
        found afterIndex
    rw [getCase] at afterGet
    split at afterGet
    · simpa only [← afterGet] using emptiedValid
    · let oldIndex : Fin state.blocks.length :=
        ⟨afterIndex.val, by
          have indexLt := afterIndex.isLt
          change
            afterIndex.val <
              (state.blocks.modify sourceId
                Block.emptiedAfterSplit).length
            at indexLt
          simpa only [List.length_modify] using indexLt⟩
      have oldGet :
          state.blocks.get oldIndex = afterBlock := by
        have indexEq :
            oldIndex =
              ⟨afterIndex.val, by
                have indexLt := afterIndex.isLt
                change
                  afterIndex.val <
                    (state.blocks.modify sourceId
                      Block.emptiedAfterSplit).length
                  at indexLt
                simpa only [List.length_modify] using indexLt⟩ :=
          Fin.ext rfl
        rw [indexEq]
        exact afterGet
      have oldValid :=
        valid.2 (state.blocks.get oldIndex)
          (List.get_mem _ oldIndex)
      rw [← oldGet]
      exact
        Block.structurallyValid_assigned_congr oldValid
          assignedMembership
  · exact prefixValid
  · exact suffixValid

/-- A legal split of a shrinking source is a visible rich step. -/
theorem split_step {n : ℕ} {params : Interface.Parameters}
    (state : State n) (sourceId : Interface.BlockId)
    (source : Block n) (prefixLength : ℕ)
    (prefixGap suffixGap : ℤ)
    (valid : state.Valid params)
    (found : state.blocks[sourceId]? = some source)
    (shrinking : source.mode = .shrinking)
    (prefixLe : prefixLength ≤ source.elements.length)
    (prefixGapValid :
      (source.splitPrefix prefixLength prefixGap).GapValid state.view)
    (suffixGapValid :
      (source.splitSuffix prefixLength suffixGap).GapValid state.view) :
    Step params state (.operation (.split sourceId prefixLength))
      (state.split sourceId source prefixLength prefixGap suffixGap) := by
  apply Step.operation valid
    (split_valid state sourceId source prefixLength prefixGap suffixGap
      valid found shrinking prefixGapValid suffixGapValid)
  apply split_effect state sourceId source prefixLength prefixGap suffixGap
  · simp [Interface.State.block?, State.toInterface, found]
  · exact shrinking
  · exact prefixLe

end State

end Splay.Lazy
