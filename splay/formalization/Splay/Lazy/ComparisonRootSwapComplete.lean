import Splay.Lazy.ExactSafeInsert

namespace Splay.Lazy

namespace State

private theorem getElem?_modify_of_ne
    {α : Type*} (values : List α) (index : ℕ)
    (update : α → α) (queried : Fin values.length)
    (different : index ≠ queried.val) :
    (values.modify index update)[queried.val]? =
      some (values.get queried) := by
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨by simp, ?_⟩
  rw [List.getElem_modify]
  simp [different, List.get_eq_getElem]

private theorem singleton_isSegment_of_mem
    {α : Type*} {element : α} {whole : List α}
    (member : element ∈ whole) :
    IsSegment [element] whole := by
  rw [List.mem_iff_append] at member
  obtain ⟨front, back, rfl⟩ := member
  exact ⟨front, back, by simp⟩

/--
Deleting the sole element of a shrinking atomic block preserves the
shift-independent atomic shape.
-/
theorem ShiftAtomic.deleteSingleton
    {n : ℕ} {state : State n}
    (atomic : state.ShiftAtomic)
    (blockId : Interface.BlockId) (block : Block n)
    (element : Element n) (intervalGap : ℤ)
    (found : state.blocks[blockId]? = some block)
    (shrinking : block.mode = .shrinking)
    (singleton : block.elements = [element]) :
    (state.delete blockId element intervalGap).ShiftAtomic := by
  rcases state with ⟨view, blocks, value⟩
  change
    ∀ afterBlock ∈
        (blocks.modify blockId fun current =>
          current.deleted element intervalGap),
      (afterBlock.mode = .growing ∧ afterBlock.elements = []) ∨
        (afterBlock.mode = .shrinking ∧
          (afterBlock.elements = [] ∨
            ∃ item, afterBlock.elements = [item]))
  change blocks[blockId]? = some block at found
  change
    ∀ current ∈ blocks,
      (current.mode = .growing ∧ current.elements = []) ∨
        (current.mode = .shrinking ∧
          (current.elements = [] ∨
            ∃ item, current.elements = [item]))
    at atomic
  intro afterBlock afterMember
  induction blocks generalizing blockId with
  | nil =>
      simp at found
  | cons head tail ih =>
      cases blockId with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst block
          simp only [List.modify_zero_cons, List.mem_cons] at afterMember
          rcases afterMember with afterEq | tailMember
          · subst afterBlock
            right
            simp [Block.deleted, shrinking, singleton]
          · exact atomic afterBlock (by simp [tailMember])
      | succ blockId =>
          simp only [List.getElem?_cons_succ] at found
          rw [List.modify_succ_cons] at afterMember
          simp only [List.mem_cons] at afterMember
          rcases afterMember with afterEq | tailMember
          · subst afterBlock
            exact atomic head (by simp)
          · have tailAtomic :
                ∀ current ∈ tail,
                  (current.mode = .growing ∧ current.elements = []) ∨
                    (current.mode = .shrinking ∧
                      (current.elements = [] ∨
                        ∃ item, current.elements = [item])) := by
              intro current currentMember
              exact atomic current (by simp [currentMember])
            exact ih blockId found tailAtomic tailMember

/-- Exact assigned-set effect of deleting an atomic singleton. -/
theorem mem_deleteSingleton_allElements_iff
    {n : ℕ} {state : State n}
    (blockId : Interface.BlockId) (block : Block n)
    (element queried : Element n) (intervalGap : ℤ)
    (found : state.blocks[blockId]? = some block)
    (singleton : block.elements = [element])
    (nodup : state.allElements.Nodup) :
    queried ∈ (state.delete blockId element intervalGap).allElements ↔
      queried ∈ state.allElements ∧ queried ≠ element := by
  rcases state with ⟨view, blocks, value⟩
  change
    queried ∈
        (blocks.modify blockId fun current =>
          current.deleted element intervalGap).flatMap Block.elements ↔
      queried ∈ blocks.flatMap Block.elements ∧ queried ≠ element
  change blocks[blockId]? = some block at found
  change (blocks.flatMap Block.elements).Nodup at nodup
  induction blocks generalizing blockId with
  | nil =>
      simp at found
  | cons head tail ih =>
      change
        (head.elements ++ tail.flatMap Block.elements).Nodup at nodup
      have splitNodup := List.nodup_append.mp nodup
      cases blockId with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst block
          have elementNotTail :
              element ∉ tail.flatMap Block.elements := by
            intro elementTail
            have elementHead : element ∈ head.elements := by
              simp [singleton]
            exact
              splitNodup.2.2 element elementHead element elementTail rfl
          simp [Block.deleted, singleton]
          constructor
          · intro tailMember
            refine ⟨Or.inr tailMember, ?_⟩
            intro queriedEq
            apply elementNotTail
            simpa only [queriedEq, List.mem_flatMap] using tailMember
          · rintro ⟨atHead | inTail, different⟩
            · exact False.elim (different atHead)
            · exact inTail
      | succ blockId =>
          simp only [List.getElem?_cons_succ] at found
          have elementTail :
              element ∈ tail.flatMap Block.elements := by
            have blockMem : block ∈ tail :=
              List.mem_iff_getElem?.2 ⟨blockId, found⟩
            simp only [List.mem_flatMap]
            exact ⟨block, blockMem, by simp [singleton]⟩
          have elementNotHead : element ∉ head.elements := by
            intro elementHead
            exact splitNodup.2.2 element elementHead element elementTail rfl
          rw [List.modify_succ_cons]
          simp only [List.flatMap_cons, List.mem_append]
          rw [ih blockId found splitNodup.2.1]
          constructor
          · intro member
            rcases member with headMember | ⟨tailMember, different⟩
            · exact
                ⟨Or.inl headMember, fun equal =>
                  elementNotHead (equal ▸ headMember)⟩
            · exact ⟨Or.inr tailMember, different⟩
          · rintro ⟨headMember | tailMember, different⟩
            · exact Or.inl headMember
            · exact Or.inr ⟨tailMember, different⟩

/-- A found shrinking singleton can be legally detached in one delete step. -/
theorem ShiftAtomic.deleteSingleton_trace
    {n : ℕ} {params : Interface.Parameters} {state : State n}
    (atomic : state.ShiftAtomic)
    (stable : state.Stable params)
    (blockId : Interface.BlockId) (block : Block n)
    (element : Element n)
    (found : state.blocks[blockId]? = some block)
    (shrinking : block.mode = .shrinking)
    (singleton : block.elements = [element]) :
    Trace params state
      [.operation (.delete blockId element)]
      (state.delete blockId element 0) := by
  have present : element ∈ block.elements := by
    simp [singleton]
  have afterSegment :
      IsSegment (block.deleted element 0).elements
        (state.view.attachedTopDown
          (state.delete blockId element 0).allElements
          block.owner block.side) := by
    rw [show (block.deleted element 0).elements = [] by
      simp [Block.deleted, singleton]]
    exact IsSegment.nil _
  have gapValid :
      (block.deleted element 0).GapValid state.view := by
    simp [Block.GapValid, Block.deleted, shrinking, singleton]
  have otherValid :
      ∀ id : Fin state.blocks.length, blockId ≠ id.val →
        (state.blocks.get id).StructurallyValid state.view
          (state.delete blockId element 0).allElements := by
    intro id different
    let other := state.blocks.get id
    have otherMember : other ∈ state.blocks :=
      List.get_mem state.blocks id
    have oldStructural :
        other.StructurallyValid state.view state.allElements :=
      stable.valid.2 other otherMember
    rcases atomic other otherMember with growing | shrinkingCase
    · exact
        ⟨by rw [growing.2]; exact IsSegment.nil _,
          oldStructural.2⟩
    · rcases shrinkingCase.2 with empty | ⟨otherElement, elementsEq⟩
      · exact
          ⟨by rw [empty]; exact IsSegment.nil _,
            oldStructural.2⟩
      · have afterFound :
            (state.delete blockId element 0).blocks[id.val]? =
              some other := by
          simpa [State.delete, other] using
            getElem?_modify_of_ne state.blocks blockId
              (fun current => current.deleted element 0) id different
        have afterOtherMember :
            other ∈ (state.delete blockId element 0).blocks :=
          List.mem_iff_getElem?.2 ⟨id.val, afterFound⟩
        have afterAssigned :
            otherElement ∈
              (state.delete blockId element 0).allElements :=
          State.mem_allElements_iff.mpr
            ⟨other, afterOtherMember, by simp [elementsEq]⟩
        have topDownMember :
            otherElement ∈
              state.view.topDown other.owner other.side :=
          state.view.mem_topDown_iff.mpr
            ⟨oldStructural.parent_eq (by simp [elementsEq]),
              oldStructural.side_eq (by simp [elementsEq])⟩
        have attachedMember :
            otherElement ∈
              state.view.attachedTopDown
                (state.delete blockId element 0).allElements
                other.owner other.side :=
          state.view.mem_attachedTopDown_iff.mpr
            ⟨topDownMember, afterAssigned⟩
        refine ⟨?_, oldStructural.2⟩
        rw [elementsEq]
        exact singleton_isSegment_of_mem attachedMember
  exact Trace.singleton
    (state.delete_step blockId block element 0 stable.valid found
      shrinking present afterSegment gapValid otherValid)

private theorem oneGrowing_modify_of_preserves
    {n : ℕ} {state : State n}
    (oneGrowing : state.OneGrowingPerSide)
    (index : ℕ) (update : Block n → Block n)
    (preserves :
      ∀ block owner childSide,
        (update block).mode = .growing ∧
            (update block).owner = owner ∧
              (update block).side = childSide ↔
          block.mode = .growing ∧ block.owner = owner ∧
            block.side = childSide) :
    ({state with blocks := state.blocks.modify index update}).OneGrowingPerSide := by
  intro owner childSide
  obtain ⟨oldId, oldProperty, oldUnique⟩ :=
    oneGrowing owner childSide
  let newId : Fin (state.blocks.modify index update).length :=
    ⟨oldId.val, by simp⟩
  have newProperty :
      let block := (state.blocks.modify index update).get newId
      block.mode = .growing ∧ block.owner = owner ∧
        block.side = childSide := by
    change
      ((state.blocks.modify index update).get newId).mode = .growing ∧
        ((state.blocks.modify index update).get newId).owner = owner ∧
          ((state.blocks.modify index update).get newId).side = childSide
    rw [List.get_eq_getElem, List.getElem_modify]
    split
    next selected =>
      apply (preserves state.blocks[oldId.val] owner childSide).mpr
      simpa [List.get_eq_getElem] using oldProperty
    next notSelected =>
      simpa [newId, List.get_eq_getElem] using oldProperty
  refine ⟨newId, newProperty, ?_⟩
  intro candidate candidateProperty
  let oldCandidate : Fin state.blocks.length :=
    ⟨candidate.val, by simpa using candidate.isLt⟩
  have oldCandidateProperty :
      let block := state.blocks.get oldCandidate
      block.mode = .growing ∧ block.owner = owner ∧
        block.side = childSide := by
    change
      (state.blocks.get oldCandidate).mode = .growing ∧
        (state.blocks.get oldCandidate).owner = owner ∧
          (state.blocks.get oldCandidate).side = childSide
    change
      ((state.blocks.modify index update).get candidate).mode =
          .growing ∧
        ((state.blocks.modify index update).get candidate).owner = owner ∧
          ((state.blocks.modify index update).get candidate).side =
            childSide
      at candidateProperty
    rw [List.get_eq_getElem, List.getElem_modify] at candidateProperty
    split at candidateProperty
    next selected =>
      apply
        (preserves state.blocks[candidate.val] owner childSide).mp
          candidateProperty
    next notSelected =>
      simpa [oldCandidate, List.get_eq_getElem] using candidateProperty
  have oldEq := oldUnique oldCandidate oldCandidateProperty
  apply Fin.ext
  simpa [newId, oldCandidate] using congrArg Fin.val oldEq

/-- Deletion changes no mode or owner-side placement. -/
theorem OneGrowingPerSide.delete
    {n : ℕ} {state : State n}
    (oneGrowing : state.OneGrowingPerSide)
    (blockId : Interface.BlockId) (element : Element n)
    (intervalGap : ℤ) :
    (state.delete blockId element intervalGap).OneGrowingPerSide := by
  apply oneGrowing_modify_of_preserves oneGrowing
  intro block owner childSide
  simp [Block.deleted]

/-- Insertion changes no mode or owner-side placement. -/
theorem OneGrowingPerSide.insert
    {n : ℕ} {state : State n}
    (oneGrowing : state.OneGrowingPerSide)
    (blockId : Interface.BlockId) (element : Element n) :
    (state.insert blockId element).OneGrowingPerSide := by
  apply oneGrowing_modify_of_preserves oneGrowing
  intro block owner childSide
  simp [Block.inserted]

/--
Inserting into one empty growing block, converting it, and appending its empty
replacement restores the shift-atomic block shape.
-/
theorem ShiftAtomic.insertConvertCreate
    {n : ℕ} {state : State n}
    (atomic : state.ShiftAtomic)
    (blockId : Interface.BlockId) (block : Block n)
    (element : Element n) (intervalGap : ℤ)
    (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing)
    (empty : block.elements = []) :
    (((state.insert blockId element).convert blockId intervalGap).create
      block.creator block.side).ShiftAtomic := by
  rcases state with ⟨view, blocks, value⟩
  change blocks[blockId]? = some block at found
  change
    ∀ current ∈ blocks,
      (current.mode = .growing ∧ current.elements = []) ∨
        (current.mode = .shrinking ∧
          (current.elements = [] ∨
            ∃ item, current.elements = [item]))
    at atomic
  intro afterBlock afterMember
  simp only [State.insert, State.convert, State.create,
    List.mem_append, List.mem_singleton] at afterMember
  rcases afterMember with oldMember | rfl
  · induction blocks generalizing blockId with
    | nil =>
        simp at found
    | cons head tail ih =>
        cases blockId with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst block
            simp only [List.modify_zero_cons, List.mem_cons] at oldMember
            rcases oldMember with afterEq | tailMember
            · subst afterBlock
              right
              refine ⟨by simp [Block.converted], Or.inr ?_⟩
              exact ⟨element, by
                simp [Block.inserted, Block.converted, empty]⟩
            · exact atomic afterBlock (by simp [tailMember])
        | succ blockId =>
            simp only [List.getElem?_cons_succ] at found
            simp only [List.modify_succ_cons, List.mem_cons] at oldMember
            rcases oldMember with afterEq | tailMember
            · subst afterBlock
              exact atomic head (by simp)
            · have tailAtomic :
                  ∀ current ∈ tail,
                    (current.mode = .growing ∧ current.elements = []) ∨
                      (current.mode = .shrinking ∧
                        (current.elements = [] ∨
                          ∃ item, current.elements = [item])) := by
                intro current currentMember
                exact atomic current (by simp [currentMember])
              exact ih blockId found tailAtomic tailMember
  · left
    simp [Block.emptyGrowing]


/--
Converting and replacing a growing block preserves owner-side uniqueness.
-/
theorem OneGrowingPerSide.convertAndCreate
    {n : ℕ} {params : Interface.Parameters} {state : State n}
    (oneGrowing : state.OneGrowingPerSide)
    (valid : state.Valid params)
    (blockId : Interface.BlockId) (block : Block n)
    (intervalGap : ℤ)
    (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing) :
    ((state.convert blockId intervalGap).create
      block.creator block.side).OneGrowingPerSide :=
  state.convertAndCreate_oneGrowingPerSide
    blockId block intervalGap valid found growing oneGrowing

/--
An empty growing block at the actual parent-side of an unassigned element
admits the value-safe insertion macro.  Shift atomicity makes every untouched
block empty or a singleton, so enlarging the assigned filter cannot destroy
its interval shape.
-/
theorem ShiftAtomic.exists_safeInsert_trace_of_emptyGrowing
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
    (elementGap : 0 ≤ state.view.rawGap element) :
    ∃ events,
      Trace params state events (state.insert blockId element) := by
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
    state.exists_safeInsert_trace blockId block element valid found
      growing unassigned elementGap afterSegment otherValid

/-- Every assigned element of a stable shift-atomic state has value one. -/
theorem ShiftAtomic.value_eq_one_of_mem
    {n : ℕ} {params : Interface.Parameters} {state : State n}
    (atomic : state.ShiftAtomic)
    (stable : state.Stable params)
    {element : Element n} (assigned : element ∈ state.allElements) :
    state.value element = 1 := by
  obtain ⟨block, blockMember, elementMember⟩ :=
    State.mem_allElements_iff.mp assigned
  rcases atomic block blockMember with growing | shrinking
  · rw [growing.2] at elementMember
    simp at elementMember
  · rcases shrinking.2 with empty | ⟨singleton, elementsEq⟩
    · rw [empty] at elementMember
      simp at elementMember
    · have elementEq : element = singleton := by
        simpa [elementsEq] using elementMember
      subst singleton
      have valueEq :=
        stable.2.2.2.2.2.2 block blockMember element elementMember
      have gapValid := (stable.valid.2 block blockMember).2.2
      simp only [Block.GapValid, shrinking.1] at gapValid
      have gapEq :
          block.intervalGap = state.view.rawGap element := by
        rcases gapValid with emptyCase | nonemptyCase
        · exact False.elim (by
            have nonempty : block.elements ≠ [] := by
              simp [elementsEq]
            exact nonempty emptyCase.1)
        · obtain ⟨minimizer, minimizerMember, attains⟩ :=
            nonemptyCase.2.1
          have minimizerEq : minimizer = element := by
            simpa [elementsEq] using minimizerMember
          subst minimizer
          exact attains.symm
      rw [valueEq, gapEq]
      exact Analysis.transientContractedGap_self _

end State

/--
Generic checked root exchange for a stable shift-atomic state.

The old root is inserted into the empty growing block at its actual new
parent-side; the new root is first removed from its shrinking singleton.
The structural endpoint is normalized by the already checked finite
value-to-one trace.
-/
theorem exists_rootSwap_trace_of_shiftAtomic
    {n : ℕ} {params : Interface.Parameters} {initial : State n}
    (stable : initial.Stable params)
    (atomic : initial.ShiftAtomic)
    (afterView : HeapView n)
    (afterOrdered : afterView.HeapOrdered)
    (rootsNe : afterView.root ≠ initial.view.root) :
    ∃ final events,
      Trace params initial events final ∧
        final.Stable params ∧ final.ShiftAtomic ∧
          final.view = afterView ∧
          Interface.totalInserts (eraseOperations events) = 1 ∧
          Interface.totalIncreases (eraseOperations events) = 1 := by
  let newRoot := afterView.root
  let oldRoot := initial.view.root
  have newRootNeOld : newRoot ≠ oldRoot := rootsNe
  have newRootParentBefore :
      initial.view.parent newRoot ≠ none :=
    initial.view.parent_ne_none_of_ne_root newRootNeOld
  have newRootAssigned :
      newRoot ∈ initial.allElements :=
    (stable.2.1 newRoot).2 newRootParentBefore
  obtain ⟨rootBlock, rootBlockMember, newRootMember⟩ :=
    State.mem_allElements_iff.mp newRootAssigned
  have rootShape := atomic rootBlock rootBlockMember
  have rootShrinking : rootBlock.mode = .shrinking := by
    rcases rootShape with growing | shrinking
    · rw [growing.2] at newRootMember
      simp at newRootMember
    · exact shrinking.1
  have rootSingleton : rootBlock.elements = [newRoot] := by
    rcases rootShape with growing | shrinking
    · rw [growing.2] at newRootMember
      simp at newRootMember
    · rcases shrinking.2 with empty | ⟨singleton, elementsEq⟩
      · rw [empty] at newRootMember
        simp at newRootMember
      · have rootEq : newRoot = singleton := by
          simpa [elementsEq] using newRootMember
        simpa [rootEq] using elementsEq
  obtain ⟨rootBlockId, rootFound⟩ :=
    List.mem_iff_getElem?.mp rootBlockMember
  let detached :=
    initial.delete rootBlockId newRoot 0
  have detachTrace :
      Trace params initial
        [.operation (.delete rootBlockId newRoot)] detached := by
    exact atomic.deleteSingleton_trace stable
      rootBlockId rootBlock newRoot rootFound
      rootShrinking rootSingleton
  have detachedValid : detached.Valid params :=
    detachTrace.final_valid
  have detachedAtomic : detached.ShiftAtomic := by
    exact atomic.deleteSingleton rootBlockId rootBlock newRoot 0
      rootFound rootShrinking rootSingleton
  have detachedRootNotMem :
      afterView.root ∉ detached.allElements := by
    intro assigned
    have different :=
      (State.mem_deleteSingleton_allElements_iff
        rootBlockId rootBlock newRoot afterView.root 0
        rootFound rootSingleton stable.valid.allElements_nodup).mp
        assigned |>.2
    exact different rfl
  let rebased := detached.rebaseShiftAtomic afterView
  have rebasedValid : rebased.Valid params := by
    exact detachedAtomic.rebase_valid_of_root_not_mem
      detachedValid detachedRootNotMem
  have rebaseTrace :
      Trace params detached [.silent] rebased := by
    exact Trace.singleton
      (Step.silent detachedValid rebasedValid
        (detached.rebaseShiftAtomic_toInterface afterView).symm)
  have rebasedAtomic : rebased.ShiftAtomic :=
    detachedAtomic.rebase afterView
  have detachedOneGrowing : detached.OneGrowingPerSide := by
    exact stable.2.2.2.1.delete rootBlockId newRoot 0
  have rebasedOneGrowing : rebased.OneGrowingPerSide := by
    exact State.ShiftAtomic.rebase_oneGrowingPerSide
      afterView detachedOneGrowing
  have oldRootNeNew : oldRoot ≠ afterView.root :=
    Ne.symm rootsNe
  cases parentEq : afterView.parent oldRoot with
  | none =>
      exact False.elim
        (afterView.parent_ne_none_of_ne_root oldRootNeNew parentEq)
  | some owner =>
      obtain ⟨growingId, growingProperty, _growingUnique⟩ :=
        rebasedOneGrowing owner (afterView.side oldRoot)
      let growingBlock := rebased.blocks.get growingId
      have growingMode : growingBlock.mode = .growing :=
        growingProperty.1
      have growingOwner : growingBlock.owner = owner :=
        growingProperty.2.1
      have growingSide :
          growingBlock.side = afterView.side oldRoot :=
        growingProperty.2.2
      have growingFound :
          rebased.blocks[growingId.val]? = some growingBlock := by
        apply List.getElem?_eq_some_iff.mpr
        exact ⟨growingId.isLt, by
          simp [growingBlock, List.get_eq_getElem]⟩
      have growingMember : growingBlock ∈ rebased.blocks :=
        List.get_mem rebased.blocks growingId
      have growingEmpty : growingBlock.elements = [] := by
        rcases rebasedAtomic growingBlock growingMember with
            growingCase | shrinkingCase
        · exact growingCase.2
        · rw [growingMode] at shrinkingCase
          simp at shrinkingCase
      have oldRootUnassigned : oldRoot ∉ rebased.allElements := by
        rw [show rebased.allElements = detached.allElements by
          exact State.rebaseShiftAtomic_allElements detached afterView]
        intro assigned
        have beforeAssigned :=
          (State.mem_deleteSingleton_allElements_iff
            rootBlockId rootBlock newRoot oldRoot 0
            rootFound rootSingleton
            stable.valid.allElements_nodup).mp assigned |>.1
        exact stable.valid.root_not_mem beforeAssigned
      have growingParent :
          rebased.view.parent oldRoot = some growingBlock.owner := by
        change afterView.parent oldRoot = some growingBlock.owner
        rw [parentEq, growingOwner]
      have growingSideEq :
          rebased.view.side oldRoot = growingBlock.side := by
        change afterView.side oldRoot = growingBlock.side
        exact growingSide.symm
      have oldRootGap :
          0 ≤ rebased.view.rawGap oldRoot := by
        change 0 ≤ afterView.rawGap oldRoot
        exact le_of_lt
          (afterView.rawGap_pos_of_heapOrdered
            afterOrdered parentEq)
      have initialValuesOne :
          ∀ queried, initial.value queried = 1 := by
        intro queried
        by_cases atRoot : queried = initial.view.root
        · subst queried
          exact stable.2.2.2.2.2.1
        · apply atomic.value_eq_one_of_mem stable
          apply (stable.2.1 queried).2
          exact initial.view.parent_ne_none_of_ne_root atRoot
      have creatorOne :
          rebased.value growingBlock.creator = 1 := by
        simpa [rebased, detached, State.rebaseShiftAtomic,
          State.delete] using initialValuesOne growingBlock.creator
      have oldRootOne :
          rebased.value oldRoot = 1 := by
        simpa [rebased, detached, State.rebaseShiftAtomic,
          State.delete] using initialValuesOne oldRoot
      let insertEvents : List (Event n) :=
        [.operation (.valueChange oldRoot .increase),
          .operation (.insert growingId.val oldRoot),
          .operation (.valueChange oldRoot .decrease)]
      have insertTrace :
          Trace params rebased insertEvents
            (rebased.insert growingId.val oldRoot) := by
        exact
          rebasedAtomic.oneIncreaseInsertDecrease_trace_of_emptyGrowing
            rebasedValid growingId.val growingBlock oldRoot
            growingFound growingMode growingEmpty oldRootUnassigned
            growingParent growingSideEq oldRootGap creatorOne oldRootOne
      let inserted := rebased.insert growingId.val oldRoot
      let insertedBlock := growingBlock.inserted oldRoot
      have insertedValid : inserted.Valid params :=
        insertTrace.final_valid
      have insertedFound :
          inserted.blocks[growingId.val]? = some insertedBlock := by
        apply List.getElem?_eq_some_iff.mpr
        refine ⟨by simp [inserted, State.insert], ?_⟩
        change
          (rebased.blocks.modify growingId.val
            (fun current => current.inserted oldRoot))[growingId.val] =
              insertedBlock
        rw [List.getElem_modify, if_pos rfl]
        have selectedEq :
            rebased.blocks[growingId.val] = growingBlock := by
          simp [growingBlock, List.get_eq_getElem]
        rw [selectedEq]
      have insertedGrowing : insertedBlock.mode = .growing := by
        simp [insertedBlock, Block.inserted, growingMode]
      have insertedGapValid :
          (insertedBlock.converted
            (afterView.rawGap oldRoot)).GapValid inserted.view := by
        simp [Block.GapValid, Block.converted, insertedBlock,
          Block.inserted, growingEmpty, inserted, State.insert]
        change
          Analysis.IsIntervalGap {oldRoot} afterView.rawGap
            (afterView.rawGap oldRoot)
        simp [Analysis.IsIntervalGap]
      let structural :=
        (inserted.convert growingId.val (afterView.rawGap oldRoot)).create
          insertedBlock.creator insertedBlock.side
      have structuralTrace :
          Trace params inserted
            [.operation (.convert growingId.val),
              .operation (.create insertedBlock.creator)]
            structural := by
        exact inserted.convertAndCreate_trace
          growingId.val insertedBlock (afterView.rawGap oldRoot)
          insertedValid insertedFound insertedGrowing insertedGapValid
      have structuralValid : structural.Valid params :=
        structuralTrace.final_valid
      have structuralAtomic : structural.ShiftAtomic := by
        simpa [structural, inserted, insertedBlock, Block.inserted] using
          rebasedAtomic.insertConvertCreate
            growingId.val growingBlock oldRoot
            (afterView.rawGap oldRoot) growingFound
            growingMode growingEmpty
      have insertedOneGrowing : inserted.OneGrowingPerSide := by
        exact rebasedOneGrowing.insert growingId.val oldRoot
      have structuralOneGrowing :
          structural.OneGrowingPerSide := by
        exact insertedOneGrowing.convertAndCreate insertedValid
          growingId.val insertedBlock (afterView.rawGap oldRoot)
          insertedFound insertedGrowing
      have structuralView : structural.view = afterView := by
        rfl
      have structuralComplete : structural.Complete := by
        intro queried
        have structuralElements :
            structural.allElements = inserted.allElements := by
          simp [structural]
        rw [structuralElements]
        rw [Canonical.mem_insert_allElements_iff
          rebased growingId.val growingBlock oldRoot queried growingFound]
        rw [show rebased.allElements = detached.allElements by
          exact State.rebaseShiftAtomic_allElements detached afterView]
        rw [State.mem_deleteSingleton_allElements_iff
          rootBlockId rootBlock newRoot queried 0 rootFound
          rootSingleton stable.valid.allElements_nodup]
        constructor
        · rintro (queriedOld | ⟨beforeAssigned, queriedNew⟩)
          · subst queried
            exact afterView.parent_ne_none_of_ne_root oldRootNeNew
          · exact afterView.parent_ne_none_of_ne_root queriedNew
        · intro afterParent
          have queriedNew : queried ≠ newRoot := by
            intro queriedEq
            subst queried
            exact afterParent afterView.root_parent
          by_cases queriedOld : queried = oldRoot
          · exact Or.inl queriedOld
          · refine Or.inr ⟨?_, queriedNew⟩
            apply (stable.2.1 queried).2
            exact initial.view.parent_ne_none_of_ne_root queriedOld
      have structuralRootValue :
          structural.value structural.view.root = 1 := by
        have initialNewRootValue :
            initial.value newRoot = 1 :=
          atomic.value_eq_one_of_mem stable newRootAssigned
        simpa [structural, inserted, rebased, detached,
          State.create, State.convert, State.insert,
          State.rebaseShiftAtomic, State.delete, structuralView,
          newRoot] using initialNewRootValue
      obtain ⟨valueEvents, final, valueTrace, finalAtomic,
          finalPrepared, finalView, valueInserts,
          valueIncreases⟩ :=
        State.exists_adjustValuesToOne_rankPrepared
          structuralAtomic structuralValid structuralComplete
          structuralOneGrowing structuralRootValue
      have finalStable : final.Stable params := by
        exact finalPrepared.stable (by
          rw [finalView, structuralView]
          exact afterOrdered)
      refine
        ⟨final,
          [.operation (.delete rootBlockId newRoot)] ++
            [.silent] ++ insertEvents ++
              [.operation (.convert growingId.val),
                .operation (.create insertedBlock.creator)] ++
                valueEvents,
          ?_, finalStable, finalAtomic, ?_, ?_, ?_⟩
      · simpa [List.append_assoc] using
          detachTrace.append
            (rebaseTrace.append
              (insertTrace.append
                (structuralTrace.append valueTrace)))
      · exact finalView.trans structuralView
      · simp [insertEvents, eraseOperations, Event.operations,
          Interface.totalInserts, Interface.Operation.insertCount]
        simpa only [eraseOperations, Interface.totalInserts] using
          valueInserts
      · simp [insertEvents, eraseOperations, Event.operations,
          Interface.totalIncreases, Interface.Operation.increaseCount]
        simpa only [eraseOperations, Interface.totalIncreases] using
          valueIncreases

/--
The concrete finite macro inhabits the root-swap obligation used by the
comparison-rotation preparer.
-/
theorem comparisonRootSwapBuilder
    {n : ℕ} (params : Interface.Parameters)
    (splayTree : Tree.BST 0 n) :
    ComparisonRootSwapBuilder params splayTree := by
  intro beforeComparison afterComparison initial
    rootRotation initialRepresents initialAtomic
  let afterView :=
    Canonical.canonicalHeapView
      (Rank.Snapshot.ofTree afterComparison) splayTree
  have afterOrdered : afterView.HeapOrdered :=
    Canonical.canonicalHeapView_heapOrdered
      (Rank.Snapshot.ofTree afterComparison) splayTree
  have rootsNe : afterView.root ≠ initial.view.root := by
    rw [initialRepresents.view_eq]
    change
      Canonical.canonicalRoot
          (Rank.Snapshot.ofTree afterComparison) splayTree ≠
        Canonical.canonicalRoot
          (Rank.Snapshot.ofTree beforeComparison) splayTree
    cases rootRotation with
    | right a b c =>
        rw [Canonical.canonicalRoot_ofTree_node,
          Canonical.canonicalRoot_ofTree_node]
        intro equal
        have valuesEqual := congrArg Fin.val equal
        have separated := b.lower_le_upper
        simp [Rank.valuePos] at valuesEqual
        omega
    | left a b c =>
        rw [Canonical.canonicalRoot_ofTree_node,
          Canonical.canonicalRoot_ofTree_node]
        intro equal
        have valuesEqual := congrArg Fin.val equal
        have separated := b.lower_le_upper
        simp [Rank.valuePos] at valuesEqual
        omega
  obtain ⟨swapped, events, trace, swappedStable,
      swappedAtomic, swappedView, _insertCount, _increaseCount⟩ :=
    exists_rootSwap_trace_of_shiftAtomic
      initialRepresents.stable initialAtomic afterView
      afterOrdered rootsNe
  refine ⟨swapped, events, trace, ?_, swappedAtomic⟩
  exact ⟨swappedStable, swappedView⟩

/-- All shift-atomic comparison rotations now have prepared trace prefixes. -/
theorem shiftAtomicComparisonRotationPreparer
    {n : ℕ} (params : Interface.Parameters)
    (splayTree : Tree.BST 0 n) :
    ShiftAtomicComparisonRotationPreparer params splayTree :=
  shiftAtomicComparisonRotationPreparer_of_rootSwapBuilder
    (comparisonRootSwapBuilder params splayTree)

end Splay.Lazy
