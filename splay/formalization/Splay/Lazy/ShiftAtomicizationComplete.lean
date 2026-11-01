import Splay.Lazy.ShiftAtomicization

namespace Splay.Lazy

namespace Block

/--
The number of structural atomization steps still needed by one block.

A growing block is first converted and replaced, after which its elements
form a shrinking block.  A shrinking block of length `k` needs `k - 1`
head-splits.  Thus both legal macros decrease the global sum by one.
-/
def atomicDefect {n : ℕ} (block : Block n) : ℕ :=
  match block.mode with
  | .growing => block.elements.length
  | .shrinking => block.elements.length - 1

def ShiftAtomic {n : ℕ} (block : Block n) : Prop :=
  (block.mode = .growing ∧ block.elements = []) ∨
    (block.mode = .shrinking ∧
      (block.elements = [] ∨ ∃ element, block.elements = [element]))

theorem shiftAtomic_iff_atomicDefect_eq_zero {n : ℕ}
    (block : Block n) :
    block.ShiftAtomic ↔ block.atomicDefect = 0 := by
  cases modeEq : block.mode <;>
    cases elementsEq : block.elements with
    | nil =>
        simp [ShiftAtomic, atomicDefect, modeEq, elementsEq]
    | cons head tail =>
        cases tail with
        | nil =>
            simp [ShiftAtomic, atomicDefect, modeEq, elementsEq]
        | cons second rest =>
            simp [ShiftAtomic, atomicDefect, modeEq, elementsEq]

end Block

namespace State

/-- Sum of all remaining block-local atomization steps. -/
def atomicDefect {n : ℕ} (state : State n) : ℕ :=
  (state.blocks.map Block.atomicDefect).sum

theorem shiftAtomic_iff_atomicDefect_eq_zero {n : ℕ}
    (state : State n) :
    state.ShiftAtomic ↔ state.atomicDefect = 0 := by
  rw [State.ShiftAtomic, atomicDefect, List.sum_eq_zero_iff]
  constructor
  · intro atomic blockDefect blockDefectMem
    obtain ⟨block, blockMem, rfl⟩ := List.mem_map.mp blockDefectMem
    exact (Block.shiftAtomic_iff_atomicDefect_eq_zero block).mp
      (atomic block blockMem)
  · intro allZero block blockMem
    apply (Block.shiftAtomic_iff_atomicDefect_eq_zero block).mpr
    exact allZero block.atomicDefect (List.mem_map.mpr
      ⟨block, blockMem, rfl⟩)

@[simp]
theorem convert_view {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (intervalGap : ℤ) :
    (state.convert blockId intervalGap).view = state.view :=
  rfl

@[simp]
theorem convert_value {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (intervalGap : ℤ) :
    (state.convert blockId intervalGap).value = state.value :=
  rfl

@[simp]
theorem create_view {n : ℕ} (state : State n)
    (creator : Element n) (side : Side) :
    (state.create creator side).view = state.view :=
  rfl

@[simp]
theorem create_value {n : ℕ} (state : State n)
    (creator : Element n) (side : Side) :
    (state.create creator side).value = state.value :=
  rfl

@[simp]
theorem split_view {n : ℕ} (state : State n)
    (sourceId : Interface.BlockId) (source : Block n)
    (prefixLength : ℕ) (prefixGap suffixGap : ℤ) :
    (state.split sourceId source prefixLength
      prefixGap suffixGap).view = state.view :=
  rfl

@[simp]
theorem split_value {n : ℕ} (state : State n)
    (sourceId : Interface.BlockId) (source : Block n)
    (prefixLength : ℕ) (prefixGap suffixGap : ℤ) :
    (state.split sourceId source prefixLength
      prefixGap suffixGap).value = state.value :=
  rfl

private theorem convertAndCreate_atomicDefect_add_one_aux {n : ℕ}
    (blocks : List (Block n)) (blockId : Interface.BlockId)
    (block : Block n) (intervalGap : ℤ)
    (found : blocks[blockId]? = some block)
    (growing : block.mode = .growing)
    (nonempty : block.elements ≠ []) :
    ((((blocks.modify blockId fun current =>
          current.converted intervalGap) ++
        [Block.emptyGrowing block.creator block.side]).map
          Block.atomicDefect).sum) + 1 =
      (blocks.map Block.atomicDefect).sum := by
  induction blocks generalizing blockId block with
  | nil =>
      simp at found
  | cons head tail ih =>
      cases blockId with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst block
          cases elementsEq : head.elements with
          | nil =>
              exact False.elim (nonempty elementsEq)
          | cons element elements =>
              simp [Block.converted, Block.emptyGrowing,
                Block.atomicDefect, growing, elementsEq,
                Nat.add_assoc, Nat.add_comm]
      | succ blockId =>
          simp only [List.getElem?_cons_succ] at found
          rw [List.modify_succ_cons]
          have tailEq :=
            ih blockId block found growing nonempty
          simp only [List.map_append, List.map_cons,
            List.sum_append, List.sum_cons]
          simp [Block.emptyGrowing, Block.atomicDefect] at tailEq ⊢
          omega

/-- Convert-and-replace strictly decreases the global atomic defect. -/
theorem convertAndCreate_atomicDefect_lt {n : ℕ}
    (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (intervalGap : ℤ)
    (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing)
    (nonempty : block.elements ≠ []) :
    ((state.convert blockId intervalGap).create
        block.creator block.side).atomicDefect <
      state.atomicDefect := by
  have defectEq :=
    convertAndCreate_atomicDefect_add_one_aux state.blocks blockId block
      intervalGap found growing nonempty
  change
    ((((state.blocks.modify blockId fun current =>
          current.converted intervalGap) ++
        [Block.emptyGrowing block.creator block.side]).map
          Block.atomicDefect).sum) <
      (state.blocks.map Block.atomicDefect).sum
  omega

private theorem splitHead_atomicDefect_add_one_aux {n : ℕ}
    (blocks : List (Block n)) (sourceId : Interface.BlockId)
    (source : Block n) (head : Element n) (tail : List (Element n))
    (prefixGap suffixGap : ℤ)
    (found : blocks[sourceId]? = some source)
    (shrinking : source.mode = .shrinking)
    (elementsEq : source.elements = head :: tail)
    (tailNonempty : tail ≠ []) :
    (((State.splitBlocks blocks sourceId source 1
          prefixGap suffixGap).map Block.atomicDefect).sum) + 1 =
      (blocks.map Block.atomicDefect).sum := by
  induction blocks generalizing sourceId source with
  | nil =>
      simp at found
  | cons first rest ih =>
      cases sourceId with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst source
          cases tail with
          | nil =>
              simp at tailNonempty
          | cons second remaining =>
              simp [State.splitBlocks, Block.emptiedAfterSplit,
                Block.splitPrefix, Block.splitSuffix,
                Block.atomicDefect, shrinking, elementsEq,
                Nat.add_assoc, Nat.add_comm]
      | succ sourceId =>
          simp only [List.getElem?_cons_succ] at found
          have restEq :=
            ih sourceId source found
              shrinking elementsEq
          simp only [State.splitBlocks, List.modify_succ_cons,
            List.map_append, List.map_cons,
            List.sum_append, List.sum_cons] at restEq ⊢
          omega

/-- Splitting a non-singleton shrinking head strictly decreases the defect. -/
theorem splitHead_atomicDefect_lt {n : ℕ}
    (state : State n) (sourceId : Interface.BlockId)
    (source : Block n) (head : Element n) (tail : List (Element n))
    (prefixGap suffixGap : ℤ)
    (found : state.blocks[sourceId]? = some source)
    (shrinking : source.mode = .shrinking)
    (elementsEq : source.elements = head :: tail)
    (tailNonempty : tail ≠ []) :
    (state.split sourceId source 1 prefixGap suffixGap).atomicDefect <
      state.atomicDefect := by
  have defectEq :=
    splitHead_atomicDefect_add_one_aux state.blocks sourceId source
      head tail prefixGap suffixGap found shrinking elementsEq tailNonempty
  change
    (((State.splitBlocks state.blocks sourceId source 1
          prefixGap suffixGap).map Block.atomicDefect).sum) <
      (state.blocks.map Block.atomicDefect).sum
  omega

private theorem split_allElements_perm_aux {n : ℕ}
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
  | cons first rest ih =>
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
            (ih sourceId source found).append_left first.elements

/-- Splitting only repartitions the selected payload. -/
theorem split_allElements_perm {n : ℕ}
    (state : State n) (sourceId : Interface.BlockId)
    (source : Block n) (prefixLength : ℕ)
    (prefixGap suffixGap : ℤ)
    (found : state.blocks[sourceId]? = some source) :
    (state.split sourceId source prefixLength
      prefixGap suffixGap).allElements.Perm state.allElements := by
  exact split_allElements_perm_aux state.blocks sourceId source
    prefixLength prefixGap suffixGap found

end State

/-- The output of the terminating structural core, before value repair. -/
structure ShiftAtomicizationCore {n : ℕ}
    (params : Interface.Parameters) (initial : State n) where
  events : List (Event n)
  final : State n
  trace : Trace params initial events final
  totalInserts_eq_zero :
    Interface.totalInserts (eraseOperations events) = 0
  totalIncreases_eq_zero :
    Interface.totalIncreases (eraseOperations events) = 0
  shiftAtomic : final.ShiftAtomic
  view_eq : final.view = initial.view
  value_eq : final.value = initial.value
  allElements_perm : final.allElements.Perm initial.allElements
  oneGrowingPerSide : final.OneGrowingPerSide

namespace State

private theorem getElem_modify_append_of_lt
    {α : Type*} (values : List α) (index : ℕ)
    (update : α → α) (replacement : α) (queried : ℕ)
    (queriedLt : queried < values.length) :
    ((values.modify index update) ++ [replacement])[queried]'(by
        simp only [List.length_append, List.length_modify,
          List.length_singleton]
        omega) =
      if index = queried then update values[queried] else values[queried] := by
  rw [List.getElem_append_left (by simpa using queriedLt)]
  exact List.getElem_modify update index values queried
    (by simpa using queriedLt)

private theorem getElem_modify_append_last
    {α : Type*} (values : List α) (index : ℕ)
    (update : α → α) (replacement : α) :
    ((values.modify index update) ++ [replacement])[values.length] =
      replacement := by
  have atEnd :=
    List.getElem_concat_length
      (l := values.modify index update) (a := replacement) rfl
      (by simp)
  simpa only [List.length_modify] using atEnd

private theorem existsUnique_get_modify_append
    {α : Type*} (values : List α) (index : ℕ) (selected : α)
    (update : α → α) (replacement : α)
    (predicate : α → Prop)
    (found : values[index]? = some selected)
    (updatedFalse : ¬predicate (update selected))
    (replacementIff :
      predicate replacement ↔ predicate selected)
    (unique :
      ∃! id : Fin values.length, predicate (values.get id)) :
    ∃! id : Fin ((values.modify index update) ++ [replacement]).length,
      predicate (((values.modify index update) ++ [replacement]).get id) := by
  classical
  obtain ⟨selectedLt, selectedGetElem⟩ :=
    List.getElem?_eq_some_iff.mp found
  let selectedId : Fin values.length := ⟨index, selectedLt⟩
  have selectedGet : values.get selectedId = selected := by
    rw [List.get_eq_getElem]
    exact selectedGetElem
  obtain ⟨oldId, oldProperty, oldUnique⟩ := unique
  by_cases selectedProperty : predicate selected
  · let replacementId :
        Fin ((values.modify index update) ++ [replacement]).length :=
      ⟨values.length, by simp⟩
    have replacementProperty :
        predicate
          (((values.modify index update) ++ [replacement]).get
            replacementId) := by
      change
        predicate
          (((values.modify index update) ++ [replacement])[values.length])
      rw [getElem_modify_append_last]
      exact replacementIff.mpr selectedProperty
    refine ⟨replacementId, replacementProperty, ?_⟩
    intro candidate candidateProperty
    apply Fin.ext
    change candidate.val = values.length
    by_contra candidateNe
    have candidateLt : candidate.val < values.length := by
      have candidateBound := candidate.isLt
      simp only [List.length_append, List.length_modify,
        List.length_singleton] at candidateBound
      omega
    let oldCandidate : Fin values.length :=
      ⟨candidate.val, candidateLt⟩
    change
      predicate
        (((values.modify index update) ++ [replacement])[candidate.val])
      at candidateProperty
    rw [getElem_modify_append_of_lt values index update replacement
      candidate.val candidateLt] at candidateProperty
    split at candidateProperty
    next selectedIndex =>
      have selectedAt :
          values[candidate.val] = selected := by
        simpa only [selectedIndex] using selectedGetElem
      rw [selectedAt] at candidateProperty
      exact False.elim (updatedFalse candidateProperty)
    next notSelectedIndex =>
      have oldCandidateProperty :
          predicate (values.get oldCandidate) := by
        simpa [oldCandidate, List.get_eq_getElem] using candidateProperty
      have oldCandidateEq :
          oldCandidate = oldId :=
        oldUnique oldCandidate oldCandidateProperty
      have selectedIdEq :
          selectedId = oldId :=
        oldUnique selectedId (by
          change predicate (values.get selectedId)
          rw [selectedGet]
          exact selectedProperty)
      have candidateEqSelected :
          oldCandidate = selectedId :=
        oldCandidateEq.trans selectedIdEq.symm
      exact notSelectedIndex (by
        simpa [oldCandidate, selectedId] using
          congrArg Fin.val candidateEqSelected.symm)
  · have oldIndexNe : oldId.val ≠ index := by
      intro oldIndexEq
      have oldIdEq : oldId = selectedId := by
        apply Fin.ext
        exact oldIndexEq
      rw [oldIdEq, selectedGet] at oldProperty
      exact selectedProperty oldProperty
    let survivingId :
        Fin ((values.modify index update) ++ [replacement]).length :=
      ⟨oldId.val, by
        simp only [List.length_append, List.length_modify,
          List.length_singleton]
        omega⟩
    have survivingProperty :
        predicate
          (((values.modify index update) ++ [replacement]).get
            survivingId) := by
      change
        predicate
          (((values.modify index update) ++ [replacement])[oldId.val])
      rw [getElem_modify_append_of_lt values index update replacement
        oldId.val oldId.isLt, if_neg]
      · simpa [List.get_eq_getElem] using oldProperty
      · exact fun indexEq => oldIndexNe indexEq.symm
    refine ⟨survivingId, survivingProperty, ?_⟩
    intro candidate candidateProperty
    apply Fin.ext
    change candidate.val = oldId.val
    by_cases candidateLt : candidate.val < values.length
    · let oldCandidate : Fin values.length :=
        ⟨candidate.val, candidateLt⟩
      change
        predicate
          (((values.modify index update) ++ [replacement])[candidate.val])
        at candidateProperty
      rw [getElem_modify_append_of_lt values index update replacement
        candidate.val candidateLt] at candidateProperty
      split at candidateProperty
      next selectedIndex =>
        have selectedAt :
            values[candidate.val] = selected := by
          simpa only [selectedIndex] using selectedGetElem
        rw [selectedAt] at candidateProperty
        exact False.elim (updatedFalse candidateProperty)
      next _ =>
        have oldCandidateProperty :
            predicate (values.get oldCandidate) := by
          simpa [oldCandidate, List.get_eq_getElem] using
            candidateProperty
        exact congrArg Fin.val
          (oldUnique oldCandidate oldCandidateProperty)
    · have candidateEqLast : candidate.val = values.length := by
        have candidateBound := candidate.isLt
        simp only [List.length_append, List.length_modify,
          List.length_singleton] at candidateBound
        omega
      have replacementProperty : predicate replacement := by
        change
          predicate
            (((values.modify index update) ++ [replacement])[candidate.val])
          at candidateProperty
        simpa only [candidateEqLast, getElem_modify_append_last] using
          candidateProperty
      exact False.elim
        (selectedProperty (replacementIff.mp replacementProperty))

private theorem existsUnique_get_append_of_false
    {α : Type*} (values : List α) (replacement : α)
    (predicate : α → Prop) (replacementFalse : ¬predicate replacement)
    (unique :
      ∃! id : Fin values.length, predicate (values.get id)) :
    ∃! id : Fin (values ++ [replacement]).length,
      predicate ((values ++ [replacement]).get id) := by
  classical
  obtain ⟨oldId, oldProperty, oldUnique⟩ := unique
  let survivingId : Fin (values ++ [replacement]).length :=
    ⟨oldId.val, by simp; omega⟩
  have survivingProperty :
      predicate ((values ++ [replacement]).get survivingId) := by
    change predicate ((values ++ [replacement])[oldId.val])
    rw [List.getElem_append_left oldId.isLt]
    simpa [List.get_eq_getElem] using oldProperty
  refine ⟨survivingId, survivingProperty, ?_⟩
  intro candidate candidateProperty
  apply Fin.ext
  change candidate.val = oldId.val
  by_cases candidateLt : candidate.val < values.length
  · let oldCandidate : Fin values.length :=
      ⟨candidate.val, candidateLt⟩
    have oldCandidateProperty :
        predicate (values.get oldCandidate) := by
      change predicate ((values ++ [replacement])[candidate.val])
        at candidateProperty
      rw [List.getElem_append_left candidateLt] at candidateProperty
      simpa [oldCandidate, List.get_eq_getElem] using candidateProperty
    exact congrArg Fin.val
      (oldUnique oldCandidate oldCandidateProperty)
  · have candidateEqLast : candidate.val = values.length := by
      have candidateBound := candidate.isLt
      simp only [List.length_append, List.length_singleton]
        at candidateBound
      omega
    have atReplacement : predicate replacement := by
      change predicate ((values ++ [replacement])[candidate.val])
        at candidateProperty
      simpa only [candidateEqLast,
        List.getElem_concat_length] using candidateProperty
    exact False.elim (replacementFalse atReplacement)

/-- Convert-and-replace preserves the unique growing owner-side placements. -/
theorem convertAndCreate_oneGrowingPerSide {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (blockId : Interface.BlockId) (block : Block n)
    (intervalGap : ℤ) (valid : state.Valid params)
    (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing)
    (oneGrowing : state.OneGrowingPerSide) :
    ((state.convert blockId intervalGap).create
      block.creator block.side).OneGrowingPerSide := by
  have blockMember : block ∈ state.blocks :=
    List.mem_iff_getElem?.mpr ⟨blockId, found⟩
  have ownerEq :
      block.owner = block.creator :=
    (valid.2 block blockMember).owner_eq_creator_of_growing growing
  intro owner childSide
  change
    ∃! id :
        Fin ((state.blocks.modify blockId fun current =>
          current.converted intervalGap) ++
            [Block.emptyGrowing block.creator block.side]).length,
      let current :=
        ((state.blocks.modify blockId fun item =>
          item.converted intervalGap) ++
            [Block.emptyGrowing block.creator block.side]).get id
      current.mode = .growing ∧
        current.owner = owner ∧ current.side = childSide
  apply existsUnique_get_modify_append state.blocks blockId block
    (fun current => current.converted intervalGap)
    (Block.emptyGrowing block.creator block.side)
    (fun current =>
      current.mode = .growing ∧
        current.owner = owner ∧ current.side = childSide)
    found
  · simp [Block.converted]
  · simp [Block.emptyGrowing, growing, ownerEq]
  · exact oneGrowing owner childSide

/-- A split introduces only shrinking blocks, so growing uniqueness survives. -/
theorem split_oneGrowingPerSide {n : ℕ}
    (state : State n) (sourceId : Interface.BlockId)
    (source : Block n) (prefixLength : ℕ)
    (prefixGap suffixGap : ℤ)
    (found : state.blocks[sourceId]? = some source)
    (shrinking : source.mode = .shrinking)
    (oneGrowing : state.OneGrowingPerSide) :
    (state.split sourceId source prefixLength
      prefixGap suffixGap).OneGrowingPerSide := by
  intro owner childSide
  let predicate : Block n → Prop :=
    fun current =>
      current.mode = .growing ∧
        current.owner = owner ∧ current.side = childSide
  have afterPrefixUnique :
      ∃! id :
          Fin ((state.blocks.modify sourceId
              Block.emptiedAfterSplit) ++
            [source.splitPrefix prefixLength prefixGap]).length,
        predicate
          (((state.blocks.modify sourceId
              Block.emptiedAfterSplit) ++
            [source.splitPrefix prefixLength prefixGap]).get id) := by
    apply existsUnique_get_modify_append state.blocks sourceId source
      Block.emptiedAfterSplit
      (source.splitPrefix prefixLength prefixGap)
      predicate found
    · simp [predicate, Block.emptiedAfterSplit, shrinking]
    · simp [predicate, Block.splitPrefix, shrinking]
    · exact oneGrowing owner childSide
  have afterSuffixUnique :=
    existsUnique_get_append_of_false
      ((state.blocks.modify sourceId Block.emptiedAfterSplit) ++
        [source.splitPrefix prefixLength prefixGap])
      (source.splitSuffix prefixLength suffixGap)
      predicate
      (by simp [predicate, Block.splitSuffix, shrinking])
      afterPrefixUnique
  change
    ∃! id :
        Fin ((state.blocks.modify sourceId
            Block.emptiedAfterSplit) ++
          [source.splitPrefix prefixLength prefixGap,
            source.splitSuffix prefixLength suffixGap]).length,
      predicate
        (((state.blocks.modify sourceId
            Block.emptiedAfterSplit) ++
          [source.splitPrefix prefixLength prefixGap,
            source.splitSuffix prefixLength suffixGap]).get id)
  have blocksEq :
      (state.blocks.modify sourceId Block.emptiedAfterSplit) ++
          [source.splitPrefix prefixLength prefixGap,
            source.splitSuffix prefixLength suffixGap] =
        ((state.blocks.modify sourceId Block.emptiedAfterSplit) ++
            [source.splitPrefix prefixLength prefixGap]) ++
          [source.splitSuffix prefixLength suffixGap] := by
    simp
  rw [blocksEq]
  exact afterSuffixUnique

/--
Every transient-valid state can be structurally atomized.

The recursion is on `atomicDefect`.  Its growing branch is exactly
`exists_convertAndCreate_trace`; its shrinking branch is exactly
`exists_splitHead_trace`.
-/
theorem exists_shiftAtomicizationCore {n : ℕ}
    {params : Interface.Parameters} (initial : State n)
    (valid : initial.Valid params)
    (oneGrowing : initial.OneGrowingPerSide) :
    Nonempty (ShiftAtomicizationCore params initial) := by
  classical
  generalize defectEq : initial.atomicDefect = defect
  induction defect using Nat.strong_induction_on generalizing initial with
  | h defect ih =>
      by_cases atomic : initial.ShiftAtomic
      · exact ⟨{
          events := []
          final := initial
          trace := Trace.nil valid
          totalInserts_eq_zero := by
            simp [eraseOperations, Interface.totalInserts]
          totalIncreases_eq_zero := by
            simp [eraseOperations, Interface.totalIncreases]
          shiftAtomic := atomic
          view_eq := rfl
          value_eq := rfl
          allElements_perm := List.Perm.refl _
          oneGrowingPerSide := oneGrowing
        }⟩
      · rw [State.ShiftAtomic] at atomic
        push Not at atomic
        obtain ⟨block, blockMem, blockNonatomic⟩ := atomic
        obtain ⟨blockId, found⟩ :=
          List.mem_iff_getElem?.mp blockMem
        cases modeEq : block.mode with
        | growing =>
            have nonempty : block.elements ≠ [] :=
              blockNonatomic.1 modeEq
            obtain ⟨intervalGap, prefixTrace⟩ :=
              initial.exists_convertAndCreate_trace
                blockId block valid found modeEq
            let middle :=
              (initial.convert blockId intervalGap).create
                block.creator block.side
            have middleLt :
                middle.atomicDefect < defect := by
              rw [← defectEq]
              exact initial.convertAndCreate_atomicDefect_lt
                blockId block intervalGap found modeEq nonempty
            obtain ⟨suffix⟩ :=
              ih middle.atomicDefect middleLt middle
                prefixTrace.final_valid
                (initial.convertAndCreate_oneGrowingPerSide
                  blockId block intervalGap valid found modeEq oneGrowing)
                rfl
            refine ⟨{
              events :=
                [.operation (.convert blockId),
                  .operation (.create block.creator)] ++ suffix.events
              final := suffix.final
              trace := prefixTrace.append suffix.trace
              totalInserts_eq_zero := by
                simpa [eraseOperations, Event.operations,
                  Interface.totalInserts,
                  Interface.Operation.insertCount] using
                    suffix.totalInserts_eq_zero
              totalIncreases_eq_zero := by
                simpa [eraseOperations, Event.operations,
                  Interface.totalIncreases,
                  Interface.Operation.increaseCount] using
                    suffix.totalIncreases_eq_zero
              shiftAtomic := suffix.shiftAtomic
              view_eq := suffix.view_eq.trans ?_
              value_eq := suffix.value_eq.trans ?_
              allElements_perm := suffix.allElements_perm.trans ?_
              oneGrowingPerSide := suffix.oneGrowingPerSide
            }⟩
            · simp [middle]
            · simp [middle]
            · have middleElements :
                  middle.allElements = initial.allElements := by
                simp [middle]
              rw [middleElements]
        | shrinking =>
            have badShape :
                ¬(block.elements = [] ∨
                  ∃ element, block.elements = [element]) := by
              have shrinkingBad := blockNonatomic.2 modeEq
              intro shape
              rcases shape with empty | ⟨element, singleton⟩
              · exact shrinkingBad.1 empty
              · exact shrinkingBad.2 element singleton
            cases elementsEq : block.elements with
            | nil =>
                exact False.elim (badShape (Or.inl elementsEq))
            | cons head tail =>
                have tailNonempty : tail ≠ [] := by
                  intro tailEmpty
                  apply badShape
                  right
                  refine ⟨head, ?_⟩
                  simp [elementsEq, tailEmpty]
                obtain ⟨suffixGap, prefixTrace, _prefixElements,
                    _suffixElements, _suffixShorter⟩ :=
                  initial.exists_splitHead_trace
                    blockId block head tail valid found modeEq elementsEq
                      tailNonempty
                let middle :=
                  initial.split blockId block 1
                    (initial.view.rawGap head) suffixGap
                have middleLt :
                    middle.atomicDefect < defect := by
                  rw [← defectEq]
                  exact initial.splitHead_atomicDefect_lt blockId block
                    head tail (initial.view.rawGap head) suffixGap
                    found modeEq elementsEq tailNonempty
                obtain ⟨suffix⟩ :=
                  ih middle.atomicDefect middleLt middle
                    prefixTrace.final_valid
                    (initial.split_oneGrowingPerSide blockId block 1
                      (initial.view.rawGap head) suffixGap found modeEq
                      oneGrowing)
                    rfl
                refine ⟨{
                  events :=
                    [.operation (.split blockId 1)] ++ suffix.events
                  final := suffix.final
                  trace := prefixTrace.append suffix.trace
                  totalInserts_eq_zero := by
                    simpa [eraseOperations, Event.operations,
                      Interface.totalInserts,
                      Interface.Operation.insertCount] using
                        suffix.totalInserts_eq_zero
                  totalIncreases_eq_zero := by
                    simpa [eraseOperations, Event.operations,
                      Interface.totalIncreases,
                      Interface.Operation.increaseCount] using
                        suffix.totalIncreases_eq_zero
                  shiftAtomic := suffix.shiftAtomic
                  view_eq := suffix.view_eq.trans ?_
                  value_eq := suffix.value_eq.trans ?_
                  allElements_perm := suffix.allElements_perm.trans ?_
                  oneGrowingPerSide := suffix.oneGrowingPerSide
                }⟩
                · simp [middle]
                · simp [middle]
                · exact initial.split_allElements_perm blockId block 1
                    (initial.view.rawGap head) suffixGap found

/-- Completeness is invariant under a payload permutation at a fixed view. -/
theorem ShiftAtomicizationCore.complete {n : ℕ}
    {params : Interface.Parameters} {initial : State n}
    (core : ShiftAtomicizationCore params initial)
    (complete : initial.Complete) :
    core.final.Complete := by
  intro element
  have assignedIff :
      element ∈ core.final.allElements ↔
        element ∈ initial.allElements :=
    core.allElements_perm.mem_iff
  rw [assignedIff, complete element, core.view_eq]

/--
The structural atomicizer required by the comparison and splay realizers.

It is unconditional in the interface parameters: stability supplies validity,
completeness, and growing uniqueness, while the terminating core uses only
legal convert/create and split operations.
-/
theorem structuralShiftAtomicizer
    (params : Interface.Parameters) :
    StructuralShiftAtomicizer params := by
  intro n initial stable
  obtain ⟨core⟩ :=
    initial.exists_shiftAtomicizationCore
      stable.valid stable.2.2.2.1
  exact ⟨{
    events := core.events
    final := core.final
    trace := core.trace
    totalInserts_eq_zero := core.totalInserts_eq_zero
    totalIncreases_eq_zero := core.totalIncreases_eq_zero
    shiftAtomic := core.shiftAtomic
    view_eq := core.view_eq
    value_eq := core.value_eq
    complete := State.ShiftAtomicizationCore.complete core stable.2.1
    oneGrowingPerSide := core.oneGrowingPerSide
  }⟩

end State

end Splay.Lazy
