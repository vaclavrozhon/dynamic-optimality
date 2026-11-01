import Splay.Lazy.PreparedComparisonRotation

namespace Splay.Lazy

open Splay.Rank

namespace State

/--
A shift-independent normal form strong enough for every comparison rotation:
growing blocks are empty, while shrinking blocks are empty or singletons.

Historical empty shrinking blocks are intentionally retained.  Singleton
shrinking blocks are uniform for every pointwise rank shift, so this normal
form removes the last shift-sector side condition from preparation.
-/
def ShiftAtomic {n : ℕ} (state : State n) : Prop :=
  ∀ block ∈ state.blocks,
    (block.mode = .growing ∧ block.elements = []) ∨
      (block.mode = .shrinking ∧
        (block.elements = [] ∨
          ∃ element, block.elements = [element]))

/-- Canonical block shift associated with a shift-atomic state. -/
def shiftAtomicBlockShift {n : ℕ}
    (elementShift : Element n → ℤ) (block : Block n) : ℤ :=
  match block.mode with
  | .growing => 0
  | .shrinking =>
      match block.elements with
      | [] => 0
      | element :: _ =>
          elementShift element - elementShift block.owner

/--
Reattach a shift-atomic block to a new heap view.

Growing and empty shrinking blocks are left literally unchanged.  A nonempty
shrinking block is necessarily a singleton under `ShiftAtomic`; its owner,
side, and attained signed minimum are therefore determined by its sole
element.  The default owner is used only in the impossible case where that
assigned element is the new root.
-/
noncomputable def rebaseShiftAtomicBlock {n : ℕ}
    (afterView : HeapView n) (block : Block n) : Block n :=
  match block.mode with
  | .growing => block
  | .shrinking =>
      match block.elements with
      | [] => block
      | element :: _ =>
          block.withPlacement
            ((afterView.parent element).getD afterView.root)
            (afterView.side element)
            (afterView.rawGap element)

@[simp]
theorem rebaseShiftAtomicBlock_toInterface {n : ℕ}
    (afterView : HeapView n) (block : Block n) :
    (rebaseShiftAtomicBlock afterView block).toInterface =
      block.toInterface := by
  cases modeEq : block.mode <;>
    cases elementsEq : block.elements <;>
    simp [rebaseShiftAtomicBlock, modeEq, elementsEq]

@[simp]
theorem rebaseShiftAtomicBlock_mode {n : ℕ}
    (afterView : HeapView n) (block : Block n) :
    (rebaseShiftAtomicBlock afterView block).mode = block.mode := by
  cases modeEq : block.mode <;>
    cases elementsEq : block.elements <;>
    simp [rebaseShiftAtomicBlock, modeEq, elementsEq, Block.withPlacement]

@[simp]
theorem rebaseShiftAtomicBlock_elements {n : ℕ}
    (afterView : HeapView n) (block : Block n) :
    (rebaseShiftAtomicBlock afterView block).elements = block.elements := by
  cases modeEq : block.mode <;>
    cases elementsEq : block.elements <;>
    simp [rebaseShiftAtomicBlock, modeEq, elementsEq, Block.withPlacement]

theorem rebaseShiftAtomicBlock_eq_of_growing {n : ℕ}
    (afterView : HeapView n) {block : Block n}
    (growing : block.mode = .growing) :
    rebaseShiftAtomicBlock afterView block = block := by
  simp [rebaseShiftAtomicBlock, growing]

theorem rebaseShiftAtomicBlock_eq_of_shrinking_empty {n : ℕ}
    (afterView : HeapView n) {block : Block n}
    (shrinking : block.mode = .shrinking)
    (empty : block.elements = []) :
    rebaseShiftAtomicBlock afterView block = block := by
  simp [rebaseShiftAtomicBlock, shrinking, empty]

/-- Simultaneously rebase every shift-atomic block to a new heap view. -/
noncomputable def rebaseShiftAtomic {n : ℕ}
    (state : State n) (afterView : HeapView n) : State n where
  view := afterView
  blocks := state.blocks.map (rebaseShiftAtomicBlock afterView)
  value := state.value

@[simp]
theorem rebaseShiftAtomic_view {n : ℕ}
    (state : State n) (afterView : HeapView n) :
    (state.rebaseShiftAtomic afterView).view = afterView :=
  rfl

@[simp]
theorem rebaseShiftAtomic_toInterface {n : ℕ}
    (state : State n) (afterView : HeapView n) :
    (state.rebaseShiftAtomic afterView).toInterface =
      state.toInterface := by
  cases state with
  | mk view blocks value =>
      simp [rebaseShiftAtomic, State.toInterface, Function.comp_def]

@[simp]
theorem rebaseShiftAtomic_allElements {n : ℕ}
    (state : State n) (afterView : HeapView n) :
    (state.rebaseShiftAtomic afterView).allElements =
      state.allElements := by
  cases state with
  | mk view blocks value =>
      simp [rebaseShiftAtomic, State.allElements, List.flatMap_map]

@[simp]
theorem rebaseShiftAtomic_blocks_length {n : ℕ}
    (state : State n) (afterView : HeapView n) :
    (state.rebaseShiftAtomic afterView).blocks.length =
      state.blocks.length := by
  simp [rebaseShiftAtomic]

namespace ShiftAtomic

private theorem singleton_isSegment_of_mem
    {α : Type*} {element : α} {whole : List α}
    (member : element ∈ whole) :
    IsSegment [element] whole := by
  rw [List.mem_iff_append] at member
  obtain ⟨front, back, rfl⟩ := member
  exact ⟨front, back, by simp⟩

/-- Rebasing preserves the shift-independent atomic block shape. -/
theorem rebase
    {n : ℕ} {state : State n}
    (atomic : state.ShiftAtomic)
    (afterView : HeapView n) :
    (state.rebaseShiftAtomic afterView).ShiftAtomic := by
  intro afterBlock afterBlockMem
  simp only [rebaseShiftAtomic] at afterBlockMem
  obtain ⟨beforeBlock, beforeBlockMem, rfl⟩ :=
    List.mem_map.mp afterBlockMem
  rcases atomic beforeBlock beforeBlockMem with growing | shrinking
  · left
    simpa [rebaseShiftAtomicBlock, growing.1] using growing
  · right
    simpa only [rebaseShiftAtomicBlock_mode,
      rebaseShiftAtomicBlock_elements] using shrinking

/--
The bulk rebase is transient-valid whenever the new heap root is unassigned.

This is the exact condition that rules out the default-owner branch in
`rebaseShiftAtomicBlock`: every assigned singleton remains a non-root vertex
and therefore has a genuine parent in the new view.
-/
theorem rebase_valid_of_root_not_mem
    {n : ℕ} {state : State n} {afterView : HeapView n}
    {params : Interface.Parameters}
    (atomic : state.ShiftAtomic)
    (valid : state.Valid params)
    (rootNotMem : afterView.root ∉ state.allElements) :
    (state.rebaseShiftAtomic afterView).Valid params := by
  constructor
  · simpa only [rebaseShiftAtomic_toInterface] using valid.toInterface
  · intro afterBlock afterBlockMem
    simp only [rebaseShiftAtomic] at afterBlockMem
    obtain ⟨beforeBlock, beforeBlockMem, rfl⟩ :=
      List.mem_map.mp afterBlockMem
    have beforeStructural :=
      valid.2 beforeBlock beforeBlockMem
    rcases atomic beforeBlock beforeBlockMem with growing | shrinking
    · have rebasedEq :
          rebaseShiftAtomicBlock afterView beforeBlock = beforeBlock :=
        rebaseShiftAtomicBlock_eq_of_growing afterView growing.1
      rw [rebasedEq, rebaseShiftAtomic_allElements]
      exact Block.structurallyValid_growing
        growing.1
        (beforeStructural.owner_eq_creator_of_growing growing.1)
        (by rw [growing.2]; exact IsSegment.nil _)
        (beforeStructural.growing_intervalGap_eq_zero growing.1)
        (by
          intro element elementMem
          rw [growing.2] at elementMem
          simp at elementMem)
    · rcases shrinking.2 with empty | ⟨element, elementsEq⟩
      · have rebasedEq :
            rebaseShiftAtomicBlock afterView beforeBlock = beforeBlock :=
          rebaseShiftAtomicBlock_eq_of_shrinking_empty
            afterView shrinking.1 empty
        rw [rebasedEq, rebaseShiftAtomic_allElements]
        apply Block.structurallyValid_empty_shrinking
          shrinking.1 empty
        have gapValid := beforeStructural.2.2
        simp only [Block.GapValid, shrinking.1] at gapValid
        rcases gapValid with emptyCase | nonemptyCase
        · exact emptyCase.2
        · exact False.elim (nonemptyCase.1 empty)
      · have assignedBefore : element ∈ state.allElements :=
          State.mem_allElements_iff.mpr
            ⟨beforeBlock, beforeBlockMem, by simp [elementsEq]⟩
        have notRootAfter : element ≠ afterView.root := by
          intro elementRoot
          apply rootNotMem
          simpa only [elementRoot] using assignedBefore
        cases parentEq : afterView.parent element with
        | none =>
            exact False.elim
              (afterView.parent_ne_none_of_ne_root
                notRootAfter parentEq)
        | some owner =>
            have rebasedEq :
                rebaseShiftAtomicBlock afterView beforeBlock =
                  beforeBlock.withPlacement owner
                    (afterView.side element)
                    (afterView.rawGap element) := by
              simp [rebaseShiftAtomicBlock, shrinking.1,
                elementsEq, parentEq]
            rw [rebasedEq]
            have assignedAfter :
                element ∈
                  (state.rebaseShiftAtomic afterView).allElements := by
              simpa only [rebaseShiftAtomic_allElements] using assignedBefore
            have topDownMem :
                element ∈
                  afterView.topDown owner (afterView.side element) :=
              afterView.mem_topDown_iff.mpr ⟨parentEq, rfl⟩
            have attachedMem :
                element ∈
                  afterView.attachedTopDown
                    (state.rebaseShiftAtomic afterView).allElements
                    owner (afterView.side element) :=
              afterView.mem_attachedTopDown_iff.mpr
                ⟨topDownMem, assignedAfter⟩
            refine ⟨?_, ?_, ?_⟩
            · simpa [Block.withPlacement, elementsEq] using
                singleton_isSegment_of_mem attachedMem
            · intro growingMode
              simp [Block.withPlacement, shrinking.1] at growingMode
            · apply Block.singleton_shrinking_gapValid
                afterView
                (beforeBlock.withPlacement owner
                  (afterView.side element)
                  (afterView.rawGap element))
                (by simp [Block.withPlacement, shrinking.1])
                element
                (by simp [Block.withPlacement, elementsEq])
                (by simp [Block.withPlacement])

/-- Preserving the heap root is a convenient sufficient rebase condition. -/
theorem rebase_valid
    {n : ℕ} {state : State n} {afterView : HeapView n}
    {params : Interface.Parameters}
    (atomic : state.ShiftAtomic)
    (valid : state.Valid params)
    (rootEq : afterView.root = state.view.root) :
    (state.rebaseShiftAtomic afterView).Valid params := by
  apply atomic.rebase_valid_of_root_not_mem valid
  intro rootMem
  apply valid.root_not_mem
  simpa only [rootEq] using rootMem

/-- Preserving the heap root preserves completeness of the block partition. -/
theorem rebase_complete
    {n : ℕ} {state : State n} {afterView : HeapView n}
    (complete : state.Complete)
    (rootEq : afterView.root = state.view.root) :
    (state.rebaseShiftAtomic afterView).Complete := by
  intro element
  rw [rebaseShiftAtomic_allElements, complete element]
  change
    state.view.parent element ≠ none ↔
      afterView.parent element ≠ none
  constructor
  · intro beforeParent afterParentNone
    have elementRootAfter :
        element = afterView.root :=
      afterView.parent_eq_none element afterParentNone
    apply beforeParent
    simpa only [elementRootAfter, rootEq] using state.view.root_parent
  · intro afterParent beforeParentNone
    have elementRootBefore :
        element = state.view.root :=
      state.view.parent_eq_none element beforeParentNone
    apply afterParent
    have elementRootAfter :
        element = afterView.root :=
      elementRootBefore.trans rootEq.symm
    simpa only [elementRootAfter] using afterView.root_parent

/-- Rebasing changes no growing block, hence preserves its unique identifier. -/
theorem rebase_oneGrowingPerSide
    {n : ℕ} {state : State n}
    (afterView : HeapView n)
    (oneGrowing : state.OneGrowingPerSide) :
    (state.rebaseShiftAtomic afterView).OneGrowingPerSide := by
  intro owner childSide
  obtain ⟨beforeId, beforeProperty, beforeUnique⟩ :=
    oneGrowing owner childSide
  change
    (state.blocks.get beforeId).mode = .growing ∧
      (state.blocks.get beforeId).owner = owner ∧
        (state.blocks.get beforeId).side = childSide
    at beforeProperty
  let afterId :
      Fin (state.rebaseShiftAtomic afterView).blocks.length :=
    ⟨beforeId.val, by
      simpa only [rebaseShiftAtomic_blocks_length] using beforeId.isLt⟩
  refine ⟨afterId, ?_, ?_⟩
  · change
      ((state.rebaseShiftAtomic afterView).blocks.get afterId).mode =
          .growing ∧
        ((state.rebaseShiftAtomic afterView).blocks.get afterId).owner =
            owner ∧
          ((state.rebaseShiftAtomic afterView).blocks.get afterId).side =
            childSide
    have selectedEq :
        (state.rebaseShiftAtomic afterView).blocks.get afterId =
          state.blocks.get beforeId := by
      simp only [List.get_eq_getElem, rebaseShiftAtomic,
        List.getElem_map]
      apply rebaseShiftAtomicBlock_eq_of_growing
      simpa only [List.get_eq_getElem] using beforeProperty.1
    rw [selectedEq]
    exact beforeProperty
  · intro candidate candidateProperty
    let beforeCandidate : Fin state.blocks.length :=
      ⟨candidate.val, by
        simpa only [rebaseShiftAtomic_blocks_length] using candidate.isLt⟩
    change
      ((state.rebaseShiftAtomic afterView).blocks.get candidate).mode =
          .growing ∧
        ((state.rebaseShiftAtomic afterView).blocks.get candidate).owner =
            owner ∧
          ((state.rebaseShiftAtomic afterView).blocks.get candidate).side =
            childSide
      at candidateProperty
    have candidateGrowing :
        (state.blocks.get beforeCandidate).mode = .growing := by
      simpa [beforeCandidate, rebaseShiftAtomic] using candidateProperty.1
    have selectedEq :
        (state.rebaseShiftAtomic afterView).blocks.get candidate =
          state.blocks.get beforeCandidate := by
      simp only [List.get_eq_getElem, rebaseShiftAtomic,
        List.getElem_map]
      apply rebaseShiftAtomicBlock_eq_of_growing
      simpa only [List.get_eq_getElem] using candidateGrowing
    have beforeCandidateProperty :
        (state.blocks.get beforeCandidate).mode = .growing ∧
          (state.blocks.get beforeCandidate).owner = owner ∧
            (state.blocks.get beforeCandidate).side = childSide := by
      rw [← selectedEq]
      exact candidateProperty
    have beforeEq :
        beforeCandidate = beforeId :=
      beforeUnique beforeCandidate beforeCandidateProperty
    apply Fin.ext
    simpa [beforeCandidate, afterId] using congrArg Fin.val beforeEq

/-- Empty growing blocks are automatically topmost in every new view. -/
theorem rebase_growingTopmost
    {n : ℕ} {state : State n}
    (atomic : state.ShiftAtomic)
    (afterView : HeapView n) :
    (state.rebaseShiftAtomic afterView).GrowingTopmost := by
  intro afterId
  let beforeId : Fin state.blocks.length :=
    ⟨afterId.val, by
      simpa only [rebaseShiftAtomic_blocks_length] using afterId.isLt⟩
  change
    ((state.rebaseShiftAtomic afterView).blocks.get afterId).mode =
        .growing →
      ∃ suffix,
        afterView.topDown
            ((state.rebaseShiftAtomic afterView).blocks.get afterId).owner
            ((state.rebaseShiftAtomic afterView).blocks.get afterId).side =
          ((state.rebaseShiftAtomic afterView).blocks.get afterId).elements ++
            suffix
  intro afterGrowing
  have beforeGrowing :
      (state.blocks.get beforeId).mode = .growing := by
    simpa [beforeId, rebaseShiftAtomic] using afterGrowing
  have beforeMem :
      state.blocks.get beforeId ∈ state.blocks :=
    List.get_mem state.blocks beforeId
  rcases atomic (state.blocks.get beforeId) beforeMem with
      growing | shrinking
  · refine
      ⟨afterView.topDown
          (state.blocks.get beforeId).owner
          (state.blocks.get beforeId).side, ?_⟩
    have selectedEq :
        (state.rebaseShiftAtomic afterView).blocks.get afterId =
          state.blocks.get beforeId := by
      simp only [List.get_eq_getElem, rebaseShiftAtomic,
        List.getElem_map]
      apply rebaseShiftAtomicBlock_eq_of_growing
      simpa only [List.get_eq_getElem] using beforeGrowing
    rw [selectedEq, growing.2]
    simp
  · rw [beforeGrowing] at shrinking
    simp at shrinking

/--
Singleton shrinking blocks realize value one both before and after rebasing.
The old attained-minimum witness supplies the former fact; the new interval
gap is definitionally the singleton's new raw gap.
-/
theorem rebase_valuesRealizeGaps
    {n : ℕ} {state : State n} {afterView : HeapView n}
    {params : Interface.Parameters}
    (atomic : state.ShiftAtomic)
    (valid : state.Valid params)
    (values : state.ValuesRealizeGaps)
    (rootEq : afterView.root = state.view.root) :
    (state.rebaseShiftAtomic afterView).ValuesRealizeGaps := by
  constructor
  · change state.value afterView.root = 1
    rw [rootEq]
    exact values.1
  · intro afterBlock afterBlockMem element elementMem
    simp only [rebaseShiftAtomic] at afterBlockMem
    obtain ⟨beforeBlock, beforeBlockMem, rfl⟩ :=
      List.mem_map.mp afterBlockMem
    have beforeElementMem :
        element ∈ beforeBlock.elements := by
      simpa only [rebaseShiftAtomicBlock_elements] using elementMem
    rcases atomic beforeBlock beforeBlockMem with growing | shrinking
    · rw [growing.2] at beforeElementMem
      simp at beforeElementMem
    · rcases shrinking.2 with empty | ⟨singleton, elementsEq⟩
      · rw [empty] at beforeElementMem
        simp at beforeElementMem
      · have elementEq : element = singleton := by
          simpa [elementsEq] using beforeElementMem
        subst element
        have oldValue :=
          values.2 beforeBlock beforeBlockMem singleton
            (by simp [elementsEq])
        have oldStructural :=
          valid.2 beforeBlock beforeBlockMem
        have oldGapValid := oldStructural.2.2
        simp only [Block.GapValid, shrinking.1] at oldGapValid
        have oldIntervalEq :
            beforeBlock.intervalGap =
              state.view.rawGap singleton := by
          rcases oldGapValid with emptyCase | nonemptyCase
          · exact False.elim (by
              have : beforeBlock.elements ≠ [] := by
                simp [elementsEq]
              exact this emptyCase.1)
          · obtain ⟨minimizer, minimizerMem, attained⟩ :=
              nonemptyCase.2.1
            have minimizerEq : minimizer = singleton := by
              simpa [elementsEq] using minimizerMem
            subst minimizer
            exact attained.symm
        have valueOne : state.value singleton = 1 := by
          calc
            state.value singleton =
                Analysis.transientContractedGap
                  (state.view.rawGap singleton)
                  beforeBlock.intervalGap :=
              oldValue
            _ = 1 := by rw [oldIntervalEq]; simp
        have assignedBefore : singleton ∈ state.allElements :=
          State.mem_allElements_iff.mpr
            ⟨beforeBlock, beforeBlockMem, by simp [elementsEq]⟩
        have notRootBefore : singleton ≠ state.view.root := by
          intro singletonRoot
          apply valid.root_not_mem
          simpa only [singletonRoot] using assignedBefore
        have notRootAfter : singleton ≠ afterView.root := by
          intro singletonRoot
          exact notRootBefore (singletonRoot.trans rootEq)
        cases parentEq : afterView.parent singleton with
        | none =>
            exact False.elim
              (afterView.parent_ne_none_of_ne_root
                notRootAfter parentEq)
        | some owner =>
            simpa [rebaseShiftAtomic, rebaseShiftAtomicBlock,
              shrinking.1, elementsEq, parentEq, Block.withPlacement]
              using valueOne

/-- A stable shift-atomic state can be rank-prepared on any same-root view. -/
theorem rebase_rankPrepared
    {n : ℕ} {state : State n} {afterView : HeapView n}
    {params : Interface.Parameters}
    (atomic : state.ShiftAtomic)
    (stable : state.Stable params)
    (rootEq : afterView.root = state.view.root) :
    (state.rebaseShiftAtomic afterView).RankPrepared params := by
  exact
    ⟨atomic.rebase_valid stable.valid rootEq,
      rebase_complete stable.2.1 rootEq,
      rebase_oneGrowingPerSide afterView stable.2.2.2.1,
      atomic.rebase_growingTopmost afterView,
      atomic.rebase_valuesRealizeGaps stable.valid
        stable.2.2.2.2.2 rootEq⟩

/-- The same-root atomic rebase is one concrete rich silent trace. -/
theorem rebase_trace
    {n : ℕ} {state : State n} {afterView : HeapView n}
    {params : Interface.Parameters}
    (atomic : state.ShiftAtomic)
    (valid : state.Valid params)
    (rootEq : afterView.root = state.view.root) :
    Trace params state [.silent]
      (state.rebaseShiftAtomic afterView) := by
  have afterValid :
      (state.rebaseShiftAtomic afterView).Valid params :=
    atomic.rebase_valid valid rootEq
  exact Trace.cons
    (Step.silent valid afterValid
      (state.rebaseShiftAtomic_toInterface afterView).symm)
    (Trace.nil afterValid)

/--
Every shift-atomic block list aligns with every pointwise element shift.
No unit bound or tree-rank equation is needed for this combinatorial fact.
-/
theorem blocksAlignedWithShift
    {n : ℕ} {state : State n}
    (atomic : state.ShiftAtomic)
    (elementShift : Element n → ℤ) :
    state.BlocksAlignedWithShift elementShift
      (shiftAtomicBlockShift elementShift) := by
  refine {
    growing := ?_
    shrinking_empty := ?_
    shrinking_nonempty := ?_
  }
  · intro block blockMem growing
    rcases atomic block blockMem with growingCase | shrinkingCase
    · refine ⟨by simp [shiftAtomicBlockShift, growing], ?_⟩
      intro element elementMem
      rw [growingCase.2] at elementMem
      simp at elementMem
    · rw [growing] at shrinkingCase
      simp at shrinkingCase
  · intro block blockMem shrinking empty
    simp [shiftAtomicBlockShift, shrinking, empty]
  · intro block blockMem shrinking nonempty
    rcases atomic block blockMem with growingCase | shrinkingCase
    · rw [shrinking] at growingCase
      simp at growingCase
    · rcases shrinkingCase.2 with empty | ⟨singleton, elementsEq⟩
      · exact False.elim (nonempty empty)
      · refine ⟨elementShift singleton, ?_, ?_⟩
        · intro element elementMem
          simp [elementsEq] at elementMem
          subst element
          rfl
        · simp [shiftAtomicBlockShift, shrinking, elementsEq]

end ShiftAtomic

end State

namespace Canonical

/--
The canonical root is the unique global rank-zero external position.

In particular it is independent of the shape used to expose the full
external interval; only the snapshot's rank function matters.
-/
theorem canonicalRoot_eq_of_rank_eq_zero
    {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) {element : Element n}
    (rankZero : snapshot.rank element = 0) :
    canonicalRoot snapshot tree = element := by
  have elementIsMin :
      IsIntervalMin snapshot.rank
        (subtreeLower tree (Nat.le_refl n))
        (subtreeUpper tree (Nat.le_refl n))
        element := by
    refine ⟨?_, ?_, ?_⟩
    · simp [subtreeLower]
    · have upperEq :
          subtreeUpper tree (Nat.le_refl n) = Fin.last (2 * n) :=
        Fin.ext rfl
      rw [upperEq]
      exact Fin.le_last element
    · intro candidate _ _
      rw [rankZero]
      exact Nat.zero_le _
  have elementEq :=
    snapshot.intervalMin_unique
      (subtreeLower tree (Nat.le_refl n))
      (subtreeUpper tree (Nat.le_refl n))
      (subtree_nonempty tree (Nat.le_refl n))
      elementIsMin
  simpa [canonicalRoot, subtreeOwner] using elementEq.symm

/--
For a fixed snapshot, the canonical root is independent of the splay-tree
shape used to expose the complete external interval.
-/
theorem canonicalRoot_eq
    {n : ℕ} (snapshot : Snapshot n)
    (firstTree secondTree : Tree.BST 0 n) :
    canonicalRoot snapshot firstTree =
      canonicalRoot snapshot secondTree := by
  apply canonicalRoot_eq_of_rank_eq_zero
  exact rank_canonicalRoot_eq_zero snapshot secondTree

/-- For a tree-derived snapshot, the comparison-tree root is canonical. -/
theorem canonicalRoot_ofTree_node
    {n root : ℕ}
    (left : Tree.BST 0 root)
    (right : Tree.BST (root + 1) n)
    (splayTree : Tree.BST 0 n) :
    canonicalRoot
        (Snapshot.ofTree (.node left right)) splayTree =
      Splay.Rank.valuePos
        ⟨root, by
          have := right.lower_le_upper
          omega⟩ := by
  apply canonicalRoot_eq_of_rank_eq_zero
  simp [Snapshot.ofTree, Splay.Rank.valuePos]

end Canonical

/--
Every non-root comparison rotation preserves the canonical heap root selected
on an arbitrary fixed splay tree.

The outer comparison-tree root is unchanged by either contextual rotation
constructor, and `Canonical.canonicalRoot_ofTree_node` identifies it as the
unique rank-zero external position.
-/
theorem canonicalRoot_eq_of_rotationAt_depth_succ
    {n depth : ℕ}
    {before after : Tree.BST 0 n}
    (rotation : Tree.BST.RotationAt depth.succ before after)
    (splayTree : Tree.BST 0 n) :
    Canonical.canonicalRoot
        (Snapshot.ofTree after) splayTree =
      Canonical.canonicalRoot
        (Snapshot.ofTree before) splayTree := by
  cases rotation with
  | leftContext step right =>
      rw [Canonical.canonicalRoot_ofTree_node,
        Canonical.canonicalRoot_ofTree_node]
  | rightContext left step =>
      rw [Canonical.canonicalRoot_ofTree_node,
        Canonical.canonicalRoot_ofTree_node]

/--
Concrete structural prefix for a shift-atomic represented state when the
comparison update preserves the canonical root selected on the fixed splay
tree.

The prefix is exactly one silent bulk rebase.  It installs the new selected
parent structure while retaining the old numeric comparison ranks.
-/
theorem existsComparisonRotationAtomicPrefix_of_canonicalRoot_eq
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    {beforeComparison afterComparison : Tree.BST 0 n}
    {initial : State n}
    (initialRepresents :
      initial.Represents params
        (Snapshot.ofTree beforeComparison) splayTree)
    (atomic : initial.ShiftAtomic)
    (canonicalRootEq :
      Canonical.canonicalRoot
          (Snapshot.ofTree afterComparison) splayTree =
        Canonical.canonicalRoot
          (Snapshot.ofTree beforeComparison) splayTree) :
    ∃ prepared prefixEvents,
      Trace params initial prefixEvents prepared ∧
        prepared.RankPrepared params ∧
        prepared.view =
          Canonical.canonicalHeapViewWithRank
            (Snapshot.ofTree afterComparison)
            (Snapshot.ofTree beforeComparison).rank
            splayTree ∧
        prepared.ShiftAtomic := by
  let afterView :=
    Canonical.canonicalHeapViewWithRank
      (Snapshot.ofTree afterComparison)
      (Snapshot.ofTree beforeComparison).rank
      splayTree
  have afterViewRootEq :
      afterView.root = initial.view.root := by
    change
      Canonical.canonicalRoot
          (Snapshot.ofTree afterComparison) splayTree =
        initial.view.root
    rw [canonicalRootEq, initialRepresents.view_eq]
    rfl
  let prepared := initial.rebaseShiftAtomic afterView
  refine ⟨prepared, [.silent], ?_, ?_, ?_, ?_⟩
  · exact
      atomic.rebase_trace initialRepresents.valid afterViewRootEq
  · exact
      atomic.rebase_rankPrepared
        initialRepresents.stable afterViewRootEq
  · rfl
  · exact atomic.rebase afterView

/--
Fully prepared comparison-rotation certificate for the same-root atomic case.

Unlike an abstract preparer assumption, this theorem constructs the prefix,
the exact unit rank shift, and the block-shift alignment from checked model
primitives.
-/
theorem existsPreparedComparisonRotation_of_shiftAtomic_of_canonicalRoot_eq
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    {rotationDepth : ℕ}
    {beforeComparison afterComparison : Tree.BST 0 n}
    {initial : State n}
    (rotation :
      Tree.BST.RotationAt rotationDepth
        beforeComparison afterComparison)
    (initialRepresents :
      initial.Represents params
        (Snapshot.ofTree beforeComparison) splayTree)
    (atomic : initial.ShiftAtomic)
    (canonicalRootEq :
      Canonical.canonicalRoot
          (Snapshot.ofTree afterComparison) splayTree =
        Canonical.canonicalRoot
          (Snapshot.ofTree beforeComparison) splayTree) :
    Nonempty
      (PreparedComparisonRotation
        params splayTree
        (rotationDepth := rotationDepth)
        (beforeComparison := beforeComparison)
        (afterComparison := afterComparison)
        initial) := by
  obtain ⟨prepared, prefixEvents, prefixTrace, rankPrepared,
      viewEq, preparedAtomic⟩ :=
    existsComparisonRotationAtomicPrefix_of_canonicalRoot_eq
      initialRepresents atomic canonicalRootEq
  obtain ⟨elementShiftAt, exactUpdate, unitShift⟩ :=
    rotation.existsExactTreeRankUpdate
  let blockShift : Block n → ℤ :=
    State.shiftAtomicBlockShift
      (fun element => elementShiftAt element.val)
  have blocksAligned :
      prepared.BlocksAlignedWithShift
        (fun element => elementShiftAt element.val) blockShift :=
    preparedAtomic.blocksAlignedWithShift
      (fun element => elementShiftAt element.val)
  exact
    ⟨{
      rotation := rotation
      initial_represents := initialRepresents
      elementShiftAt := elementShiftAt
      exactUpdate := exactUpdate
      unitShift := unitShift
      blockShift := blockShift
      prepared := prepared
      prefixEvents := prefixEvents
      prefixTrace := prefixTrace
      rankPrepared := rankPrepared
      view_eq := viewEq
      blocksAligned := blocksAligned
    }⟩

/--
Every positive-depth comparison rotation has a concrete prepared certificate
from a shift-atomic represented state.

No additional junction, alignment, or root hypothesis remains: contextual
rotations preserve the outer comparison-tree root automatically.
-/
theorem existsPreparedComparisonRotation_of_shiftAtomic_of_depth_succ
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    {rotationDepth : ℕ}
    {beforeComparison afterComparison : Tree.BST 0 n}
    {initial : State n}
    (rotation :
      Tree.BST.RotationAt rotationDepth.succ
        beforeComparison afterComparison)
    (initialRepresents :
      initial.Represents params
        (Snapshot.ofTree beforeComparison) splayTree)
    (atomic : initial.ShiftAtomic) :
    Nonempty
      (PreparedComparisonRotation
        params splayTree
        (rotationDepth := rotationDepth.succ)
        (beforeComparison := beforeComparison)
        (afterComparison := afterComparison)
        initial) :=
  existsPreparedComparisonRotation_of_shiftAtomic_of_canonicalRoot_eq
    rotation initialRepresents atomic
      (canonicalRoot_eq_of_rotationAt_depth_succ
        rotation splayTree)

/--
Concrete structural prefix obligation with no reference to the rank-shift
witness chosen by a rotation.

It asks the finite lazy algorithm to install the post-rotation selected view,
retain the old numeric ranks, and reach the shift-atomic normal form.  The
generic theorem below supplies the exact unit shift and all block alignment.
-/
def ComparisonRotationAtomicPrefixBuilder {n : ℕ}
    (params : Interface.Parameters)
    (splayTree : Tree.BST 0 n) : Prop :=
  ∀ {rotationDepth : ℕ}
      {beforeComparison afterComparison : Tree.BST 0 n}
      {initial : State n},
    Tree.BST.RotationAt rotationDepth
        beforeComparison afterComparison →
      initial.Represents params
        (Snapshot.ofTree beforeComparison) splayTree →
        ∃ prepared prefixEvents,
          Trace params initial prefixEvents prepared ∧
            prepared.RankPrepared params ∧
            prepared.view =
              Canonical.canonicalHeapViewWithRank
                (Snapshot.ofTree afterComparison)
                (Snapshot.ofTree beforeComparison).rank
                splayTree ∧
            prepared.ShiftAtomic

/--
A shift-atomic structural prefix builder is a complete
`ComparisonRotationPreparer`.

This is strictly stronger than the existing aligned no-junction case in one
useful direction: the prefix builder never needs to inspect which exact unit
shift witness `RotationAt.existsExactTreeRankUpdate` selects.
-/
theorem comparisonRotationPreparer_of_atomicPrefixBuilder
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    (builder :
      ComparisonRotationAtomicPrefixBuilder params splayTree) :
    ComparisonRotationPreparer params splayTree := by
  intro rotationDepth beforeComparison afterComparison initial
    rotation initialRepresents
  obtain ⟨prepared, prefixEvents, prefixTrace, rankPrepared,
      viewEq, atomic⟩ :=
    builder rotation initialRepresents
  obtain ⟨elementShiftAt, exactUpdate, unitShift⟩ :=
    rotation.existsExactTreeRankUpdate
  let blockShift : Block n → ℤ :=
    State.shiftAtomicBlockShift
      (fun element => elementShiftAt element.val)
  have blocksAligned :
      prepared.BlocksAlignedWithShift
        (fun element => elementShiftAt element.val) blockShift := by
    exact
      atomic.blocksAlignedWithShift
        (fun element => elementShiftAt element.val)
  exact
    ⟨{
      rotation := rotation
      initial_represents := initialRepresents
      elementShiftAt := elementShiftAt
      exactUpdate := exactUpdate
      unitShift := unitShift
      blockShift := blockShift
      prepared := prepared
      prefixEvents := prefixEvents
      prefixTrace := prefixTrace
      rankPrepared := rankPrepared
      view_eq := viewEq
      blocksAligned := blocksAligned
    }⟩

/-- The shift-atomic prefix builder also discharges the public trace API. -/
theorem comparisonRotationTraceRealizer_of_atomicPrefixBuilder
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    (builder :
      ComparisonRotationAtomicPrefixBuilder params splayTree) :
    ComparisonRotationTraceRealizer params splayTree :=
  comparisonRotationTraceRealizer_of_preparer
    (comparisonRotationPreparer_of_atomicPrefixBuilder builder)

namespace PreparedComparisonRotation

private theorem Trace.initial_eq_final_of_events_eq_nil
    {n : ℕ} {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    (trace : Trace params initial events final)
    (eventsEmpty : events = []) :
    initial = final := by
  cases trace with
  | nil =>
      rfl
  | cons head tail =>
      simp at eventsEmpty

/--
If a comparison rotation changes the canonical heap-parent relation selected
on the fixed splay tree, no prepared certificate can have an empty prefix.

Thus the silent rank-update primitive alone cannot prove the universal
preparer: a genuine structural junction/split prefix is logically necessary.
-/
theorem prefixEvents_ne_nil_of_canonicalParent_ne
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    {rotationDepth : ℕ}
    {beforeComparison afterComparison : Tree.BST 0 n}
    {initial : State n}
    (certificate :
      PreparedComparisonRotation
        params splayTree
        (rotationDepth := rotationDepth)
        (beforeComparison := beforeComparison)
        (afterComparison := afterComparison)
        initial)
    (parentNe :
      Canonical.canonicalParent
          (Snapshot.ofTree beforeComparison) splayTree ≠
        Canonical.canonicalParent
          (Snapshot.ofTree afterComparison) splayTree) :
    certificate.prefixEvents ≠ [] := by
  intro eventsEmpty
  have initialEq :
      initial = certificate.prepared :=
    Trace.initial_eq_final_of_events_eq_nil
      certificate.prefixTrace eventsEmpty
  apply parentNe
  have preparedViewEq := certificate.view_eq
  rw [← initialEq] at preparedViewEq
  have viewEq :
      Canonical.canonicalHeapView
          (Snapshot.ofTree beforeComparison) splayTree =
        Canonical.canonicalHeapViewWithRank
          (Snapshot.ofTree afterComparison)
          (Snapshot.ofTree beforeComparison).rank
          splayTree :=
    certificate.initial_represents.view_eq.symm.trans
      preparedViewEq
  exact congrArg HeapView.parent viewEq

end PreparedComparisonRotation

end Splay.Lazy
