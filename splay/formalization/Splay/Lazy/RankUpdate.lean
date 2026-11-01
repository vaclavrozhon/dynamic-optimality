import Splay.Lazy.Operations

namespace Splay.Lazy

namespace HeapView

/--
Two transient views have the same heap structure and differ, if at all, only
in their real ranks.

This is the relation used for the second half of a non-atomic junction: the
new parent relation has already been installed and the comparison-tree rank
update is applied afterwards.
-/
structure SameStructure {n : ℕ}
    (before after : HeapView n) : Prop where
  root_eq : after.root = before.root
  parent_eq : after.parent = before.parent
  side_eq : after.side = before.side
  topDown_eq : after.topDown = before.topDown
  level_eq : after.level = before.level

namespace SameStructure

theorem parent_apply {n : ℕ} {before after : HeapView n}
    (same : SameStructure before after) (element : Element n) :
    after.parent element = before.parent element := by
  rw [same.parent_eq]

theorem side_apply {n : ℕ} {before after : HeapView n}
    (same : SameStructure before after) (element : Element n) :
    after.side element = before.side element := by
  rw [same.side_eq]

theorem topDown_apply {n : ℕ} {before after : HeapView n}
    (same : SameStructure before after)
    (owner : Element n) (childSide : Side) :
    after.topDown owner childSide =
      before.topDown owner childSide := by
  rw [same.topDown_eq]

theorem attachedTopDown_eq {n : ℕ} {before after : HeapView n}
    (same : SameStructure before after)
    (assigned : List (Element n)) (owner : Element n)
    (childSide : Side) :
    after.attachedTopDown assigned owner childSide =
      before.attachedTopDown assigned owner childSide := by
  unfold attachedTopDown
  rw [same.topDown_apply]

end SameStructure

/-- A signed description of one element's rank update. -/
def RankShift {n : ℕ} (before after : HeapView n)
    (element : Element n) (shift : ℤ) : Prop :=
  (after.rank element : ℤ) = before.rank element + shift

/--
When the parent relation is fixed, the raw-gap shift is the child's rank shift
minus the owner's rank shift.
-/
theorem rawGap_eq_add_sub_of_rankShifts
    {n : ℕ} {before after : HeapView n}
    (same : SameStructure before after)
    {element owner : Element n} {childShift ownerShift : ℤ}
    (parent : before.parent element = some owner)
    (childRank : RankShift before after element childShift)
    (ownerRank : RankShift before after owner ownerShift) :
    after.rawGap element =
      before.rawGap element + (childShift - ownerShift) := by
  simp only [rawGap, same.parent_apply, parent]
  unfold RankShift at childRank ownerRank
  omega

/-- Equal rank shifts of a child and its owner leave their raw gap unchanged. -/
theorem rawGap_eq_of_equal_rankShift
    {n : ℕ} {before after : HeapView n}
    (same : SameStructure before after)
    {element owner : Element n} {shift : ℤ}
    (parent : before.parent element = some owner)
    (childRank : RankShift before after element shift)
    (ownerRank : RankShift before after owner shift) :
    after.rawGap element = before.rawGap element := by
  have hGap :=
    rawGap_eq_add_sub_of_rankShifts same parent childRank ownerRank
  simpa using hGap

end HeapView

namespace Block

/-- Apply the common signed raw-gap shift to a block's stored interval gap. -/
def shiftedInterval {n : ℕ} (block : Block n) (shift : ℤ) : Block n :=
  { block with intervalGap := block.intervalGap + shift }

@[simp]
theorem shiftedInterval_toInterface {n : ℕ}
    (block : Block n) (shift : ℤ) :
    (block.shiftedInterval shift).toInterface = block.toInterface :=
  rfl

/--
A uniform rank update on a shrinking interval is an exact silent transfer in
the rich model, even though neither the child nor owner ranks need stay fixed.
-/
def isTransfer_shiftedInterval_of_rankShifts
    {n : ℕ} {before after : HeapView n}
    (same : before.SameStructure after)
    {block : Block n} (shrinking : block.mode = .shrinking)
    {childShift ownerShift : ℤ}
    (parents :
      ∀ element ∈ block.elements,
        before.parent element = some block.owner)
    (childRanks :
      ∀ element ∈ block.elements,
        HeapView.RankShift before after element childShift)
    (ownerRank :
      HeapView.RankShift before after block.owner ownerShift) :
    IsTransfer before after block
      (block.shiftedInterval (childShift - ownerShift)) := by
  refine {
    shift := childShift - ownerShift
    shrinking := shrinking
    creator_eq := rfl
    passCount_eq := rfl
    mode_eq := rfl
    elements_eq := rfl
    intervalGap_eq := rfl
    rawGap_eq := ?_
  }
  intro element member
  exact before.rawGap_eq_add_sub_of_rankShifts same
    (parents element member)
    (childRanks element member) ownerRank

/--
The full local preservation lemma for a nonempty shrinking block under a
uniform rank update.
-/
theorem structurallyValid_shiftedInterval_of_rankShifts
    {n : ℕ} {before after : HeapView n}
    (same : before.SameStructure after)
    {assigned : List (Element n)} {block : Block n}
    (valid : block.StructurallyValid before assigned)
    (shrinking : block.mode = .shrinking)
    (nonempty : block.elements ≠ [])
    {childShift ownerShift : ℤ}
    (childRanks :
      ∀ element ∈ block.elements,
        HeapView.RankShift before after element childShift)
    (ownerRank :
      HeapView.RankShift before after block.owner ownerShift) :
    (block.shiftedInterval (childShift - ownerShift)).StructurallyValid
      after assigned := by
  have transfer :=
    isTransfer_shiftedInterval_of_rankShifts same shrinking
      (fun element member => valid.parent_eq member)
      childRanks ownerRank
  apply transfer.after_structurallyValid valid nonempty
  rw [same.attachedTopDown_eq]
  exact valid.isSegment

/--
The exact local condition under which a block absorbs a rank update.

Growing blocks cannot absorb a nonzero shift because their interval gap is
fixed at zero. Empty shrinking blocks also keep zero. Every nonempty shrinking
block may absorb one common signed shift of all member raw gaps.
-/
def AbsorbsRankUpdate {n : ℕ}
    (before after : HeapView n) (block : Block n) (shift : ℤ) : Prop :=
  match block.mode with
  | .growing =>
      shift = 0 ∧
        ∀ element ∈ block.elements,
          after.rawGap element = before.rawGap element
  | .shrinking =>
      (block.elements = [] ∧ shift = 0) ∨
        (block.elements ≠ [] ∧
          ∀ element ∈ block.elements,
            after.rawGap element = before.rawGap element + shift)

/-- A compatible absorbed rank update preserves the complete block invariant. -/
theorem shiftedInterval_structurallyValid
    {n : ℕ} {before after : HeapView n}
    (same : before.SameStructure after)
    {assigned : List (Element n)} {block : Block n} {shift : ℤ}
    (valid : block.StructurallyValid before assigned)
    (absorbs : AbsorbsRankUpdate before after block shift) :
    (block.shiftedInterval shift).StructurallyValid after assigned := by
  have afterSegment :
      IsSegment (block.shiftedInterval shift).elements
        (after.attachedTopDown assigned
          (block.shiftedInterval shift).owner
          (block.shiftedInterval shift).side) := by
    change IsSegment block.elements
      (after.attachedTopDown assigned block.owner block.side)
    rw [same.attachedTopDown_eq]
    exact valid.isSegment
  cases hMode : block.mode with
  | growing =>
      have hAbsorbs :
          shift = 0 ∧
            ∀ element ∈ block.elements,
              after.rawGap element = before.rawGap element := by
        simpa only [AbsorbsRankUpdate, hMode] using absorbs
      apply structurallyValid_growing
        (block := block.shiftedInterval shift)
        (by
          change block.mode = .growing
          exact hMode)
        (by
          change block.owner = block.creator
          exact valid.owner_eq_creator_of_growing hMode)
        afterSegment
      · simp [shiftedInterval, hAbsorbs.1,
          valid.growing_intervalGap_eq_zero hMode]
      · intro element member
        rw [hAbsorbs.2 element member]
        have hBefore := valid.2.2
        simp only [GapValid, hMode] at hBefore
        exact hBefore.2 element member
  | shrinking =>
      have hAbsorbs :
          (block.elements = [] ∧ shift = 0) ∨
            (block.elements ≠ [] ∧
              ∀ element ∈ block.elements,
                after.rawGap element =
                  before.rawGap element + shift) := by
        simpa only [AbsorbsRankUpdate, hMode] using absorbs
      rcases hAbsorbs with hEmpty | hNonempty
      · apply structurallyValid_empty_shrinking
          (by simp [shiftedInterval, hMode])
          (by simpa [shiftedInterval] using hEmpty.1)
        have hBefore := valid.2.2
        simp only [GapValid, hMode] at hBefore
        rcases hBefore with beforeEmpty | beforeNonempty
        · simp [shiftedInterval, hEmpty.2, beforeEmpty.2]
        · exact False.elim (beforeNonempty.1 hEmpty.1)
      · apply structurallyValid_shrinking
          (by simp [shiftedInterval, hMode])
          (by simpa [shiftedInterval] using hNonempty.1)
          afterSegment
        have hGap :=
          shrinking_gapValid_of_uniform_shift
            (beforeView := before) (afterView := after)
            (beforeBlock := block)
            (afterBlock := block.shiftedInterval shift)
            (shift := shift)
            hMode valid.2.2 rfl rfl hNonempty.1 rfl hNonempty.2
        have afterMode :
            (block.shiftedInterval shift).mode = .shrinking := by
          simp [shiftedInterval, hMode]
        simp only [GapValid, afterMode] at hGap
        rcases hGap with impossible | nonemptyGap
        · have afterNonempty :
              (block.shiftedInterval shift).elements ≠ [] := by
            simpa [shiftedInterval] using hNonempty.1
          exact False.elim (afterNonempty impossible.1)
        · exact nonemptyGap.2

end Block

namespace State

/--
Apply a rank update after all affected shrinking interval gaps have been
shifted by their common raw-gap changes.
-/
def absorbRankUpdate {n : ℕ} (state : State n)
    (afterView : HeapView n) (shift : Block n → ℤ) : State n where
  view := afterView
  blocks := state.blocks.map fun block =>
    block.shiftedInterval (shift block)
  value := state.value

@[simp]
theorem absorbRankUpdate_toInterface {n : ℕ} (state : State n)
    (afterView : HeapView n) (shift : Block n → ℤ) :
    (state.absorbRankUpdate afterView shift).toInterface =
      state.toInterface := by
  cases state with
  | mk view blocks value =>
      simp [absorbRankUpdate, State.toInterface,
        Function.comp_def]

@[simp]
theorem absorbRankUpdate_allElements {n : ℕ} (state : State n)
    (afterView : HeapView n) (shift : Block n → ℤ) :
    (state.absorbRankUpdate afterView shift).allElements =
      state.allElements := by
  cases state with
  | mk view blocks value =>
      simp only [absorbRankUpdate, State.allElements]
      induction blocks with
      | nil =>
          rfl
      | cons head tail ih =>
          simp only [List.map_cons, List.flatMap_cons]
          change
            head.elements ++
                (tail.map fun block =>
                  block.shiftedInterval (shift block)).flatMap
                    (fun block => block.elements) =
              head.elements ++
                tail.flatMap (fun block => block.elements)
          exact congrArg (head.elements ++ ·) ih

/-- Every block absorbs the rank update prescribed for it. -/
def RankUpdateCompatible {n : ℕ} (state : State n)
    (afterView : HeapView n) (shift : Block n → ℤ) : Prop :=
  state.view.SameStructure afterView ∧
    ∀ block ∈ state.blocks,
      Block.AbsorbsRankUpdate state.view afterView block (shift block)

theorem absorbRankUpdate_valid {n : ℕ}
    {state : State n} {afterView : HeapView n}
    {shift : Block n → ℤ} {params : Interface.Parameters}
    (valid : state.Valid params)
    (compatible : state.RankUpdateCompatible afterView shift) :
    (state.absorbRankUpdate afterView shift).Valid params := by
  constructor
  · simpa only [absorbRankUpdate_toInterface] using valid.toInterface
  · intro afterBlock hAfterBlock
    simp only [absorbRankUpdate] at hAfterBlock
    obtain ⟨beforeBlock, hBeforeBlock, rfl⟩ :=
      List.mem_map.mp hAfterBlock
    rw [absorbRankUpdate_allElements]
    exact Block.shiftedInterval_structurallyValid compatible.1
      (valid.2 beforeBlock hBeforeBlock)
      (compatible.2 beforeBlock hBeforeBlock)

/--
An absorbed rank update is one rich silent step: it preserves transient
validity and erases to no abstract-interface operation.
-/
theorem absorbRankUpdate_step {n : ℕ}
    {state : State n} {afterView : HeapView n}
    {shift : Block n → ℤ} {params : Interface.Parameters}
    (valid : state.Valid params)
    (compatible : state.RankUpdateCompatible afterView shift) :
    Step params state .silent
      (state.absorbRankUpdate afterView shift) :=
  Step.silent valid
    (state.absorbRankUpdate_valid valid compatible)
    (state.absorbRankUpdate_toInterface afterView shift).symm

end State

end Splay.Lazy
