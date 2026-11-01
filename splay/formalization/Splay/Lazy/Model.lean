import Splay.Analysis.TransientGap
import Splay.Interface.Model
import Mathlib.Data.Finset.Max

namespace Splay.Lazy

abbrev Element (n : ℕ) :=
  Interface.Element n

/-- Side of a heap-parent heavy path on which a heap-child is attached. -/
inductive Side
  | left
  | right
  deriving DecidableEq, Repr

/-- `inside` occurs as one contiguous segment of `whole`. -/
def IsSegment {α : Type*} (inside whole : List α) : Prop :=
  ∃ front back, whole = front ++ inside ++ back

namespace IsSegment

/-- Every member of a contiguous segment is a member of the ambient list. -/
theorem mem {α : Type*} {inside whole : List α}
    (segment : IsSegment inside whole) {element : α}
    (member : element ∈ inside) :
    element ∈ whole := by
  obtain ⟨front, back, rfl⟩ := segment
  simp only [List.mem_append]
  exact Or.inl (Or.inr member)

end IsSegment

/--
A transient heap view.

The parent relation and its top-down child order are kept explicitly because a
junction may be installed before the comparison-tree ranks are updated. Thus
`parent` need not be heap-ordered in a transient state.
-/
structure HeapView (n : ℕ) where
  rank : Element n → ℕ
  root : Element n
  parent : Element n → Option (Element n)
  side : Element n → Side
  topDown : Element n → Side → List (Element n)
  /-- Structural depth, independent of comparison-tree rank. -/
  level : Element n → ℕ
  root_parent : parent root = none
  parent_eq_none :
    ∀ element, parent element = none → element = root
  parent_level_lt :
    ∀ {element owner}, parent element = some owner →
      level owner < level element
  side_order :
    ∀ {element owner}, parent element = some owner →
      match side element with
      | .left => element.val < owner.val
      | .right => owner.val < element.val
  topDown_nodup :
    ∀ owner childSide, (topDown owner childSide).Nodup
  topDown_ordered :
    ∀ owner,
      (topDown owner .left).Pairwise
          (fun earlier later => earlier.val < later.val) ∧
        (topDown owner .right).Pairwise
          (fun earlier later => later.val < earlier.val)
  mem_topDown_iff :
    ∀ {owner childSide element},
      element ∈ topDown owner childSide ↔
        parent element = some owner ∧ side element = childSide

namespace HeapView

/--
Signed heap gap. It can be negative in the deliberately non-atomic interval
between installing a junction and updating ranks.
-/
def rawGap {n : ℕ} (view : HeapView n) (element : Element n) : ℤ :=
  match view.parent element with
  | none => 0
  | some owner => (view.rank element : ℤ) - view.rank owner

/-- Stable heap views recover strict heap order. -/
def HeapOrdered {n : ℕ} (view : HeapView n) : Prop :=
  ∀ {element owner}, view.parent element = some owner →
    view.rank owner < view.rank element

/-- Laminar symmetric-order property of heap paths induced by a BST.

If `winner` and `loser` are sibling heap children, every existing child of
`winner` on the side toward `loser` lies strictly inside the winner's region.
Consequently the sibling is farther out in symmetric order.  This property
is intentionally separate from `HeapView`: arbitrary transient views need
not come from a BST, while canonical views do. -/
def NestedChildOrder {n : ℕ} (view : HeapView n) : Prop :=
  ∀ {owner winner loser child},
    view.parent winner = some owner →
      view.parent loser = some owner →
        winner ≠ loser →
          view.parent child = some winner →
          view.side child =
              (if loser.val < winner.val then Side.left else Side.right) →
            match (if loser.val < winner.val then Side.left else Side.right) with
            | Side.left => loser.val < child.val
            | Side.right => child.val < loser.val

/--
Top-down order restricted to elements that currently belong to some block.
This is the order against which transient interval consecutiveness is checked:
a `Delete` may leave an element detached while it remains part of the heap
view or is already installed under its new parent.
-/
def attachedTopDown {n : ℕ} (view : HeapView n)
    (assigned : List (Element n)) (owner : Element n) (childSide : Side) :
    List (Element n) :=
  (view.topDown owner childSide).filter fun element =>
    decide (element ∈ assigned)

@[simp]
theorem mem_attachedTopDown_iff {n : ℕ} (view : HeapView n)
    {assigned : List (Element n)} {owner element : Element n}
    {childSide : Side} :
    element ∈ view.attachedTopDown assigned owner childSide ↔
      element ∈ view.topDown owner childSide ∧ element ∈ assigned := by
  simp [attachedTopDown]

theorem parent_ne_none_of_ne_root {n : ℕ} (view : HeapView n)
    {element : Element n} (hNe : element ≠ view.root) :
    view.parent element ≠ none := by
  intro hNone
  exact hNe (view.parent_eq_none element hNone)

theorem mem_topDown_parent {n : ℕ} (view : HeapView n)
    {owner element : Element n} {childSide : Side}
    (hMember : element ∈ view.topDown owner childSide) :
    view.parent element = some owner :=
  (view.mem_topDown_iff.mp hMember).1

theorem mem_topDown_side {n : ℕ} (view : HeapView n)
    {owner element : Element n} {childSide : Side}
    (hMember : element ∈ view.topDown owner childSide) :
    view.side element = childSide :=
  (view.mem_topDown_iff.mp hMember).2

theorem rawGap_pos_of_heapOrdered {n : ℕ} {view : HeapView n}
    (hOrdered : view.HeapOrdered) {element owner : Element n}
    (hParent : view.parent element = some owner) :
    0 < view.rawGap element := by
  have hRank : view.rank owner < view.rank element :=
    hOrdered hParent
  have hRankInt :
      (view.rank owner : ℤ) < (view.rank element : ℤ) := by
    exact_mod_cast hRank
  simp only [rawGap, hParent]
  omega

end HeapView

/--
A lazy interval enriched with the data intentionally erased by the abstract
interface.

`creator` is immutable and is what the interface tracks. `owner` is the
current heap-parent and can change when a shrinking interval is transferred.
-/
structure Block (n : ℕ) where
  creator : Element n
  owner : Element n
  side : Side
  passCount : ℕ
  mode : Interface.Mode
  elements : List (Element n)
  intervalGap : ℤ
  deriving Repr

namespace Block

def toInterface {n : ℕ} (block : Block n) : Interface.Block n where
  creator := block.creator
  passCount := block.passCount
  mode := block.mode
  elements := block.elements

/--
Gap validity in both stable and transient states.

Growing intervals use interval gap zero and therefore require nonnegative raw
gaps. A nonempty shrinking interval stores the attained minimum signed raw
gap. Empty shrinking intervals are harmless administrative remnants, use
zero, and persist under the interface's stable block identifiers.
-/
def GapValid {n : ℕ} (view : HeapView n) (block : Block n) : Prop :=
  match block.mode with
  | .growing =>
      block.intervalGap = 0 ∧
        ∀ element ∈ block.elements, 0 ≤ view.rawGap element
  | .shrinking =>
      (block.elements = [] ∧ block.intervalGap = 0) ∨
        (block.elements ≠ [] ∧
          Analysis.IsIntervalGap block.elements.toFinset view.rawGap
            block.intervalGap)

/-- Every nonempty finite block payload has an attained signed minimum. -/
theorem exists_intervalGap {n : ℕ} (view : HeapView n)
    (elements : List (Element n)) (nonempty : elements ≠ []) :
    ∃ intervalGap,
      Analysis.IsIntervalGap elements.toFinset view.rawGap intervalGap := by
  have finiteNonempty : elements.toFinset.Nonempty :=
    (List.toFinset_nonempty_iff elements).2 nonempty
  obtain ⟨minimizer, minimizerMember, minimum⟩ :=
    Finset.exists_min_image elements.toFinset view.rawGap finiteNonempty
  exact
    ⟨view.rawGap minimizer,
      ⟨⟨minimizer, minimizerMember, rfl⟩,
        fun element member => minimum element member⟩⟩

/-- A shrinking block admits a canonical recomputation of its interval gap:
zero for the empty payload and an attained signed minimum otherwise. -/
theorem exists_gapValid_of_shrinking {n : ℕ} (view : HeapView n)
    (block : Block n) (shrinking : block.mode = .shrinking) :
    ∃ intervalGap,
      ({ block with intervalGap := intervalGap }).GapValid view := by
  by_cases empty : block.elements = []
  · refine ⟨0, ?_⟩
    simp [GapValid, shrinking, empty]
  · obtain ⟨intervalGap, minimum⟩ :=
      exists_intervalGap view block.elements empty
    refine ⟨intervalGap, ?_⟩
    simpa [GapValid, shrinking, empty] using minimum

/--
The complete local structural invariant for one transient lazy interval.
-/
def StructurallyValid {n : ℕ} (view : HeapView n)
    (assigned : List (Element n)) (block : Block n) : Prop :=
  IsSegment block.elements
      (view.attachedTopDown assigned block.owner block.side) ∧
    (block.mode = .growing → block.owner = block.creator) ∧
    block.GapValid view

theorem StructurallyValid.isSegment {n : ℕ} {view : HeapView n}
    {assigned : List (Element n)} {block : Block n}
    (valid : block.StructurallyValid view assigned) :
    IsSegment block.elements
      (view.attachedTopDown assigned block.owner block.side) :=
  valid.1

theorem StructurallyValid.owner_eq_creator_of_growing
    {n : ℕ} {view : HeapView n} {assigned : List (Element n)}
    {block : Block n}
    (valid : block.StructurallyValid view assigned)
    (growing : block.mode = .growing) :
    block.owner = block.creator :=
  valid.2.1 growing

theorem StructurallyValid.parent_eq {n : ℕ} {view : HeapView n}
    {assigned : List (Element n)} {block : Block n}
    (valid : block.StructurallyValid view assigned)
    {element : Element n} (member : element ∈ block.elements) :
    view.parent element = some block.owner := by
  have hAttached := valid.isSegment.mem member
  have hTopDown :=
    (view.mem_attachedTopDown_iff.mp hAttached).1
  exact view.mem_topDown_parent hTopDown

theorem StructurallyValid.side_eq {n : ℕ} {view : HeapView n}
    {assigned : List (Element n)} {block : Block n}
    (valid : block.StructurallyValid view assigned)
    {element : Element n} (member : element ∈ block.elements) :
    view.side element = block.side := by
  have hAttached := valid.isSegment.mem member
  have hTopDown :=
    (view.mem_attachedTopDown_iff.mp hAttached).1
  exact view.mem_topDown_side hTopDown

theorem StructurallyValid.growing_intervalGap_eq_zero
    {n : ℕ} {view : HeapView n} {assigned : List (Element n)}
    {block : Block n}
    (valid : block.StructurallyValid view assigned)
    (growing : block.mode = .growing) :
    block.intervalGap = 0 := by
  have hGap := valid.2.2
  simp only [GapValid, growing] at hGap
  exact hGap.1

theorem StructurallyValid.shrinking_interval_le_raw
    {n : ℕ} {view : HeapView n} {assigned : List (Element n)}
    {block : Block n}
    (valid : block.StructurallyValid view assigned)
    (shrinking : block.mode = .shrinking)
    {element : Element n} (member : element ∈ block.elements) :
    block.intervalGap ≤ view.rawGap element := by
  have hGap := valid.2.2
  simp only [GapValid, shrinking] at hGap
  rcases hGap with hEmpty | hNonempty
  · rw [hEmpty.1] at member
    simp at member
  · exact hNonempty.2.interval_le (by
      simpa using member)

theorem StructurallyValid.intervalGap_le_raw
    {n : ℕ} {view : HeapView n} {assigned : List (Element n)}
    {block : Block n}
    (valid : block.StructurallyValid view assigned)
    {element : Element n} (member : element ∈ block.elements) :
    block.intervalGap ≤ view.rawGap element := by
  cases hMode : block.mode with
  | growing =>
      have hGap := valid.2.2
      simp only [GapValid, hMode] at hGap
      rw [hGap.1]
      exact hGap.2 element member
  | shrinking =>
      exact valid.shrinking_interval_le_raw hMode member

theorem StructurallyValid.pointGap_coe_eq
    {n : ℕ} {view : HeapView n} {assigned : List (Element n)}
    {block : Block n}
    (valid : block.StructurallyValid view assigned)
    {element : Element n} (member : element ∈ block.elements) :
    (Analysis.transientPointGap
        (view.rawGap element) block.intervalGap : ℤ) =
      view.rawGap element - block.intervalGap :=
  Analysis.transientPointGap_coe_eq
    (valid.intervalGap_le_raw member)

theorem StructurallyValid.contractedGap_pos
    {n : ℕ} {view : HeapView n} {assigned : List (Element n)}
    {block : Block n}
    (_valid : block.StructurallyValid view assigned)
    {element : Element n} (_member : element ∈ block.elements) :
    0 < Analysis.transientContractedGap
      (view.rawGap element) block.intervalGap := by
  simp only [Analysis.transientContractedGap, Analysis.contractedGap]
  omega

/-- Changing the heap view preserves a block whenever its placement remains
consecutive and every member keeps the same signed raw gap. -/
theorem StructurallyValid.of_rawGap_eq
    {n : ℕ} {before after : HeapView n}
    {beforeAssigned afterAssigned : List (Element n)} {block : Block n}
    (valid : block.StructurallyValid before beforeAssigned)
    (afterSegment :
      IsSegment block.elements
        (after.attachedTopDown afterAssigned block.owner block.side))
    (rawGapEq : ∀ element ∈ block.elements,
      after.rawGap element = before.rawGap element) :
    block.StructurallyValid after afterAssigned := by
  refine ⟨afterSegment, valid.2.1, ?_⟩
  cases modeEq : block.mode with
  | growing =>
      have beforeGap := valid.2.2
      simp only [GapValid, modeEq] at beforeGap ⊢
      exact ⟨beforeGap.1, fun element member => by
        rw [rawGapEq element member]
        exact beforeGap.2 element member⟩
  | shrinking =>
      have beforeGap := valid.2.2
      simp only [GapValid, modeEq] at beforeGap ⊢
      rcases beforeGap with empty | nonempty
      · exact Or.inl empty
      · refine Or.inr ⟨nonempty.1, ?_⟩
        obtain ⟨⟨minimizer, minimizerMember, attained⟩, minimum⟩ :=
          nonempty.2
        constructor
        · exact ⟨minimizer, minimizerMember, by
            rw [rawGapEq minimizer (by simpa using minimizerMember)]
            exact attained⟩
        · intro element member
          rw [rawGapEq element (by simpa using member)]
          exact minimum element member

end Block

/-- Rich lazy-interval state together with interface values. -/
structure State (n : ℕ) where
  view : HeapView n
  blocks : List (Block n)
  value : Element n → ℕ

namespace State

def toInterface {n : ℕ} (state : State n) : Interface.State n where
  blocks := state.blocks.map Block.toInterface
  value := state.value

def allElements {n : ℕ} (state : State n) : List (Element n) :=
  state.blocks.flatMap fun block => block.elements

@[simp]
theorem mem_allElements_iff {n : ℕ} {state : State n}
    {element : Element n} :
    element ∈ state.allElements ↔
      ∃ block ∈ state.blocks, element ∈ block.elements := by
  simp [allElements]

@[simp]
theorem toInterface_allElements {n : ℕ} (state : State n) :
    state.toInterface.allElements = state.allElements := by
  change
    (state.blocks.map Block.toInterface).flatMap
        (fun block : Interface.Block n => block.elements) =
      state.blocks.flatMap (fun block : Block n => block.elements)
  induction state.blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      change
        block.elements ++
            (blocks.map Block.toInterface).flatMap
              (fun item : Interface.Block n => item.elements) =
          block.elements ++
            blocks.flatMap (fun item : Block n => item.elements)
      exact congrArg (block.elements ++ ·) ih

/--
Transient validity: the abstract interface state is valid and every rich block
is a genuine consecutive interval with coherent owner, side, and signed gap.

Completeness and exact value synchronization are intentionally deferred to
stable checkpoints so that `Delete`/`Insert` and temporary value adjustments
can be represented one primitive step at a time.
-/
def Valid {n : ℕ} (state : State n) (params : Interface.Parameters) : Prop :=
  state.toInterface.Valid params ∧
    ∀ block ∈ state.blocks,
      block.StructurallyValid state.view state.allElements

/-- An element with a heap-parent that is temporarily between blocks. -/
def Detached {n : ℕ} (state : State n) (element : Element n) : Prop :=
  state.view.parent element ≠ none ∧ element ∉ state.allElements

/-- At a stable checkpoint, blocks contain exactly all non-root heap paths. -/
def Complete {n : ℕ} (state : State n) : Prop :=
  ∀ element,
    element ∈ state.allElements ↔ state.view.parent element ≠ none

/-- There is exactly one ordinary growing interval on each side of each path. -/
def OneGrowingPerSide {n : ℕ} (state : State n) : Prop :=
  ∀ owner childSide,
    ∃! id : Fin state.blocks.length,
      let block := state.blocks.get id
      block.mode = .growing ∧
        block.owner = owner ∧ block.side = childSide

/-- Every growing interval is the top-most segment on its side. -/
def GrowingTopmost {n : ℕ} (state : State n) : Prop :=
  ∀ id : Fin state.blocks.length,
    let block := state.blocks.get id
    block.mode = .growing →
      ∃ suffix,
        state.view.topDown block.owner block.side =
          block.elements ++ suffix

/-- Interface values exactly encode the current transient point gaps. -/
def ValuesRealizeGaps {n : ℕ} (state : State n) : Prop :=
  state.value state.view.root = 1 ∧
    ∀ block ∈ state.blocks, ∀ element ∈ block.elements,
      state.value element =
        Analysis.transientContractedGap
          (state.view.rawGap element) block.intervalGap

/--
A stable lazy state agrees with a heap-ordered view, has no detached elements,
has the canonical two growing intervals per owner, and synchronizes all
interface values with contracted point gaps.
-/
def Stable {n : ℕ} (state : State n)
    (params : Interface.Parameters) : Prop :=
  state.Valid params ∧
    state.Complete ∧
    state.view.HeapOrdered ∧
    state.OneGrowingPerSide ∧
    state.GrowingTopmost ∧
    state.ValuesRealizeGaps

theorem Valid.toInterface {n : ℕ} {state : State n}
    {params : Interface.Parameters} (valid : state.Valid params) :
    state.toInterface.Valid params :=
  valid.1

theorem Valid.allElements_nodup {n : ℕ} {state : State n}
    {params : Interface.Parameters} (valid : state.Valid params) :
    state.allElements.Nodup := by
  have hNodup := valid.toInterface.1
  simpa only [toInterface_allElements] using hNodup

/-- In a valid rich state, an assigned element determines its block ID.
This is the block-list form of global payload duplicate-freeness and is the
basic separation fact used when a pass moves losers out of one source into
distinct destinations. -/
theorem Valid.blockId_eq_of_element_mem
    {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params)
    {firstId secondId : Interface.BlockId} {first second : Block n}
    {element : Element n}
    (firstFound : state.blocks[firstId]? = some first)
    (firstMem : element ∈ first.elements)
    (secondFound : state.blocks[secondId]? = some second)
    (secondMem : element ∈ second.elements) :
    firstId = secondId := by
  have blocksPairwise :
      state.blocks.Pairwise
        (fun first second => List.Disjoint first.elements second.elements) :=
    (List.nodup_flatMap.mp valid.allElements_nodup).2
  obtain ⟨firstLt, firstEq⟩ := List.getElem?_eq_some_iff.mp firstFound
  obtain ⟨secondLt, secondEq⟩ := List.getElem?_eq_some_iff.mp secondFound
  rcases lt_trichotomy firstId secondId with firstBefore | idsEq |
      secondBefore
  · have disjoint :
        List.Disjoint state.blocks[firstId].elements
          state.blocks[secondId].elements :=
      (List.pairwise_iff_getElem.mp blocksPairwise)
        firstId secondId firstLt secondLt firstBefore
    rw [firstEq, secondEq] at disjoint
    exact False.elim
      ((List.disjoint_left.mp disjoint) firstMem secondMem)
  · exact idsEq
  · have disjoint :
        List.Disjoint state.blocks[secondId].elements
          state.blocks[firstId].elements :=
      (List.pairwise_iff_getElem.mp blocksPairwise)
        secondId firstId secondLt firstLt secondBefore
    rw [secondEq, firstEq] at disjoint
    exact False.elim
      ((List.disjoint_left.mp disjoint) secondMem firstMem)

theorem Valid.assigned_placement {n : ℕ} {state : State n}
    {params : Interface.Parameters} (valid : state.Valid params)
    {element : Element n} (assigned : element ∈ state.allElements) :
    ∃ block ∈ state.blocks,
      element ∈ block.elements ∧
        state.view.parent element = some block.owner ∧
        state.view.side element = block.side := by
  obtain ⟨block, hBlock, hElement⟩ :=
    mem_allElements_iff.mp assigned
  have hStructural := valid.2 block hBlock
  exact ⟨block, hBlock, hElement,
    hStructural.parent_eq hElement,
    hStructural.side_eq hElement⟩

theorem Valid.root_not_mem {n : ℕ} {state : State n}
    {params : Interface.Parameters} (valid : state.Valid params) :
    state.view.root ∉ state.allElements := by
  intro hRoot
  obtain ⟨block, _, _, hParent, _⟩ :=
    valid.assigned_placement hRoot
  rw [state.view.root_parent] at hParent
  simp at hParent

theorem Valid.assigned_or_detached {n : ℕ} {state : State n}
    {params : Interface.Parameters} (_valid : state.Valid params)
    (element : Element n) (notRoot : element ≠ state.view.root) :
    element ∈ state.allElements ∨ state.Detached element := by
  by_cases assigned : element ∈ state.allElements
  · exact Or.inl assigned
  · exact Or.inr
      ⟨state.view.parent_ne_none_of_ne_root notRoot, assigned⟩

theorem Stable.valid {n : ℕ} {state : State n}
    {params : Interface.Parameters} (stable : state.Stable params) :
    state.Valid params :=
  stable.1

theorem Stable.noDetached {n : ℕ} {state : State n}
    {params : Interface.Parameters} (stable : state.Stable params)
    (element : Element n) :
    ¬state.Detached element := by
  intro hDetached
  exact hDetached.2 ((stable.2.1 element).2 hDetached.1)

theorem Stable.root_not_mem {n : ℕ} {state : State n}
    {params : Interface.Parameters} (stable : state.Stable params) :
    state.view.root ∉ state.allElements := by
  rw [stable.2.1]
  simp [state.view.root_parent]

theorem Stable.value_eq_transientContractedGap
    {n : ℕ} {state : State n} {params : Interface.Parameters}
    (stable : state.Stable params)
    {block : Block n} (hBlock : block ∈ state.blocks)
    {element : Element n} (hElement : element ∈ block.elements) :
    state.value element =
      Analysis.transientContractedGap
        (state.view.rawGap element) block.intervalGap :=
  stable.2.2.2.2.2.2 block hBlock element hElement

end State

end Splay.Lazy
