import Splay.Lazy.SideTransferGeometry
import Splay.Accounting.PairingSourceSublist

namespace Splay.Lazy

namespace Block

/-- Nonempty shrinking intervals of the source side, excluding its isolated
boundary singleton, are transferred as whole blocks. -/
def SelectedForSideTransfer {n : ℕ} (source boundary : Element n) (side : Side)
    (block : Block n) : Prop :=
  block.mode = .shrinking ∧ block.owner = source ∧ block.side = side ∧
    boundary ∉ block.elements ∧ block.elements ≠ []

noncomputable def sideTransferred {n : ℕ} (view : HeapView n)
    (source boundary : Element n) (side : Side) (block : Block n) : Block n := by
  classical
  exact if block.SelectedForSideTransfer source boundary side then
    block.transferred boundary side ((view.rank source : ℤ) - view.rank boundary)
  else block

@[simp]
theorem sideTransferred_toInterface {n : ℕ} (view : HeapView n)
    (source boundary : Element n) (side : Side) (block : Block n) :
    (block.sideTransferred view source boundary side).toInterface = block.toInterface := by
  unfold sideTransferred
  split <;> rfl

@[simp]
theorem sideTransferred_elements {n : ℕ} (view : HeapView n)
    (source boundary : Element n) (side : Side) (block : Block n) :
    (block.sideTransferred view source boundary side).elements = block.elements := by
  unfold sideTransferred
  split <;> rfl

@[simp]
theorem sideTransferred_mode {n : ℕ} (view : HeapView n)
    (source boundary : Element n) (side : Side) (block : Block n) :
    (block.sideTransferred view source boundary side).mode = block.mode := by
  unfold sideTransferred
  split <;> rfl

theorem sideTransferred_of_growing {n : ℕ} (view : HeapView n)
    (source boundary : Element n) (side : Side) (block : Block n)
    (growing : block.mode = .growing) :
    block.sideTransferred view source boundary side = block := by
  simp [sideTransferred, SelectedForSideTransfer, growing]

end Block

namespace State

/-- A whole-side transfer preserves each block ID, its payload, creator and
pass counter. It changes only the selected placements and their gap offsets. -/
noncomputable def transferSide {n : ℕ} (state : State n)
    {source boundary : Element n} {side : Side}
    (geometry : SideTransferGeometry state.view source boundary side)
    (ordered : state.view.HeapOrdered) : State n where
  view := geometry.after ordered
  blocks := state.blocks.map (Block.sideTransferred state.view source boundary side)
  value := state.value

@[simp]
theorem transferSide_toInterface {n : ℕ} (state : State n)
    {source boundary : Element n} {side : Side}
    (geometry : SideTransferGeometry state.view source boundary side)
    (ordered : state.view.HeapOrdered) :
    (state.transferSide geometry ordered).toInterface = state.toInterface := by
  unfold transferSide toInterface
  congr 1
  simp [List.map_map, Function.comp_def]

@[simp]
theorem transferSide_allElements {n : ℕ} (state : State n)
    {source boundary : Element n} {side : Side}
    (geometry : SideTransferGeometry state.view source boundary side)
    (ordered : state.view.HeapOrdered) :
    (state.transferSide geometry ordered).allElements = state.allElements := by
  simp [transferSide, allElements, List.flatMap_map]

end State

namespace SideTransferGeometry

variable {n : ℕ} {params : Interface.Parameters} {state : State n}
  {source boundary : Element n} {side : Side}
  (geometry : SideTransferGeometry state.view source boundary side)
  (stable : state.Stable params)

private theorem fullOrder (view : HeapView n) (assigned : List (Element n))
    (complete : ∀ element, element ∈ assigned ↔ view.parent element ≠ none)
    (owner : Element n) (side : Side) :
    view.attachedTopDown assigned owner side = view.topDown owner side := by
  apply List.filter_eq_self.mpr
  intro element member
  have parent := (view.mem_topDown_iff.mp member).1
  simp only [decide_eq_true_eq]
  exact (complete element).mpr (by simp [parent])

include geometry stable in
theorem transferSide_complete : (state.transferSide geometry stable.2.2.1).Complete := by
  intro element
  rw [State.transferSide_allElements, stable.2.1 element]
  change state.view.parent element ≠ none ↔ (geometry.after stable.2.2.1).parent element ≠ none
  rw [geometry.after_parent]
  by_cases moved : element ∈ geometry.moved
  · simp [moved, (geometry.moved_parent_side moved).1]
  · simp [moved]

include stable in
private theorem before_fullOrder (owner : Element n) (side : Side) :
    state.view.attachedTopDown state.allElements owner side = state.view.topDown owner side :=
  fullOrder _ _ stable.2.1 owner side

private theorem after_fullOrder (owner : Element n) (childSide : Side) :
    (geometry.after stable.2.2.1).attachedTopDown state.allElements owner childSide =
      (geometry.after stable.2.2.1).topDown owner childSide := by
  apply fullOrder
  intro element
  have complete := geometry.transferSide_complete stable element
  rw [State.transferSide_allElements] at complete
  exact complete

include geometry stable in
theorem selected_members {block : Block n} (member : block ∈ state.blocks)
    (selected : block.SelectedForSideTransfer source boundary side) :
    ∀ element ∈ block.elements, element ∈ geometry.moved := by
  intro element inside
  have inOrder := (stable.1.2 block member).1.mem inside
  rw [before_fullOrder stable, selected.2.1, selected.2.2.1, geometry.decomposition] at inOrder
  rcases List.mem_append.mp inOrder with moved | singleton
  · exact moved
  · have equal : element = boundary := by simpa using singleton
    exact (selected.2.2.2.1 (equal ▸ inside)).elim

include geometry stable in
noncomputable def selected_transfer {block : Block n} (member : block ∈ state.blocks)
    (selected : block.SelectedForSideTransfer source boundary side) :
    Block.IsTransfer state.view (geometry.after stable.2.2.1) block
      (block.sideTransferred state.view source boundary side) := by
  rw [Block.sideTransferred, if_pos selected]
  apply Block.transferred_isTransfer _ _ _ _ _ _ selected.1
  intro element inside
  have moved := geometry.selected_members stable member selected element inside
  simp only [HeapView.rawGap, geometry.after_parent, moved, ↓reduceIte,
    (geometry.moved_parent_side moved).1]
  change (state.view.rank element : ℤ) - state.view.rank boundary =
    (state.view.rank element : ℤ) - state.view.rank source +
      ((state.view.rank source : ℤ) - state.view.rank boundary)
  omega

include geometry stable in
theorem selected_valid {block : Block n} (member : block ∈ state.blocks)
    (selected : block.SelectedForSideTransfer source boundary side) :
    (block.sideTransferred state.view source boundary side).StructurallyValid
      (geometry.after stable.2.2.1) state.allElements := by
  apply (geometry.selected_transfer stable member selected).after_structurallyValid
    (stable.1.2 block member) selected.2.2.2.2
  rw [Block.sideTransferred, if_pos selected]
  change IsSegment block.elements
    ((geometry.after stable.2.2.1).attachedTopDown state.allElements boundary side)
  rw [geometry.after_fullOrder stable, geometry.boundary_topDown]
  have oldSegment := (stable.1.2 block member).1
  rw [before_fullOrder stable, selected.2.1, selected.2.2.1] at oldSegment
  have sublist : geometry.moved.Sublist (state.view.topDown source side) := by
    rw [geometry.decomposition]
    exact List.sublist_append_left _ _
  obtain ⟨front, back, decomposition⟩ := oldSegment.in_sublist sublist
    (state.view.topDown_nodup source side) (geometry.selected_members stable member selected)
  refine ⟨front, back ++ state.view.topDown boundary side, ?_⟩
  rw [decomposition]
  simp only [List.append_assoc]

/-- Both affected growing slots have already been converted and replaced by
empty growing intervals before the transfer. -/
def EmptyGrowingSlots (_geometry : SideTransferGeometry state.view source boundary side) : Prop :=
  ∀ block ∈ state.blocks, block.mode = .growing →
    (block.owner = source ∨ block.owner = boundary) → block.side = side → block.elements = []

/-- The bottommost child was isolated by the request preparation. -/
def IsolatedBoundary (_geometry : SideTransferGeometry state.view source boundary side) : Prop :=
  ∀ block ∈ state.blocks, boundary ∈ block.elements → block.elements = [boundary]

include geometry stable in
theorem stationary_not_moved (emptySlots : geometry.EmptyGrowingSlots)
    (isolated : geometry.IsolatedBoundary) {block : Block n} (member : block ∈ state.blocks)
    (stationary : ¬ block.SelectedForSideTransfer source boundary side) :
    ∀ element ∈ block.elements, element ∉ geometry.moved := by
  intro element inside moved
  have valid := stable.1.2 block member
  have placement := geometry.moved_parent_side moved
  have ownerEq : block.owner = source := Option.some.inj ((valid.parent_eq inside).symm.trans placement.1)
  have sideEq : block.side = side := (valid.side_eq inside).symm.trans placement.2
  have nonempty : block.elements ≠ [] := List.ne_nil_of_mem inside
  have excludes : boundary ∉ block.elements := by
    intro boundaryMember
    rw [isolated block member boundaryMember] at inside
    have equal : element = boundary := by simpa using inside
    exact geometry.boundary_not_moved (equal ▸ moved)
  cases mode : block.mode with
  | shrinking => exact stationary ⟨mode, ownerEq, sideEq, excludes, nonempty⟩
  | growing => exact nonempty (emptySlots block member mode (Or.inl ownerEq) sideEq)

include geometry stable in
theorem stationary_rawGap (emptySlots : geometry.EmptyGrowingSlots)
    (isolated : geometry.IsolatedBoundary) {block : Block n} (member : block ∈ state.blocks)
    (stationary : ¬ block.SelectedForSideTransfer source boundary side) :
    ∀ element ∈ block.elements,
      (geometry.after stable.2.2.1).rawGap element = state.view.rawGap element := by
  intro element inside
  have outside := geometry.stationary_not_moved stable emptySlots isolated member stationary element inside
  simp only [HeapView.rawGap, geometry.after_parent, outside, ↓reduceIte]
  rfl

include geometry stable in
theorem stationary_valid (emptySlots : geometry.EmptyGrowingSlots)
    (isolated : geometry.IsolatedBoundary) {block : Block n} (member : block ∈ state.blocks)
    (stationary : ¬ block.SelectedForSideTransfer source boundary side) :
    block.StructurallyValid (geometry.after stable.2.2.1) state.allElements := by
  apply (stable.1.2 block member).of_rawGap_eq _
    (geometry.stationary_rawGap stable emptySlots isolated member stationary)
  rw [geometry.after_fullOrder stable]
  have oldSegment := (stable.1.2 block member).1
  rw [before_fullOrder stable] at oldSegment
  by_cases sameSide : block.side = side
  · by_cases atSource : block.owner = source
    · rw [atSource, sameSide, geometry.source_topDown]
      by_cases empty : block.elements = []
      · rw [empty]; exact IsSegment.nil _
      · obtain ⟨element, inside⟩ := List.exists_mem_of_ne_nil block.elements empty
        have orderMember := oldSegment.mem inside
        rw [atSource, sameSide, geometry.decomposition] at orderMember
        have outside := geometry.stationary_not_moved stable emptySlots isolated member stationary element inside
        have equal : element = boundary := by simpa [outside] using orderMember
        rw [isolated block member (equal ▸ inside)]
        exact ⟨[], [], by simp⟩
    · by_cases atBoundary : block.owner = boundary
      · rw [atBoundary, sameSide, geometry.boundary_topDown]
        obtain ⟨front, back, decomposition⟩ := oldSegment
        refine ⟨geometry.moved ++ front, back, ?_⟩
        rw [atBoundary, sameSide] at decomposition
        rw [decomposition]
        simp only [List.append_assoc]
      · rw [geometry.other_topDown _ _ _ (Or.inl atSource) (Or.inl atBoundary)]
        exact oldSegment
  · rw [geometry.other_topDown _ _ _ (Or.inr sameSide) (Or.inr sameSide)]
    exact oldSegment

include geometry stable in
theorem transferSide_valid (emptySlots : geometry.EmptyGrowingSlots)
    (isolated : geometry.IsolatedBoundary) :
    (state.transferSide geometry stable.2.2.1).Valid params := by
  constructor
  · rw [State.transferSide_toInterface]
    exact stable.1.1
  · intro block member
    obtain ⟨oldBlock, oldMember, rfl⟩ := List.mem_map.mp member
    rw [State.transferSide_allElements]
    by_cases selected : oldBlock.SelectedForSideTransfer source boundary side
    · exact geometry.selected_valid stable oldMember selected
    · rw [Block.sideTransferred, if_neg selected]
      exact geometry.stationary_valid stable emptySlots isolated oldMember selected

include geometry stable in
theorem transferSide_values (emptySlots : geometry.EmptyGrowingSlots)
    (isolated : geometry.IsolatedBoundary) :
    (state.transferSide geometry stable.2.2.1).ValuesRealizeGaps := by
  constructor
  · exact stable.2.2.2.2.2.1
  · intro block member element inside
    obtain ⟨oldBlock, oldMember, rfl⟩ := List.mem_map.mp member
    rw [Block.sideTransferred_elements] at inside
    change state.value element = Analysis.transientContractedGap
      ((geometry.after stable.2.2.1).rawGap element)
      (oldBlock.sideTransferred state.view source boundary side).intervalGap
    by_cases selected : oldBlock.SelectedForSideTransfer source boundary side
    · rw [(geometry.selected_transfer stable oldMember selected).contractedGap_eq inside]
      exact stable.2.2.2.2.2.2 oldBlock oldMember element inside
    · rw [Block.sideTransferred, if_neg selected,
        geometry.stationary_rawGap stable emptySlots isolated oldMember selected element inside]
      exact stable.2.2.2.2.2.2 oldBlock oldMember element inside

include geometry stable in
theorem transferSide_oneGrowingPerSide :
    (state.transferSide geometry stable.2.2.1).OneGrowingPerSide := by
  intro owner childSide
  obtain ⟨oldId, oldProperty, unique⟩ := stable.2.2.2.1 owner childSide
  dsimp only at oldProperty
  let newId : Fin (state.transferSide geometry stable.2.2.1).blocks.length :=
    ⟨oldId.val, by simpa [State.transferSide] using oldId.isLt⟩
  have fixed : (state.transferSide geometry stable.2.2.1).blocks.get newId = state.blocks.get oldId := by
    simp only [State.transferSide, List.get_eq_getElem, List.getElem_map]
    exact Block.sideTransferred_of_growing _ _ _ _ _ oldProperty.1
  refine ⟨newId, ?_, ?_⟩
  · dsimp only
    rw [fixed]
    exact oldProperty
  · intro candidate property
    dsimp only at property
    let oldCandidate : Fin state.blocks.length :=
      ⟨candidate.val, by simpa [State.transferSide] using candidate.isLt⟩
    have growing : (state.blocks.get oldCandidate).mode = .growing := by
      simpa [State.transferSide, oldCandidate] using property.1
    have candidateFixed : (state.transferSide geometry stable.2.2.1).blocks.get candidate =
        state.blocks.get oldCandidate := by
      simp only [State.transferSide, List.get_eq_getElem, List.getElem_map]
      exact Block.sideTransferred_of_growing _ _ _ _ _ growing
    rw [candidateFixed] at property
    have equal := unique oldCandidate property
    apply Fin.ext
    exact congrArg (fun index : Fin state.blocks.length => index.val) equal

include geometry stable in
theorem transferSide_growingTopmost (emptySlots : geometry.EmptyGrowingSlots) :
    (state.transferSide geometry stable.2.2.1).GrowingTopmost := by
  intro newId
  dsimp only
  intro newGrowing
  let oldId : Fin state.blocks.length :=
    ⟨newId.val, by simpa [State.transferSide] using newId.isLt⟩
  let oldBlock := state.blocks.get oldId
  have growing : oldBlock.mode = .growing := by
    simpa [State.transferSide, oldBlock, oldId] using newGrowing
  have fixed : (state.transferSide geometry stable.2.2.1).blocks.get newId = oldBlock := by
    simp only [State.transferSide, List.get_eq_getElem, List.getElem_map]
    exact Block.sideTransferred_of_growing _ _ _ _ _ growing
  rw [fixed]
  have member : oldBlock ∈ state.blocks := List.get_mem _ _
  change ∃ suffix, (geometry.after stable.2.2.1).topDown oldBlock.owner oldBlock.side = oldBlock.elements ++ suffix
  by_cases sameSide : oldBlock.side = side
  · by_cases affected : oldBlock.owner = source ∨ oldBlock.owner = boundary
    · rw [emptySlots oldBlock member growing affected sameSide]
      exact ⟨(geometry.after stable.2.2.1).topDown oldBlock.owner oldBlock.side, by simp⟩
    · have notSource : oldBlock.owner ≠ source := fun equal => affected (Or.inl equal)
      have notBoundary : oldBlock.owner ≠ boundary := fun equal => affected (Or.inr equal)
      rw [geometry.other_topDown _ _ _ (Or.inl notSource) (Or.inl notBoundary)]
      exact stable.2.2.2.2.1 oldId growing
  · rw [geometry.other_topDown _ _ _ (Or.inr sameSide) (Or.inr sameSide)]
    exact stable.2.2.2.2.1 oldId growing

include geometry stable in
/-- The actual simultaneous transfer is stable, including complete coverage,
unique growing slots and exact contracted-gap values. -/
theorem transferSide_stable (emptySlots : geometry.EmptyGrowingSlots)
    (isolated : geometry.IsolatedBoundary) :
    (state.transferSide geometry stable.2.2.1).Stable params :=
  ⟨geometry.transferSide_valid stable emptySlots isolated,
    geometry.transferSide_complete stable, geometry.after_ordered stable.2.2.1,
    geometry.transferSide_oneGrowingPerSide stable,
    geometry.transferSide_growingTopmost stable emptySlots,
    geometry.transferSide_values stable emptySlots isolated⟩

include geometry stable in
/-- No interface operation or value adjustment is hidden in a side transfer:
its entire rich trace consists of one checked silent step. -/
theorem transferSide_trace (emptySlots : geometry.EmptyGrowingSlots)
    (isolated : geometry.IsolatedBoundary) :
    Trace params state [.silent] (state.transferSide geometry stable.2.2.1) := by
  have valid := geometry.transferSide_valid stable emptySlots isolated
  exact Trace.cons (Step.silent stable.1 valid (State.transferSide_toInterface _ _ _).symm)
    (Trace.nil valid)

include geometry stable in
/-- Finding the isolated boundary block at its persistent ID suffices for
all other blocks to satisfy the singleton exclusion used by the transfer. -/
theorem isolatedBoundary_of_found {id : Interface.BlockId} {block : Block n}
    (found : state.blocks[id]? = some block) (singleton : block.elements = [boundary]) :
    geometry.IsolatedBoundary := by
  intro other member contains
  obtain ⟨otherId, otherFound⟩ := List.mem_iff_getElem?.mp member
  have equal := stable.1.blockId_eq_of_element_mem found (by simp [singleton]) otherFound contains
  rw [← equal, found] at otherFound
  have blocksEqual := Option.some.inj otherFound
  rw [← blocksEqual, singleton]

end SideTransferGeometry
end Splay.Lazy
