import Splay.Lazy.InitializedExecution
import Splay.Lazy.SafeInsert

namespace Splay.Lazy.Canonical

open Splay.Rank

/-- Number of pending owner-side placements belonging to one owner. -/
def placementCount {n : ℕ}
    (placements : List (Element n × Side)) (owner : Element n) : ℕ :=
  (placements.filter fun placement =>
    decide (placement.1 = owner)).length

@[simp]
theorem placementCount_nil {n : ℕ} (owner : Element n) :
    placementCount ([] : List (Element n × Side)) owner = 0 :=
  rfl

@[simp]
theorem placementCount_cons {n : ℕ}
    (placement : Element n × Side)
    (placements : List (Element n × Side)) (owner : Element n) :
    placementCount (placement :: placements) owner =
      placementCount placements owner +
        if placement.1 = owner then 1 else 0 := by
  by_cases equal : placement.1 = owner
  · simp [placementCount, equal]
  · simp [placementCount, equal]

/-- Append one empty growing block for every placement, in list order. -/
def createPlacements {n : ℕ} :
    State n → List (Element n × Side) → State n
  | state, [] => state
  | state, placement :: placements =>
      createPlacements
        (state.create placement.1 placement.2) placements

/-- Visible create events emitted by `createPlacements`. -/
def createPlacementEvents {n : ℕ} :
    List (Element n × Side) → List (Event n)
  | [] => []
  | placement :: placements =>
      .operation (.create placement.1) ::
        createPlacementEvents placements

@[simp]
theorem createPlacements_nil {n : ℕ} (state : State n) :
    createPlacements state [] = state :=
  rfl

@[simp]
theorem createPlacements_cons {n : ℕ} (state : State n)
    (placement : Element n × Side)
    (placements : List (Element n × Side)) :
    createPlacements state (placement :: placements) =
      createPlacements
        (state.create placement.1 placement.2) placements :=
  rfl

@[simp]
theorem createPlacementEvents_nil {n : ℕ} :
    createPlacementEvents ([] : List (Element n × Side)) = [] :=
  rfl

@[simp]
theorem createPlacementEvents_cons {n : ℕ}
    (placement : Element n × Side)
    (placements : List (Element n × Side)) :
    createPlacementEvents (placement :: placements) =
      .operation (.create placement.1) ::
        createPlacementEvents placements :=
  rfl

/-- Creating one empty block increments exactly its owner's growing count. -/
theorem create_growingCount {n : ℕ} (state : State n)
    (owner queried : Element n) (side : Side) :
    (state.create owner side).toInterface.growingCount queried =
      state.toInterface.growingCount queried +
        if owner = queried then 1 else 0 := by
  by_cases equal : owner = queried
  · subst queried
    simp
      [State.create, State.toInterface,
        Interface.State.growingCount, Block.emptyGrowing,
        Block.toInterface]
  · simp
      [State.create, State.toInterface,
        Interface.State.growingCount, Block.emptyGrowing,
        Block.toInterface, equal]

/-- The created block list is the old list followed by the requested blocks. -/
@[simp]
theorem createPlacements_blocks {n : ℕ} (state : State n)
    (placements : List (Element n × Side)) :
    (createPlacements state placements).blocks =
      state.blocks ++
        placements.map fun placement =>
          Block.emptyGrowing placement.1 placement.2 := by
  induction placements generalizing state with
  | nil =>
      simp
  | cons placement placements ih =>
      rw [createPlacements_cons, ih]
      simp [State.create, List.append_assoc]

@[simp]
theorem createPlacements_view {n : ℕ} (state : State n)
    (placements : List (Element n × Side)) :
    (createPlacements state placements).view = state.view := by
  induction placements generalizing state with
  | nil =>
      rfl
  | cons placement placements ih =>
      rw [createPlacements_cons, ih]
      rfl

@[simp]
theorem createPlacements_value {n : ℕ} (state : State n)
    (placements : List (Element n × Side)) :
    (createPlacements state placements).value = state.value := by
  induction placements generalizing state with
  | nil =>
      rfl
  | cons placement placements ih =>
      rw [createPlacements_cons, ih]
      rfl

/--
Bulk creation is a genuine rich trace whenever the initial growing counts plus
all pending placements fit under the per-creator limit.
-/
theorem createPlacements_trace {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (placements : List (Element n × Side))
    (valid : state.Valid params)
    (capacity :
      ∀ owner,
        state.toInterface.growingCount owner +
            placementCount placements owner ≤
          params.growingLimit) :
    Trace params state (createPlacementEvents placements)
      (createPlacements state placements) := by
  induction placements generalizing state with
  | nil =>
      exact Trace.nil valid
  | cons placement placements ih =>
      have room :
          state.toInterface.growingCount placement.1 <
            params.growingLimit := by
        have bound := capacity placement.1
        simp only [placementCount_cons, if_pos] at bound
        omega
      have headStep :
          Step params state
            (.operation (.create placement.1))
            (state.create placement.1 placement.2) :=
        state.create_step placement.1 placement.2 valid room
      have afterValid :
          (state.create placement.1 placement.2).Valid params :=
        headStep.after_valid
      have tailCapacity :
          ∀ owner,
            (state.create placement.1
                placement.2).toInterface.growingCount owner +
                  placementCount placements owner ≤
              params.growingLimit := by
        intro owner
        rw [create_growingCount]
        have bound := capacity owner
        rw [placementCount_cons] at bound
        by_cases equal : placement.1 = owner
        · simp only [if_pos equal] at bound ⊢
          omega
        · simp only [if_neg equal] at bound ⊢
          exact bound
      exact
        Trace.cons headStep
          (ih (state.create placement.1 placement.2)
            afterValid tailCapacity)

/-- State obtained after creating all canonical owner-side blocks, still empty. -/
noncomputable def emptyCanonicalBlocksState {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) : State n :=
  createPlacements (emptyCanonicalState snapshot tree)
    (ownerSidePairs n)

@[simp]
theorem emptyCanonicalBlocksState_view {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (emptyCanonicalBlocksState snapshot tree).view =
      canonicalHeapView snapshot tree := by
  simp [emptyCanonicalBlocksState]

@[simp]
theorem emptyCanonicalBlocksState_value {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (emptyCanonicalBlocksState snapshot tree).value =
      canonicalValue snapshot tree := by
  simp [emptyCanonicalBlocksState]

@[simp]
theorem emptyCanonicalBlocksState_blocks {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (emptyCanonicalBlocksState snapshot tree).blocks =
      (ownerSidePairs n).map fun placement =>
        Block.emptyGrowing placement.1 placement.2 := by
  simp [emptyCanonicalBlocksState]

/-- All canonical empty blocks can be created from the genuine initial state. -/
theorem emptyCanonicalBlocksState_trace {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    Trace params (emptyCanonicalState snapshot tree)
      (createPlacementEvents (ownerSidePairs n))
      (emptyCanonicalBlocksState snapshot tree) := by
  apply
    createPlacements_trace
      (emptyCanonicalState snapshot tree) (ownerSidePairs n)
      (emptyCanonicalState_valid snapshot tree params valueBound)
  intro owner
  have pairCount :
      placementCount (ownerSidePairs n) owner = 2 := by
    exact ownerSidePairs_filter_owner_length owner
  simp
    [emptyCanonicalState, State.toInterface,
      Interface.State.growingCount, pairCount]
  exact growingLimit

/-- The placement metadata retained by insertion. -/
def blockPlacement {n : ℕ} (block : Block n) : Element n × Side :=
  (block.owner, block.side)

@[simp]
theorem blockPlacement_emptyGrowing {n : ℕ}
    (owner : Element n) (side : Side) :
    blockPlacement (Block.emptyGrowing owner side) = (owner, side) :=
  rfl

/--
No two rich blocks occupy the same heap-parent side.  This is the small
structural invariant needed while the initially empty canonical blocks are
populated.
-/
def UniquePlacements {n : ℕ} (state : State n) : Prop :=
  (state.blocks.map blockPlacement).Nodup

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

/-- Membership in the global assigned list after a found insertion. -/
theorem mem_insert_allElements_iff {n : ℕ}
    (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (element queried : Element n)
    (found : state.blocks[blockId]? = some block) :
    queried ∈ (state.insert blockId element).allElements ↔
      queried = element ∨ queried ∈ state.allElements := by
  have permutation :
      (state.insert blockId element).allElements.Perm
        (element :: state.allElements) := by
    exact
      inserted_allElements_perm state.blocks blockId block element found
  rw [permutation.mem_iff]
  simp

/-- Insertion changes no block placement metadata. -/
theorem insert_blockPlacements {n : ℕ}
    (state : State n) (blockId : Interface.BlockId)
    (element : Element n) :
    (state.insert blockId element).blocks.map blockPlacement =
      state.blocks.map blockPlacement := by
  unfold State.insert
  change
    (state.blocks.modify blockId fun block =>
        block.inserted element).map blockPlacement =
      state.blocks.map blockPlacement
  induction state.blocks generalizing blockId with
  | nil =>
      cases blockId <;> rfl
  | cons head tail ih =>
      cases blockId with
      | zero =>
          simp [Block.inserted, blockPlacement]
      | succ blockId =>
          simp [ih]

/-- Inserting into a block preserves uniqueness of owner-side placements. -/
theorem UniquePlacements.insert {n : ℕ} {state : State n}
    (unique : UniquePlacements state)
    (blockId : Interface.BlockId) (element : Element n) :
    UniquePlacements (state.insert blockId element) := by
  rw [UniquePlacements, insert_blockPlacements]
  exact unique

/--
Under unique placements, two in-bounds blocks with the same owner and side
have the same index.
-/
theorem UniquePlacements.index_eq_of_placement_eq {n : ℕ}
    {state : State n} (unique : UniquePlacements state)
    (first second : Fin state.blocks.length)
    (placementEq :
      blockPlacement (state.blocks.get first) =
        blockPlacement (state.blocks.get second)) :
    first.val = second.val := by
  have mappedNodup :
      (state.blocks.map blockPlacement).Nodup :=
    unique
  have mappedEq :
      (state.blocks.map blockPlacement)[first.val] =
        (state.blocks.map blockPlacement)[second.val] := by
    simpa only [List.get_eq_getElem, List.getElem_map] using placementEq
  exact mappedNodup.getElem_inj_iff.mp mappedEq

/-- A contiguous segment is, in particular, a sublist. -/
theorem IsSegment.sublist {α : Type*} {inside whole : List α}
    (segment : IsSegment inside whole) :
    inside.Sublist whole := by
  obtain ⟨front, back, rfl⟩ := segment
  exact
    (List.sublist_append_left inside back).trans
      (by
        simpa only [List.append_assoc] using
          List.sublist_append_right front (inside ++ back))

/--
Filtering the ambient list preserves a contiguous segment when every element
of the segment passes the filter.
-/
theorem IsSegment.filter_of_all {α : Type*}
    {inside whole : List α} {predicate : α → Bool}
    (segment : IsSegment inside whole)
    (passes : ∀ element ∈ inside, predicate element = true) :
    IsSegment inside (whole.filter predicate) := by
  obtain ⟨front, back, rfl⟩ := segment
  refine
    ⟨front.filter predicate, back.filter predicate, ?_⟩
  rw [List.filter_append, List.filter_append,
    List.filter_eq_self.mpr passes]

/--
With unique owner-side placements, a segment-respecting insertion is
automatically globally unassigned, remains a segment after assignment
filtering, and leaves every other block structurally valid.  Consequently the
value-adjusting safe-insert construction supplies a genuine trace.
-/
theorem safeInsert_trace_of_uniquePlacements {n : ℕ}
    {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (element : Element n)
    (valid : state.Valid params)
    (unique : UniquePlacements state)
    (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing)
    (plannedSegment :
      IsSegment (block.inserted element).elements
        (state.view.topDown block.owner block.side))
    (elementGap : 0 ≤ state.view.rawGap element) :
    Trace params state (state.safeInsertEvents blockId block element) (state.insert blockId element) := by
  obtain ⟨blockIdLt, selectedEq⟩ :=
    List.getElem?_eq_some_iff.mp found
  let selectedId : Fin state.blocks.length :=
    ⟨blockId, blockIdLt⟩
  have selectedGet :
      state.blocks.get selectedId = block := by
    simpa only [selectedId, List.get_eq_getElem] using selectedEq
  have blockMember : block ∈ state.blocks :=
    List.mem_iff_getElem?.2 ⟨blockId, found⟩
  have elementInside :
      element ∈ (block.inserted element).elements := by
    simp [Block.inserted]
  have elementTopDown :
      element ∈ state.view.topDown block.owner block.side :=
    plannedSegment.mem elementInside
  have selectedParent :
      state.view.parent element = some block.owner :=
    state.view.mem_topDown_parent elementTopDown
  have selectedSide :
      state.view.side element = block.side :=
    state.view.mem_topDown_side elementTopDown
  have insertedNodup :
      (block.inserted element).elements.Nodup :=
    (Splay.Lazy.Canonical.IsSegment.sublist plannedSegment).nodup
      (state.view.topDown_nodup block.owner block.side)
  have elementNotInBlock : element ∉ block.elements := by
    have consNodup :
        (element :: block.elements).Nodup := by
      simpa only [Block.inserted] using insertedNodup
    exact (List.nodup_cons.mp consNodup).1
  have unassigned : element ∉ state.allElements := by
    intro assigned
    obtain
      ⟨otherBlock, otherMember, elementMember,
        otherParent, otherSide⟩ :=
      valid.assigned_placement assigned
    obtain ⟨otherId, otherGet⟩ :=
      List.mem_iff_get.mp otherMember
    have ownerEq : block.owner = otherBlock.owner :=
      Option.some.inj (selectedParent.symm.trans otherParent)
    have sideEq : block.side = otherBlock.side :=
      selectedSide.symm.trans otherSide
    have placementEq :
        blockPlacement (state.blocks.get selectedId) =
          blockPlacement (state.blocks.get otherId) := by
      rw [selectedGet, otherGet]
      simp only [blockPlacement, Prod.mk.injEq]
      exact ⟨ownerEq, sideEq⟩
    have indexEq : selectedId = otherId := by
      apply Fin.ext
      exact
        unique.index_eq_of_placement_eq
          selectedId otherId placementEq
    have blocksEq : block = otherBlock := by
      rw [← selectedGet, ← otherGet, indexEq]
    exact elementNotInBlock (by
      simpa only [blocksEq] using elementMember)
  have afterSegment :
      IsSegment (block.inserted element).elements
        (state.view.attachedTopDown
          (state.insert blockId element).allElements
          block.owner block.side) := by
    unfold HeapView.attachedTopDown
    apply
      Splay.Lazy.Canonical.IsSegment.filter_of_all plannedSegment
    intro queried queriedMember
    simp only [decide_eq_true_eq]
    rw [mem_insert_allElements_iff
      state blockId block element queried found]
    change queried ∈ element :: block.elements at queriedMember
    simp only [List.mem_cons] at queriedMember
    rcases queriedMember with rfl | oldMember
    · exact Or.inl rfl
    · exact
        Or.inr
          (State.mem_allElements_iff.mpr
            ⟨block, blockMember, oldMember⟩)
  have otherValid :
      ∀ id : Fin state.blocks.length, blockId ≠ id.val →
        (state.blocks.get id).StructurallyValid state.view
          (state.insert blockId element).allElements := by
    intro id different
    let otherBlock := state.blocks.get id
    have oldValid :
        otherBlock.StructurallyValid state.view state.allElements :=
      valid.2 otherBlock (List.get_mem state.blocks id)
    have elementNotOtherTopDown :
        element ∉
          state.view.topDown otherBlock.owner otherBlock.side := by
      intro otherTopDown
      have otherParent :
          state.view.parent element = some otherBlock.owner :=
        state.view.mem_topDown_parent otherTopDown
      have otherSide :
          state.view.side element = otherBlock.side :=
        state.view.mem_topDown_side otherTopDown
      have ownerEq : block.owner = otherBlock.owner :=
        Option.some.inj (selectedParent.symm.trans otherParent)
      have sideEq : block.side = otherBlock.side :=
        selectedSide.symm.trans otherSide
      have placementEq :
          blockPlacement (state.blocks.get selectedId) =
            blockPlacement (state.blocks.get id) := by
        rw [selectedGet]
        change
          (block.owner, block.side) =
            (otherBlock.owner, otherBlock.side)
        exact Prod.ext ownerEq sideEq
      have indexEq :
          selectedId.val = id.val :=
        unique.index_eq_of_placement_eq
          selectedId id placementEq
      exact different (by
        simpa only [selectedId] using indexEq)
    have attachedEq :
        state.view.attachedTopDown
            (state.insert blockId element).allElements
            otherBlock.owner otherBlock.side =
          state.view.attachedTopDown state.allElements
            otherBlock.owner otherBlock.side := by
      unfold HeapView.attachedTopDown
      apply List.filter_congr
      intro queried queriedTopDown
      apply decide_eq_decide.mpr
      rw [mem_insert_allElements_iff
        state blockId block element queried found]
      constructor
      · intro afterMember
        rcases afterMember with equal | oldMember
        · subst queried
          exact False.elim (elementNotOtherTopDown queriedTopDown)
        · exact oldMember
      · exact Or.inr
    exact
      ⟨by
        rw [attachedEq]
        exact oldValid.1,
       oldValid.2⟩
  exact
    state.safeInsert_trace blockId block element valid found
      growing unassigned elementGap afterSegment otherValid

theorem exists_safeInsert_trace_of_uniquePlacements {n : ℕ}
    {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (element : Element n)
    (valid : state.Valid params)
    (unique : UniquePlacements state)
    (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing)
    (plannedSegment :
      IsSegment (block.inserted element).elements
        (state.view.topDown block.owner block.side))
    (elementGap : 0 ≤ state.view.rawGap element) :
    ∃ events : List (Event n),
      Trace params state events (state.insert blockId element) := by
  exact ⟨state.safeInsertEvents blockId block element,
    safeInsert_trace_of_uniquePlacements state blockId block element valid unique found growing plannedSegment elementGap⟩

/-- Repeatedly prepend a list of elements to one fixed rich block. -/
def insertMany {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) : List (Element n) → State n
  | [] => state
  | element :: elements =>
      insertMany (state.insert blockId element) blockId elements

@[simp]
theorem insertMany_nil {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) :
    insertMany state blockId [] = state :=
  rfl

@[simp]
theorem insertMany_cons {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (element : Element n)
    (elements : List (Element n)) :
    insertMany state blockId (element :: elements) =
      insertMany (state.insert blockId element) blockId elements :=
  rfl

/-- The block payload produced by the same sequence of prepends. -/
def insertedManyBlock {n : ℕ} (block : Block n) :
    List (Element n) → Block n
  | [] => block
  | element :: elements =>
      insertedManyBlock (block.inserted element) elements

@[simp]
theorem insertedManyBlock_nil {n : ℕ} (block : Block n) :
    insertedManyBlock block [] = block :=
  rfl

@[simp]
theorem insertedManyBlock_cons {n : ℕ} (block : Block n)
    (element : Element n) (elements : List (Element n)) :
    insertedManyBlock block (element :: elements) =
      insertedManyBlock (block.inserted element) elements :=
  rfl

/-- Repeated insertion reverses the insertion sequence into the block. -/
theorem insertedManyBlock_eq {n : ℕ} (block : Block n)
    (elements : List (Element n)) :
    insertedManyBlock block elements =
      { block with
        elements := elements.reverse ++ block.elements } := by
  induction elements generalizing block with
  | nil =>
      simp
  | cons element elements ih =>
      rw [insertedManyBlock_cons, ih]
      simp only [Block.inserted, List.reverse_cons,
        List.singleton_append, List.append_assoc]

/-- The selected block after repeated found insertions. -/
theorem insertMany_found {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (block : Block n)
    (elements : List (Element n))
    (found : state.blocks[blockId]? = some block) :
    (insertMany state blockId elements).blocks[blockId]? =
      some (insertedManyBlock block elements) := by
  induction elements generalizing state block with
  | nil =>
      exact found
  | cons element elements ih =>
      apply ih (state.insert blockId element)
        (block.inserted element)
      simp [State.insert, found]

/-- Repeated insertion at one index leaves every other block unchanged. -/
theorem insertMany_found_of_ne {n : ℕ} (state : State n)
    (blockId otherId : Interface.BlockId)
    (elements : List (Element n))
    (different : blockId ≠ otherId) :
    (insertMany state blockId elements).blocks[otherId]? =
      state.blocks[otherId]? := by
  induction elements generalizing state with
  | nil =>
      rfl
  | cons element elements ih =>
      rw [insertMany_cons, ih]
      simp [State.insert, different]

@[simp]
theorem insertMany_view {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (elements : List (Element n)) :
    (insertMany state blockId elements).view = state.view := by
  induction elements generalizing state with
  | nil =>
      rfl
  | cons element elements ih =>
      rw [insertMany_cons, ih]
      rfl

@[simp]
theorem insertMany_value {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (elements : List (Element n)) :
    (insertMany state blockId elements).value = state.value := by
  induction elements generalizing state with
  | nil =>
      rfl
  | cons element elements ih =>
      rw [insertMany_cons, ih]
      rfl

@[simp]
theorem insertMany_blocks_length {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (elements : List (Element n)) :
    (insertMany state blockId elements).blocks.length =
      state.blocks.length := by
  induction elements generalizing state with
  | nil =>
      rfl
  | cons element elements ih =>
      rw [insertMany_cons, ih]
      simp [State.insert]

/-- Repeated insertion preserves unique owner-side placements. -/
theorem UniquePlacements.insertMany {n : ℕ} {state : State n}
    (unique : UniquePlacements state)
    (blockId : Interface.BlockId) (elements : List (Element n)) :
    UniquePlacements (insertMany state blockId elements) := by
  induction elements generalizing state with
  | nil =>
      exact unique
  | cons element elements ih =>
      exact
        ih (unique.insert blockId element)

/--
Populate one growing block by any finite insertion sequence whose reverse,
followed by the old block, is a segment of the placement's top-down list.
-/
/- Exact safe-insertion events for a fixed block, including value restoration. -/
def insertManyEvents {n : ℕ} (state : State n) (blockId : Interface.BlockId)
    (block : Block n) : List (Element n) → List (Event n)
  | [] => []
  | element :: elements => state.safeInsertEvents blockId block element ++
      insertManyEvents (state.insert blockId element) blockId (block.inserted element) elements

theorem insertMany_trace_of_uniquePlacements {n : ℕ}
    {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (elements : List (Element n))
    (valid : state.Valid params)
    (unique : UniquePlacements state)
    (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing)
    (plannedSegment :
      IsSegment (elements.reverse ++ block.elements)
        (state.view.topDown block.owner block.side))
    (elementGaps :
      ∀ element ∈ elements, 0 ≤ state.view.rawGap element) :
    Trace params state (insertManyEvents state blockId block elements)
      (insertMany state blockId elements) := by
  induction elements generalizing state block with
  | nil =>
      exact Trace.nil valid
  | cons element elements ih =>
      have rearrangedSegment :
          IsSegment
            (elements.reverse ++ (element :: block.elements))
            (state.view.topDown block.owner block.side) := by
        simpa only [List.reverse_cons, List.singleton_append,
          List.append_assoc] using plannedSegment
      have headSegment :
          IsSegment (block.inserted element).elements
            (state.view.topDown block.owner block.side) := by
        have dropped :=
          Splay.Lazy.IsSegment.drop rearrangedSegment
            elements.reverse.length
        simpa only [List.drop_left, Block.inserted] using dropped
      have headGap : 0 ≤ state.view.rawGap element :=
        elementGaps element (by simp)
      have headTrace :=
        safeInsert_trace_of_uniquePlacements
          state blockId block element valid unique found growing
          headSegment headGap
      have afterValid :
          (state.insert blockId element).Valid params :=
        headTrace.final_valid
      have afterUnique :
          UniquePlacements (state.insert blockId element) :=
        unique.insert blockId element
      have afterFound :
          (state.insert blockId element).blocks[blockId]? =
            some (block.inserted element) := by
        simp [State.insert, found]
      have afterGrowing :
          (block.inserted element).mode = .growing := by
        simpa only [Block.inserted] using growing
      have tailSegment :
          IsSegment
              (elements.reverse ++
                (block.inserted element).elements)
              ((state.insert blockId element).view.topDown
                (block.inserted element).owner
                (block.inserted element).side) := by
        simpa only [State.insert, Block.inserted] using
          rearrangedSegment
      have tailGaps :
          ∀ queried ∈ elements,
            0 ≤
              (state.insert blockId element).view.rawGap queried := by
        intro queried queriedMember
        simpa only [State.insert] using
          elementGaps queried (by simp [queriedMember])
      have tailTrace :=
        ih (state.insert blockId element)
          (block.inserted element) afterValid afterUnique afterFound
          afterGrowing tailSegment tailGaps
      exact headTrace.append tailTrace

theorem exists_insertMany_trace_of_uniquePlacements {n : ℕ}
    {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (elements : List (Element n))
    (valid : state.Valid params)
    (unique : UniquePlacements state)
    (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing)
    (plannedSegment :
      IsSegment (elements.reverse ++ block.elements)
        (state.view.topDown block.owner block.side))
    (elementGaps :
      ∀ element ∈ elements, 0 ≤ state.view.rawGap element) :
    ∃ events : List (Event n),
      Trace params state events
        (insertMany state blockId elements) := by
  exact ⟨insertManyEvents state blockId block elements,
    insertMany_trace_of_uniquePlacements state blockId block elements valid unique found growing plannedSegment elementGaps⟩

/-- Reverse top-down insertion order for one canonical placement. -/
noncomputable def canonicalInsertionSequence {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (placement : Element n × Side) : List (Element n) :=
  ((canonicalHeapView snapshot tree).topDown
    placement.1 placement.2).reverse

/-- Populating an empty canonical placement yields its canonical block. -/
theorem insertedManyBlock_emptyGrowing_canonical {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (placement : Element n × Side) :
    insertedManyBlock
        (Block.emptyGrowing placement.1 placement.2)
        (canonicalInsertionSequence snapshot tree placement) =
      canonicalBlock snapshot tree placement.1 placement.2 := by
  rw [insertedManyBlock_eq]
  simp [canonicalInsertionSequence, Block.emptyGrowing,
    canonicalBlock]

/-- The bulk-created empty canonical block list has unique placements. -/
theorem emptyCanonicalBlocksState_uniquePlacements {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    UniquePlacements (emptyCanonicalBlocksState snapshot tree) := by
  rw [UniquePlacements, emptyCanonicalBlocksState_blocks]
  have functionEq :
      (blockPlacement ∘ fun placement : Element n × Side =>
        Block.emptyGrowing placement.1 placement.2) = id := by
    funext placement
    rcases placement with ⟨owner, side⟩
    rfl
  rw [List.map_map, functionEq, List.map_id]
  exact ownerSidePairs_nodup n

/--
Populate consecutive block identifiers with the canonical blocks described by
the matching placement list.
-/
noncomputable def populateCanonicalPlacements {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    State n → Interface.BlockId →
      List (Element n × Side) → State n
  | state, _, [] => state
  | state, blockId, placement :: placements =>
      populateCanonicalPlacements snapshot tree
        (insertMany state blockId
          (canonicalInsertionSequence snapshot tree placement))
        (blockId + 1) placements

@[simp]
theorem populateCanonicalPlacements_nil {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (state : State n) (blockId : Interface.BlockId) :
    populateCanonicalPlacements snapshot tree state blockId [] =
      state :=
  rfl

@[simp]
theorem populateCanonicalPlacements_cons {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (state : State n) (blockId : Interface.BlockId)
    (placement : Element n × Side)
    (placements : List (Element n × Side)) :
    populateCanonicalPlacements snapshot tree state blockId
        (placement :: placements) =
      populateCanonicalPlacements snapshot tree
        (insertMany state blockId
          (canonicalInsertionSequence snapshot tree placement))
        (blockId + 1) placements :=
  rfl

@[simp]
theorem populateCanonicalPlacements_view {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (state : State n) (blockId : Interface.BlockId)
    (placements : List (Element n × Side)) :
    (populateCanonicalPlacements snapshot tree state blockId
      placements).view = state.view := by
  induction placements generalizing state blockId with
  | nil =>
      rfl
  | cons placement placements ih =>
      rw [populateCanonicalPlacements_cons, ih]
      exact insertMany_view state blockId
        (canonicalInsertionSequence snapshot tree placement)

@[simp]
theorem populateCanonicalPlacements_value {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (state : State n) (blockId : Interface.BlockId)
    (placements : List (Element n × Side)) :
    (populateCanonicalPlacements snapshot tree state blockId
      placements).value = state.value := by
  induction placements generalizing state blockId with
  | nil =>
      rfl
  | cons placement placements ih =>
      rw [populateCanonicalPlacements_cons, ih]
      exact insertMany_value state blockId
        (canonicalInsertionSequence snapshot tree placement)

@[simp]
theorem populateCanonicalPlacements_blocks_length {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (state : State n) (blockId : Interface.BlockId)
    (placements : List (Element n × Side)) :
    (populateCanonicalPlacements snapshot tree state blockId
      placements).blocks.length = state.blocks.length := by
  induction placements generalizing state blockId with
  | nil =>
      rfl
  | cons placement placements ih =>
      rw [populateCanonicalPlacements_cons, ih]
      exact
        insertMany_blocks_length state blockId
          (canonicalInsertionSequence snapshot tree placement)

/-- Population at and above `blockId` leaves every lower identifier intact. -/
theorem populateCanonicalPlacements_found_of_lt {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (state : State n) (blockId : Interface.BlockId)
    (placements : List (Element n × Side))
    (otherId : Interface.BlockId) (lower : otherId < blockId) :
    (populateCanonicalPlacements snapshot tree state blockId
      placements).blocks[otherId]? =
        state.blocks[otherId]? := by
  induction placements generalizing state blockId with
  | nil =>
      rfl
  | cons placement placements ih =>
      rw [populateCanonicalPlacements_cons]
      calc
        (populateCanonicalPlacements snapshot tree
              (insertMany state blockId
                (canonicalInsertionSequence snapshot tree placement))
              (blockId + 1) placements).blocks[otherId]? =
            (insertMany state blockId
              (canonicalInsertionSequence snapshot tree placement)).blocks[
                otherId]? :=
          ih (insertMany state blockId
            (canonicalInsertionSequence snapshot tree placement))
            (blockId + 1)
              (lower.trans (Nat.lt_add_one blockId))
        _ = state.blocks[otherId]? :=
          insertMany_found_of_ne state blockId otherId
            (canonicalInsertionSequence snapshot tree placement)
            (Nat.ne_of_gt lower)

/--
Starting from consecutive empty blocks, canonical population is a real trace
and leaves each processed identifier equal to its canonical block.
-/
/- Exact event list populating the canonical owner-side slots. -/
noncomputable def populateCanonicalPlacementEvents {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) (state : State n) (blockId : Interface.BlockId) :
    List (Element n × Side) → List (Event n)
  | [] => []
  | placement :: placements =>
      insertManyEvents state blockId (Block.emptyGrowing placement.1 placement.2)
        (canonicalInsertionSequence snapshot tree placement) ++
      populateCanonicalPlacementEvents snapshot tree
        (insertMany state blockId (canonicalInsertionSequence snapshot tree placement))
        (blockId + 1) placements

theorem populateCanonicalPlacements_trace {n : ℕ}
    {params : Interface.Parameters}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (state : State n) (blockId : Interface.BlockId)
    (placements : List (Element n × Side))
    (valid : state.Valid params)
    (unique : UniquePlacements state)
    (viewEq :
      state.view = canonicalHeapView snapshot tree)
    (emptyFound :
      ∀ index (indexLt : index < placements.length),
        state.blocks[blockId + index]? =
          some
            (Block.emptyGrowing
              placements[index].1 placements[index].2)) :
    Trace params state (populateCanonicalPlacementEvents snapshot tree state blockId placements)
        (populateCanonicalPlacements snapshot tree state blockId
          placements) ∧
      ∀ index (indexLt : index < placements.length),
        (populateCanonicalPlacements snapshot tree state blockId
          placements).blocks[blockId + index]? =
            some
              (canonicalBlock snapshot tree
                placements[index].1 placements[index].2) := by
  induction placements generalizing state blockId with
  | nil =>
      refine ⟨Trace.nil valid, ?_⟩
      intro index indexLt
      simp at indexLt
  | cons placement placements ih =>
      have headFound :
          state.blocks[blockId]? =
            some
              (Block.emptyGrowing placement.1 placement.2) := by
        have foundZero := emptyFound 0 (by simp)
        have placementZero :
            (placement :: placements)[0] = placement :=
          rfl
        rw [Nat.add_zero, placementZero] at foundZero
        exact foundZero
      have plannedSegment :
          IsSegment
              ((canonicalInsertionSequence snapshot tree
                    placement).reverse ++
                (Block.emptyGrowing
                  placement.1 placement.2).elements)
              (state.view.topDown placement.1 placement.2) := by
        rw [viewEq]
        simp [canonicalInsertionSequence, Block.emptyGrowing]
        exact ⟨[], [], by simp⟩
      have elementGaps :
          ∀ element ∈
              canonicalInsertionSequence snapshot tree placement,
            0 ≤ state.view.rawGap element := by
        intro element member
        have topDownMember :
            element ∈
              (canonicalHeapView snapshot tree).topDown
                placement.1 placement.2 := by
          simpa [canonicalInsertionSequence] using member
        have parent :=
          (canonicalHeapView snapshot tree).mem_topDown_parent
            topDownMember
        rw [viewEq]
        exact
          le_of_lt
            ((canonicalHeapView snapshot tree).rawGap_pos_of_heapOrdered
              (canonicalHeapView_heapOrdered snapshot tree) parent)
      have headTrace :=
        insertMany_trace_of_uniquePlacements
          state blockId
          (Block.emptyGrowing placement.1 placement.2)
          (canonicalInsertionSequence snapshot tree placement)
          valid unique headFound rfl plannedSegment elementGaps
      let after :=
        insertMany state blockId
          (canonicalInsertionSequence snapshot tree placement)
      have afterValid : after.Valid params :=
        headTrace.final_valid
      have afterUnique : UniquePlacements after :=
        unique.insertMany blockId
          (canonicalInsertionSequence snapshot tree placement)
      have afterViewEq :
          after.view = canonicalHeapView snapshot tree := by
        simpa [after] using viewEq
      have tailEmptyFound :
          ∀ index (indexLt : index < placements.length),
            after.blocks[(blockId + 1) + index]? =
              some
                (Block.emptyGrowing
                  placements[index].1 placements[index].2) := by
        intro index indexLt
        have old :=
          emptyFound (index + 1) (by
            simpa only [List.length_cons, Nat.succ_eq_add_one] using
              Nat.succ_lt_succ indexLt)
        have unchanged :=
          insertMany_found_of_ne state blockId
            ((blockId + 1) + index)
            (canonicalInsertionSequence snapshot tree placement)
            (Nat.ne_of_lt
              ((Nat.lt_add_one blockId).trans_le
                (Nat.le_add_right (blockId + 1) index)))
        rw [unchanged]
        simpa [after, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using old
      obtain ⟨tailTrace, tailFound⟩ :=
        ih after (blockId + 1) afterValid afterUnique
          afterViewEq tailEmptyFound
      refine
        ⟨headTrace.append tailTrace, ?_⟩
      intro index indexLt
      cases index with
      | zero =>
          have persisted :=
            populateCanonicalPlacements_found_of_lt
              snapshot tree after (blockId + 1) placements
              blockId (Nat.lt_add_one blockId)
          have populatedHead :
              after.blocks[blockId]? =
                some
                  (canonicalBlock snapshot tree
                    placement.1 placement.2) := by
            have inserted :=
              insertMany_found state blockId
                (Block.emptyGrowing placement.1 placement.2)
                (canonicalInsertionSequence snapshot tree placement)
                headFound
            simpa [after,
              insertedManyBlock_emptyGrowing_canonical] using inserted
          simpa using persisted.trans populatedHead
      | succ index =>
          have tailLt : index < placements.length := by
            exact Nat.lt_of_succ_lt_succ (by
              simpa only [List.length_cons,
                Nat.succ_eq_add_one] using indexLt)
          have foundTail :=
            tailFound index tailLt
          simpa [Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using foundTail

theorem exists_populateCanonicalPlacements_trace {n : ℕ}
    {params : Interface.Parameters}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (state : State n) (blockId : Interface.BlockId)
    (placements : List (Element n × Side))
    (valid : state.Valid params)
    (unique : UniquePlacements state)
    (viewEq :
      state.view = canonicalHeapView snapshot tree)
    (emptyFound :
      ∀ index (indexLt : index < placements.length),
        state.blocks[blockId + index]? =
          some
            (Block.emptyGrowing
              placements[index].1 placements[index].2)) :
    ∃ events : List (Event n),
      Trace params state events
        (populateCanonicalPlacements snapshot tree state blockId
          placements) ∧
      ∀ index (indexLt : index < placements.length),
        (populateCanonicalPlacements snapshot tree state blockId
          placements).blocks[blockId + index]? =
            some
              (canonicalBlock snapshot tree
                placements[index].1 placements[index].2) := by
  exact ⟨populateCanonicalPlacementEvents snapshot tree state blockId placements,
    populateCanonicalPlacements_trace snapshot tree state blockId placements valid unique viewEq emptyFound⟩

private theorem State.eq_of_view_blocks_value {n : ℕ}
    {first second : State n}
    (viewEq : first.view = second.view)
    (blocksEq : first.blocks = second.blocks)
    (valueEq : first.value = second.value) :
    first = second := by
  cases first
  cases second
  simp_all

/--
Creating every empty canonical block and then populating each one in reverse
top-down order reaches the literal canonical rich state.
-/
/- All actual initialization operations, starting with empty interface storage. -/
noncomputable def canonicalInitializationEvents {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) : List (Event n) :=
  createPlacementEvents (ownerSidePairs n) ++ populateCanonicalPlacementEvents snapshot tree
    (emptyCanonicalBlocksState snapshot tree) 0 (ownerSidePairs n)

theorem emptyCanonicalState_canonicalState_trace {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    Trace params (emptyCanonicalState snapshot tree) (canonicalInitializationEvents snapshot tree)
        (canonicalState snapshot tree) := by
  have creationTrace :=
    emptyCanonicalBlocksState_trace snapshot tree params
      growingLimit valueBound
  have createdValid :
      (emptyCanonicalBlocksState snapshot tree).Valid params :=
    creationTrace.final_valid
  have emptyFound :
      ∀ index (indexLt : index < (ownerSidePairs n).length),
        (emptyCanonicalBlocksState snapshot tree).blocks[0 + index]? =
          some
            (Block.emptyGrowing
              (ownerSidePairs n)[index].1
              (ownerSidePairs n)[index].2) := by
    intro index indexLt
    rw [emptyCanonicalBlocksState_blocks, Nat.zero_add,
      List.getElem?_map]
    rw [List.getElem?_eq_getElem indexLt]
    rfl
  obtain ⟨populationTrace, populatedFound⟩ :=
    populateCanonicalPlacements_trace snapshot tree
      (emptyCanonicalBlocksState snapshot tree) 0
      (ownerSidePairs n) createdValid
      (emptyCanonicalBlocksState_uniquePlacements snapshot tree)
      (emptyCanonicalBlocksState_view snapshot tree) emptyFound
  let populated :=
    populateCanonicalPlacements snapshot tree
      (emptyCanonicalBlocksState snapshot tree) 0
      (ownerSidePairs n)
  have populatedLength :
      populated.blocks.length = (ownerSidePairs n).length := by
    calc
      populated.blocks.length =
          (emptyCanonicalBlocksState snapshot tree).blocks.length := by
        simp [populated]
      _ = (ownerSidePairs n).length := by
        simp
  have canonicalLength :
      (canonicalBlocks snapshot tree).length =
        (ownerSidePairs n).length := by
    simp [canonicalBlocks]
  have populatedBlocks :
      populated.blocks = canonicalBlocks snapshot tree := by
    apply List.ext_getElem
    · exact populatedLength.trans canonicalLength.symm
    · intro index populatedLt canonicalLt
      have indexLt : index < (ownerSidePairs n).length := by
        simpa only [populatedLength] using populatedLt
      have found :=
        populatedFound index indexLt
      have foundAtIndex :
          populated.blocks[index]? =
            some
              (canonicalBlock snapshot tree
                (ownerSidePairs n)[index].1
                (ownerSidePairs n)[index].2) := by
        simpa only [Nat.zero_add, populated] using found
      obtain ⟨_, populatedGet⟩ :=
        List.getElem?_eq_some_iff.mp foundAtIndex
      calc
        populated.blocks[index] =
            canonicalBlock snapshot tree
              (ownerSidePairs n)[index].1
              (ownerSidePairs n)[index].2 :=
          populatedGet
        _ = (canonicalBlocks snapshot tree)[index] := by
          simp [canonicalBlocks]
  have populatedEq :
      populated = canonicalState snapshot tree := by
    apply State.eq_of_view_blocks_value
    · simp [populated]
    · simpa only [canonicalState_blocks] using populatedBlocks
    · simp [populated]
  have completeTrace :=
    creationTrace.append populationTrace
  simpa only [canonicalInitializationEvents, populated, populatedEq] using completeTrace

theorem exists_emptyCanonicalState_canonicalState_trace {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    ∃ events : List (Event n),
      Trace params (emptyCanonicalState snapshot tree) events
        (canonicalState snapshot tree) := by
  exact ⟨canonicalInitializationEvents snapshot tree,
    emptyCanonicalState_canonicalState_trace snapshot tree params growingLimit valueBound⟩

/--
Concrete initialization certificate obtained solely from primitive create,
value-change, and insert steps.
-/
noncomputable def canonicalInitialization {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    Initialization params snapshot tree := by
  let traceWitness :=
    exists_emptyCanonicalState_canonicalState_trace
      snapshot tree params growingLimit valueBound
  exact
    { valueBound := valueBound
      final := canonicalState snapshot tree
      events := Classical.choose traceWitness
      trace := Classical.choose_spec traceWitness
      final_represents :=
        canonicalState_represents snapshot tree params
          growingLimit valueBound }

end Splay.Lazy.Canonical
