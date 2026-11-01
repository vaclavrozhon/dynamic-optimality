import Splay.Lazy.ComparisonRootSwapComplete

namespace Splay.Lazy

namespace Canonical

open Splay.Rank

/-- The finite list of every interface element. -/
def allInterfaceElements (n : ℕ) : List (Element n) :=
  List.finRange (2 * n + 1)

@[simp]
theorem mem_allInterfaceElements {n : ℕ} (element : Element n) :
    element ∈ allInterfaceElements n := by
  simp [allInterfaceElements]

/--
First lower every initial value to one.  This changes no heap or block
structure and emits no increasing value operation.
-/
noncomputable def oneValueEmptyState {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) : State n :=
  (emptyCanonicalState snapshot tree).adjustValuesToOne
    (allInterfaceElements n)

/-- Add the canonical two empty growing placements for every possible owner. -/
noncomputable def oneValueEmptyBlocksState {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) : State n :=
  createPlacements (oneValueEmptyState snapshot tree)
    (ownerSidePairs n)

@[simp]
theorem oneValueEmptyState_view {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (oneValueEmptyState snapshot tree).view =
      canonicalHeapView snapshot tree := by
  simp [oneValueEmptyState]

@[simp]
theorem oneValueEmptyState_blocks {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (oneValueEmptyState snapshot tree).blocks = [] := by
  simp [oneValueEmptyState]

@[simp]
theorem oneValueEmptyState_value {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (element : Element n) :
    (oneValueEmptyState snapshot tree).value element = 1 := by
  apply State.adjustValuesToOne_value_eq_one_of_mem
  exact mem_allInterfaceElements element

@[simp]
theorem oneValueEmptyBlocksState_view {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (oneValueEmptyBlocksState snapshot tree).view =
      canonicalHeapView snapshot tree := by
  simp [oneValueEmptyBlocksState]

@[simp]
theorem oneValueEmptyBlocksState_blocks {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (oneValueEmptyBlocksState snapshot tree).blocks =
      (ownerSidePairs n).map fun placement =>
        Block.emptyGrowing placement.1 placement.2 := by
  simp [oneValueEmptyBlocksState]

@[simp]
theorem oneValueEmptyBlocksState_value {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (element : Element n) :
    (oneValueEmptyBlocksState snapshot tree).value element = 1 := by
  simp [oneValueEmptyBlocksState]

/-- Value lowering followed by creation of all empty placements is legal. -/
theorem oneValueEmptyBlocksState_trace {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    Trace params (emptyCanonicalState snapshot tree)
      ((emptyCanonicalState snapshot tree).adjustValuesToOneEvents
          (allInterfaceElements n) ++
        createPlacementEvents (ownerSidePairs n))
      (oneValueEmptyBlocksState snapshot tree) := by
  have initialValid :=
    emptyCanonicalState_valid snapshot tree params valueBound
  have valueTrace :
      Trace params (emptyCanonicalState snapshot tree)
        ((emptyCanonicalState snapshot tree).adjustValuesToOneEvents
          (allInterfaceElements n))
        (oneValueEmptyState snapshot tree) := by
    exact
      (emptyCanonicalState snapshot tree).adjustValuesToOne_trace
        (allInterfaceElements n) initialValid
  have creationTrace :
      Trace params (oneValueEmptyState snapshot tree)
        (createPlacementEvents (ownerSidePairs n))
        (oneValueEmptyBlocksState snapshot tree) := by
    apply createPlacements_trace
      (oneValueEmptyState snapshot tree) (ownerSidePairs n)
      valueTrace.final_valid
    intro owner
    have pairCount :
        placementCount (ownerSidePairs n) owner = 2 :=
      ownerSidePairs_filter_owner_length owner
    simp [oneValueEmptyState, State.toInterface,
      Interface.State.growingCount, pairCount]
    exact growingLimit
  exact valueTrace.append creationTrace

/-- The prepared empty-placement state is already shift-atomic. -/
theorem oneValueEmptyBlocksState_shiftAtomic {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (oneValueEmptyBlocksState snapshot tree).ShiftAtomic := by
  intro block member
  rw [oneValueEmptyBlocksState_blocks] at member
  obtain ⟨placement, _, rfl⟩ := List.mem_map.mp member
  exact Or.inl ⟨rfl, rfl⟩

/-- There is exactly one empty growing block at every owner-side placement. -/
theorem oneValueEmptyBlocksState_oneGrowingPerSide {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (oneValueEmptyBlocksState snapshot tree).OneGrowingPerSide := by
  classical
  rw [State.OneGrowingPerSide, oneValueEmptyBlocksState_blocks]
  intro owner side
  let placements := ownerSidePairs n
  let makeBlock :=
    fun placement : Element n × Side =>
      Block.emptyGrowing placement.1 placement.2
  obtain ⟨rawId, rawGet⟩ :=
    List.mem_iff_get.mp
      (mem_ownerSidePairs (n := n) (owner, side))
  let id : Fin (placements.map makeBlock).length :=
    ⟨rawId.val, by
      simpa [placements] using rawId.isLt⟩
  refine ⟨id, ?_, ?_⟩
  · change
      ((placements.map makeBlock).get id).mode = .growing ∧
        ((placements.map makeBlock).get id).owner = owner ∧
        ((placements.map makeBlock).get id).side = side
    have selected :
        placements.get
            ⟨id.val, by
              simpa [placements, makeBlock] using id.isLt⟩ =
          (owner, side) := by
      simpa [placements, id] using rawGet
    have mappedSelected :
        (placements.map makeBlock).get id =
          Block.emptyGrowing owner side := by
      rw [List.get_eq_getElem, List.getElem_map]
      have selectedElem :
          placements[id.val] = (owner, side) := by
        simpa [List.get_eq_getElem] using selected
      rw [selectedElem]
    rw [mappedSelected]
    exact ⟨rfl, rfl, rfl⟩
  · intro other otherProperty
    dsimp only at otherProperty
    let otherRaw : Fin placements.length :=
      ⟨other.val, by
        simpa [placements, makeBlock] using other.isLt⟩
    have otherSelected :
        placements.get otherRaw = (owner, side) := by
      apply Prod.ext
      · simpa [placements, makeBlock, otherRaw, Block.emptyGrowing] using
          otherProperty.2.1
      · simpa [placements, makeBlock, otherRaw, Block.emptyGrowing] using
          otherProperty.2.2
    have rawEq : otherRaw = rawId := by
      apply (ownerSidePairs_nodup n).get_inj_iff.mp
      exact otherSelected.trans rawGet.symm
    apply Fin.ext
    have valEq : otherRaw.val = rawId.val :=
      congrArg (fun index : Fin placements.length => index.val) rawEq
    exact valEq

end Canonical

namespace State

/--
Result of populating a shift-atomic state with a finite list of previously
unassigned non-root elements.  One shrinking singleton is installed for each
element and the unique empty growing block at its parent-side is replaced.
-/
structure AtomicPopulation
    {n : ℕ} (params : Interface.Parameters)
    (initial : State n) (elements : List (Element n)) where
  final : State n
  events : List (Event n)
  trace : Trace params initial events final
  shiftAtomic : final.ShiftAtomic
  oneGrowingPerSide : final.OneGrowingPerSide
  view_eq : final.view = initial.view
  value_eq : final.value = initial.value
  assigned_iff :
    ∀ element,
      element ∈ final.allElements ↔
        element ∈ elements ∨ element ∈ initial.allElements
  totalInserts_eq :
    Interface.totalInserts (eraseOperations events) = elements.length
  totalIncreases_eq :
    Interface.totalIncreases (eraseOperations events) = elements.length

namespace AtomicPopulation

/--
Populate every requested non-root endpoint by the exact five-event atomic
macro

`increase; insert; decrease; convert; create`.

The theorem is deliberately independent of canonical trees.  It only needs a
heap-ordered shift-atomic view, one empty growing block per owner-side, value
one everywhere, and a duplicate-free list disjoint from the initially
assigned elements.
-/
theorem exists_population
    {n : ℕ} {params : Interface.Parameters}
    {initial : State n} {elements : List (Element n)}
    (valid : initial.Valid params)
    (atomic : initial.ShiftAtomic)
    (oneGrowing : initial.OneGrowingPerSide)
    (heapOrdered : initial.view.HeapOrdered)
    (valuesOne : ∀ element, initial.value element = 1)
    (nodup : elements.Nodup)
    (unassigned :
      ∀ element ∈ elements, element ∉ initial.allElements)
    (nonroot :
      ∀ element ∈ elements, initial.view.parent element ≠ none) :
    Nonempty (AtomicPopulation params initial elements) := by
  induction elements generalizing initial with
  | nil =>
      exact
        ⟨{
          final := initial
          events := []
          trace := Trace.nil valid
          shiftAtomic := atomic
          oneGrowingPerSide := oneGrowing
          view_eq := rfl
          value_eq := rfl
          assigned_iff := by simp
          totalInserts_eq := by
            simp [eraseOperations, Interface.totalInserts]
          totalIncreases_eq := by
            simp [eraseOperations, Interface.totalIncreases]
        }⟩
  | cons element elements ih =>
      have elementNotTail : element ∉ elements :=
        (List.nodup_cons.mp nodup).1
      have tailNodup : elements.Nodup :=
        (List.nodup_cons.mp nodup).2
      have elementUnassigned : element ∉ initial.allElements :=
        unassigned element (by simp)
      obtain ⟨owner, parent⟩ :=
        Option.ne_none_iff_exists.mp
          (nonroot element (by simp))
      obtain ⟨growingId, growingProperty, _growingUnique⟩ :=
        oneGrowing owner (initial.view.side element)
      let growingBlock := initial.blocks.get growingId
      have growingMode : growingBlock.mode = .growing :=
        growingProperty.1
      have growingOwner : growingBlock.owner = owner :=
        growingProperty.2.1
      have growingSide :
          growingBlock.side = initial.view.side element :=
        growingProperty.2.2
      have growingFound :
          initial.blocks[growingId.val]? = some growingBlock := by
        apply List.getElem?_eq_some_iff.mpr
        exact
          ⟨growingId.isLt, by
            simp [growingBlock, List.get_eq_getElem]⟩
      have growingMember : growingBlock ∈ initial.blocks :=
        List.get_mem initial.blocks growingId
      have growingEmpty : growingBlock.elements = [] := by
        rcases atomic growingBlock growingMember with
            growingCase | shrinkingCase
        · exact growingCase.2
        · rw [growingMode] at shrinkingCase
          simp at shrinkingCase
      have elementGap : 0 ≤ initial.view.rawGap element := by
        exact le_of_lt
          (initial.view.rawGap_pos_of_heapOrdered
            heapOrdered parent.symm)
      have parentAtBlock :
          initial.view.parent element = some growingBlock.owner := by
        simpa [growingOwner] using parent.symm
      have sideAtBlock :
          initial.view.side element = growingBlock.side :=
        growingSide.symm
      have creatorOne :
          initial.value growingBlock.creator = 1 :=
        valuesOne growingBlock.creator
      have elementOne :
          initial.value element = 1 :=
        valuesOne element
      let inserted := initial.insert growingId.val element
      have insertTrace :
          Trace params initial
            [.operation (.valueChange element .increase),
              .operation (.insert growingId.val element),
              .operation (.valueChange element .decrease)]
            inserted := by
        exact
          atomic.oneIncreaseInsertDecrease_trace_of_emptyGrowing
            valid growingId.val growingBlock element
            growingFound growingMode growingEmpty elementUnassigned
            parentAtBlock sideAtBlock elementGap creatorOne elementOne
      have insertedValid : inserted.Valid params :=
        insertTrace.final_valid
      let insertedBlock := growingBlock.inserted element
      have insertedFound :
          inserted.blocks[growingId.val]? = some insertedBlock := by
        apply List.getElem?_eq_some_iff.mpr
        refine ⟨by simp [inserted, State.insert], ?_⟩
        change
          (initial.blocks.modify growingId.val
            (fun current => current.inserted element))[growingId.val] =
              insertedBlock
        rw [List.getElem_modify, if_pos rfl]
        have selectedEq :
            initial.blocks[growingId.val] = growingBlock := by
          simp [growingBlock, List.get_eq_getElem]
        rw [selectedEq]
      have insertedGrowing : insertedBlock.mode = .growing := by
        simp [insertedBlock, Block.inserted, growingMode]
      have insertedGapValid :
          (insertedBlock.converted
            (initial.view.rawGap element)).GapValid inserted.view := by
        simp [Block.GapValid, Block.converted, insertedBlock,
          Block.inserted, growingEmpty, inserted, State.insert]
        change
          Analysis.IsIntervalGap {element} initial.view.rawGap
            (initial.view.rawGap element)
        simp [Analysis.IsIntervalGap]
      let next :=
        (inserted.convert growingId.val
          (initial.view.rawGap element)).create
            insertedBlock.creator insertedBlock.side
      have structuralTrace :
          Trace params inserted
            [.operation (.convert growingId.val),
              .operation (.create insertedBlock.creator)]
            next := by
        exact inserted.convertAndCreate_trace
          growingId.val insertedBlock
          (initial.view.rawGap element)
          insertedValid insertedFound insertedGrowing insertedGapValid
      have nextValid : next.Valid params :=
        structuralTrace.final_valid
      have nextAtomic : next.ShiftAtomic := by
        simpa [next, inserted, insertedBlock, Block.inserted] using
          atomic.insertConvertCreate
            growingId.val growingBlock element
            (initial.view.rawGap element) growingFound
            growingMode growingEmpty
      have insertedOneGrowing : inserted.OneGrowingPerSide :=
        oneGrowing.insert growingId.val element
      have nextOneGrowing : next.OneGrowingPerSide := by
        exact insertedOneGrowing.convertAndCreate insertedValid
          growingId.val insertedBlock
          (initial.view.rawGap element)
          insertedFound insertedGrowing
      have nextView : next.view = initial.view := rfl
      have nextValue : next.value = initial.value := rfl
      have nextValuesOne :
          ∀ queried, next.value queried = 1 := by
        intro queried
        rw [nextValue]
        exact valuesOne queried
      have nextHeapOrdered : next.view.HeapOrdered := by
        rw [nextView]
        exact heapOrdered
      have nextAssigned :
          ∀ queried,
            queried ∈ next.allElements ↔
              queried = element ∨ queried ∈ initial.allElements := by
        intro queried
        simp only [next, State.create_allElements,
          State.convert_allElements]
        exact
          Canonical.mem_insert_allElements_iff
            initial growingId.val growingBlock element queried
              growingFound
      have tailUnassigned :
          ∀ queried ∈ elements, queried ∉ next.allElements := by
        intro queried queriedMember nextMember
        have cases := (nextAssigned queried).mp nextMember
        rcases cases with queriedEq | oldMember
        · subst queried
          exact elementNotTail queriedMember
        · exact
            unassigned queried (by simp [queriedMember]) oldMember
      have tailNonroot :
          ∀ queried ∈ elements, next.view.parent queried ≠ none := by
        intro queried queriedMember
        rw [nextView]
        exact nonroot queried (by simp [queriedMember])
      obtain ⟨tail⟩ :=
        ih nextValid nextAtomic nextOneGrowing
          nextHeapOrdered nextValuesOne tailNodup
          tailUnassigned tailNonroot
      let headEvents : List (Event n) :=
        [.operation (.valueChange element .increase),
          .operation (.insert growingId.val element),
          .operation (.valueChange element .decrease),
          .operation (.convert growingId.val),
          .operation (.create insertedBlock.creator)]
      have headTrace :
          Trace params initial headEvents next := by
        exact insertTrace.append structuralTrace
      refine
        ⟨{
          final := tail.final
          events := headEvents ++ tail.events
          trace := headTrace.append tail.trace
          shiftAtomic := tail.shiftAtomic
          oneGrowingPerSide := tail.oneGrowingPerSide
          view_eq := tail.view_eq.trans nextView
          value_eq := tail.value_eq.trans nextValue
          assigned_iff := ?_
          totalInserts_eq := ?_
          totalIncreases_eq := ?_
        }⟩
      intro queried
      rw [tail.assigned_iff, nextAssigned]
      simp only [List.mem_cons]
      constructor <;> tauto
      · simp only [headEvents, eraseOperations, Event.operations,
          List.flatMap_append, List.map_append, List.sum_append,
          Interface.totalInserts, Interface.Operation.insertCount,
          List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
          List.length_cons]
        change
          1 + Interface.totalInserts
                (eraseOperations tail.events) =
            elements.length + 1
        rw [tail.totalInserts_eq]
        omega
      · simp only [headEvents, eraseOperations, Event.operations,
          List.flatMap_append, List.map_append, List.sum_append,
          Interface.totalIncreases, Interface.Operation.increaseCount,
          List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
          List.length_cons]
        change
          1 + Interface.totalIncreases
                (eraseOperations tail.events) =
            elements.length + 1
        rw [tail.totalIncreases_eq]
        omega

end AtomicPopulation

end State

namespace Canonical

open Splay.Rank

@[simp]
theorem oneValueEmptyBlocksState_allElements {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (oneValueEmptyBlocksState snapshot tree).allElements = [] := by
  rw [State.allElements, oneValueEmptyBlocksState_blocks,
    List.flatMap_map]
  simp [Block.emptyGrowing]

/--
The canonical non-root heap endpoints can all be populated by the atomic
five-event macro.
-/
theorem atomicPopulation_nonempty {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    Nonempty
      (State.AtomicPopulation params
        (oneValueEmptyBlocksState snapshot tree)
        (canonicalAllElements snapshot tree)) := by
  have preparation :=
    oneValueEmptyBlocksState_trace snapshot tree params
      growingLimit valueBound
  have heapOrdered :
      (oneValueEmptyBlocksState snapshot tree).view.HeapOrdered := by
    rw [oneValueEmptyBlocksState_view]
    exact canonicalHeapView_heapOrdered snapshot tree
  apply State.AtomicPopulation.exists_population
    preparation.final_valid
    (oneValueEmptyBlocksState_shiftAtomic snapshot tree)
    (oneValueEmptyBlocksState_oneGrowingPerSide snapshot tree)
    heapOrdered
    (oneValueEmptyBlocksState_value snapshot tree)
    (canonicalAllElements_nodup snapshot tree)
  · intro element _member
    simp
  · intro element member
    rw [oneValueEmptyBlocksState_view]
    exact
      (mem_canonicalAllElements_iff_parent_ne_none
        snapshot tree element).mp member

/-- Canonical choice of the atomic population trace. -/
noncomputable def atomicPopulation {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    State.AtomicPopulation params
      (oneValueEmptyBlocksState snapshot tree)
      (canonicalAllElements snapshot tree) :=
  Classical.choice
    (atomicPopulation_nonempty snapshot tree params
      growingLimit valueBound)

namespace AtomicPopulation

variable {n : ℕ} {snapshot : Snapshot n} {tree : Tree.BST 0 n}
  {params : Interface.Parameters}
  {growingLimit : 2 ≤ params.growingLimit}
  {valueBound :
    Analysis.contractedGap snapshot.maxRank ≤ params.valueBound}

/-- The atomic population covers exactly every non-root heap endpoint. -/
theorem complete
    (population :=
      atomicPopulation snapshot tree params
        growingLimit valueBound) :
    population.final.Complete := by
  intro element
  rw [population.assigned_iff]
  rw [population.view_eq]
  simp only [oneValueEmptyBlocksState_allElements,
    List.not_mem_nil, or_false]
  rw [oneValueEmptyBlocksState_view]
  exact
    mem_canonicalAllElements_iff_parent_ne_none
      snapshot tree element

/-- Every remaining growing block is empty and hence trivially topmost. -/
theorem growingTopmost
    (population :=
      atomicPopulation snapshot tree params
        growingLimit valueBound) :
    population.final.GrowingTopmost := by
  intro id
  dsimp only
  intro growing
  have member :
      population.final.blocks.get id ∈ population.final.blocks :=
    List.get_mem _ id
  rcases population.shiftAtomic
      (population.final.blocks.get id) member with
      growingCase | shrinkingCase
  · refine
      ⟨population.final.view.topDown
          (population.final.blocks.get id).owner
          (population.final.blocks.get id).side,
        ?_⟩
    rw [growingCase.2]
    simp
  · rw [growing] at shrinkingCase
    simp at shrinkingCase

/-- Atomic singleton gaps and value one realize every final point gap. -/
theorem valuesRealizeGaps
    (population :=
      atomicPopulation snapshot tree params
        growingLimit valueBound) :
    population.final.ValuesRealizeGaps := by
  have finalValuesOne :
      ∀ element, population.final.value element = 1 := by
    intro element
    rw [population.value_eq]
    exact oneValueEmptyBlocksState_value snapshot tree element
  exact
    State.valuesRealizeGaps_of_shiftAtomic_of_values_eq_one
      population.shiftAtomic population.trace.final_valid
      (finalValuesOne population.final.view.root)
      (fun element _member => finalValuesOne element)

/-- The endpoint is a stable representation of the original heap view. -/
theorem stable
    (population :=
      atomicPopulation snapshot tree params
        growingLimit valueBound) :
    population.final.Stable params := by
  refine
    ⟨population.trace.final_valid,
      AtomicPopulation.complete
        (growingLimit := growingLimit) (valueBound := valueBound)
        (population := population),
      ?_,
      population.oneGrowingPerSide,
      AtomicPopulation.growingTopmost
        (growingLimit := growingLimit) (valueBound := valueBound)
        (population := population),
      AtomicPopulation.valuesRealizeGaps
        (growingLimit := growingLimit) (valueBound := valueBound)
        (population := population)⟩
  rw [population.view_eq, oneValueEmptyBlocksState_view]
  exact canonicalHeapView_heapOrdered snapshot tree

/-- Final represented-state form used by `Initialization`. -/
theorem represents
    (population :=
      atomicPopulation snapshot tree params
        growingLimit valueBound) :
    population.final.Represents params snapshot tree := by
  refine
    ⟨AtomicPopulation.stable
      (growingLimit := growingLimit) (valueBound := valueBound)
      (population := population), ?_⟩
  exact
    population.view_eq.trans
      (oneValueEmptyBlocksState_view snapshot tree)

end AtomicPopulation

/--
Productive-efficient initialization.

The prefix first lowers all preloaded values to one, creates the two empty
growing placements per owner, and then installs every non-root endpoint as a
shrinking singleton.  It reaches a dynamic stable representative directly;
there is no need to build the expensive all-growing canonical payload first.
-/
noncomputable def atomicInitialization {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    Initialization params snapshot tree := by
  let population :=
    atomicPopulation snapshot tree params growingLimit valueBound
  let preparationEvents :=
    (emptyCanonicalState snapshot tree).adjustValuesToOneEvents
        (allInterfaceElements n) ++
      createPlacementEvents (ownerSidePairs n)
  let preparationTrace :=
    oneValueEmptyBlocksState_trace snapshot tree params
      growingLimit valueBound
  exact
    { valueBound := valueBound
      final := population.final
      events := preparationEvents ++ population.events
      trace := preparationTrace.append population.trace
      final_represents :=
        AtomicPopulation.represents
          (growingLimit := growingLimit) (valueBound := valueBound)
          (population := population) }

end Canonical

end Splay.Lazy
