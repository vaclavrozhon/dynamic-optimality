import Splay.Lazy.ComparisonRotationPreparation
import Splay.Lazy.ComparisonRootSwap
import Splay.Lazy.ValueTrace
import Mathlib.Data.Finset.Max

namespace Splay.Lazy

private theorem totalInserts_append
    {n : ℕ} (first second : List (Interface.Operation n)) :
    Interface.totalInserts (first ++ second) =
      Interface.totalInserts first + Interface.totalInserts second := by
  simp [Interface.totalInserts]

private theorem totalIncreases_append
    {n : ℕ} (first second : List (Interface.Operation n)) :
    Interface.totalIncreases (first ++ second) =
      Interface.totalIncreases first + Interface.totalIncreases second := by
  simp [Interface.totalIncreases]

namespace State

/--
Adjust the values of a finite list of elements to one, from left to right.

The block structure and heap view are definitionally untouched.  Keeping the
state recursion explicit makes the accompanying event list compositional:
each suffix is computed from the endpoint of the preceding value trace.
-/
def adjustValuesToOne {n : ℕ} :
    State n → List (Element n) → State n
  | state, [] => state
  | state, element :: elements =>
      adjustValuesToOne (state.adjustValue element 1) elements

/-- Visible unit value-change events emitted by `adjustValuesToOne`. -/
def adjustValuesToOneEvents {n : ℕ} :
    State n → List (Element n) → List (Event n)
  | _state, [] => []
  | state, element :: elements =>
      state.adjustValueEvents element 1 ++
        adjustValuesToOneEvents
          (state.adjustValue element 1) elements

@[simp]
theorem adjustValuesToOne_nil {n : ℕ} (state : State n) :
    state.adjustValuesToOne [] = state :=
  rfl

@[simp]
theorem adjustValuesToOne_cons {n : ℕ} (state : State n)
    (element : Element n) (elements : List (Element n)) :
    state.adjustValuesToOne (element :: elements) =
      (state.adjustValue element 1).adjustValuesToOne elements :=
  rfl

@[simp]
theorem adjustValuesToOneEvents_nil {n : ℕ} (state : State n) :
    state.adjustValuesToOneEvents [] = [] :=
  rfl

@[simp]
theorem adjustValuesToOneEvents_cons {n : ℕ} (state : State n)
    (element : Element n) (elements : List (Element n)) :
    state.adjustValuesToOneEvents (element :: elements) =
      state.adjustValueEvents element 1 ++
        (state.adjustValue element 1).adjustValuesToOneEvents elements :=
  rfl

/-- Bulk normalization never inserts an element. -/
theorem totalInserts_adjustValuesToOneEvents_eq_zero
    {n : ℕ} (state : State n) (elements : List (Element n)) :
    Interface.totalInserts
        (eraseOperations (state.adjustValuesToOneEvents elements)) = 0 := by
  induction elements generalizing state with
  | nil =>
      rfl
  | cons element elements ih =>
      rw [adjustValuesToOneEvents_cons, eraseOperations_append,
        totalInserts_append]
      rw [totalInserts_adjustValueEvents, ih, zero_add]

/--
Lowering a valid state's values to one never emits an increasing value
operation.
-/
theorem totalIncreases_adjustValuesToOneEvents_eq_zero
    {n : ℕ} {params : Interface.Parameters}
    (state : State n) (elements : List (Element n))
    (valid : state.Valid params) :
    Interface.totalIncreases
        (eraseOperations (state.adjustValuesToOneEvents elements)) = 0 := by
  induction elements generalizing state with
  | nil =>
      rfl
  | cons element elements ih =>
      have one_le : 1 ≤ state.value element :=
        (valid.toInterface.2.1 element).1
      have headTrace :=
        state.adjustValue_trace element 1 valid (by omega)
          (le_trans (by omega) params.valueBound_ge_two)
      rw [adjustValuesToOneEvents_cons, eraseOperations_append,
        totalIncreases_append]
      have headZero :
          Interface.totalIncreases
              (eraseOperations (state.adjustValueEvents element 1)) = 0 := by
        rw [eraseOperations_adjustValueEvents, if_pos one_le]
        simp [Interface.totalIncreases,
          Interface.Operation.increaseCount]
      rw [headZero, zero_add]
      exact ih (state.adjustValue element 1) headTrace.final_valid

/-- Bulk normalization is a genuine rich trace of unit value changes. -/
theorem adjustValuesToOne_trace {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (elements : List (Element n)) (valid : state.Valid params) :
    Trace params state (state.adjustValuesToOneEvents elements)
      (state.adjustValuesToOne elements) := by
  induction elements generalizing state with
  | nil =>
      exact Trace.nil valid
  | cons element elements ih =>
      have headTrace :
          Trace params state (state.adjustValueEvents element 1)
            (state.adjustValue element 1) :=
        state.adjustValue_trace element 1 valid (by omega)
          (by
            exact le_trans (by omega) params.valueBound_ge_two)
      exact headTrace.append
        (ih (state.adjustValue element 1) headTrace.final_valid)

@[simp]
theorem adjustValuesToOne_blocks {n : ℕ} (state : State n)
    (elements : List (Element n)) :
    (state.adjustValuesToOne elements).blocks = state.blocks := by
  induction elements generalizing state with
  | nil =>
      rfl
  | cons element elements ih =>
      rw [adjustValuesToOne_cons, ih, adjustValue_blocks]

@[simp]
theorem adjustValuesToOne_view {n : ℕ} (state : State n)
    (elements : List (Element n)) :
    (state.adjustValuesToOne elements).view = state.view := by
  induction elements generalizing state with
  | nil =>
      rfl
  | cons element elements ih =>
      rw [adjustValuesToOne_cons, ih, adjustValue_view]

theorem adjustValuesToOne_value_of_not_mem {n : ℕ} (state : State n)
    (elements : List (Element n)) {queried : Element n}
    (notMember : queried ∉ elements) :
    (state.adjustValuesToOne elements).value queried =
      state.value queried := by
  induction elements generalizing state with
  | nil =>
      rfl
  | cons element elements ih =>
      simp only [List.mem_cons, not_or] at notMember
      rw [adjustValuesToOne_cons, ih _ notMember.2]
      exact adjustValue_value_of_ne state notMember.1 1

theorem adjustValuesToOne_value_eq_one_of_mem {n : ℕ}
    (state : State n) (elements : List (Element n))
    {queried : Element n} (member : queried ∈ elements) :
    (state.adjustValuesToOne elements).value queried = 1 := by
  induction elements generalizing state with
  | nil =>
      simp at member
  | cons element elements ih =>
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · subst queried
        by_cases later : element ∈ elements
        · exact ih (state.adjustValue element 1) later
        · rw [adjustValuesToOne_cons,
            adjustValuesToOne_value_of_not_mem _ _ later]
          exact adjustValue_value_self state element 1 (by omega)
      · exact ih (state.adjustValue element 1) member

@[simp]
theorem adjustValuesToOne_allElements {n : ℕ} (state : State n)
    (elements : List (Element n)) :
    (state.adjustValuesToOne elements).allElements =
      state.allElements := by
  simp [State.allElements]

/--
In a valid shift-atomic state, value one on every assigned element is exactly
the non-root part of `ValuesRealizeGaps`.

Every assigned growing case is impossible because growing blocks are empty.
Every assigned shrinking block is a singleton; its gap-validity forces the
stored interval gap to equal the sole raw gap, whose contracted point gap is
one.
-/
theorem valuesRealizeGaps_of_shiftAtomic_of_values_eq_one {n : ℕ}
    {state : State n} {params : Interface.Parameters}
    (atomic : state.ShiftAtomic)
    (valid : state.Valid params)
    (rootValue : state.value state.view.root = 1)
    (assignedValue :
      ∀ element ∈ state.allElements, state.value element = 1) :
    state.ValuesRealizeGaps := by
  constructor
  · exact rootValue
  · intro block blockMember element elementMember
    have elementAssigned : element ∈ state.allElements :=
      State.mem_allElements_iff.mpr
        ⟨block, blockMember, elementMember⟩
    rcases atomic block blockMember with growing | shrinking
    · rw [growing.2] at elementMember
      simp at elementMember
    · rcases shrinking.2 with empty | ⟨singleton, elementsEq⟩
      · rw [empty] at elementMember
        simp at elementMember
      · have elementEq : element = singleton := by
          simpa [elementsEq] using elementMember
        subst singleton
        have gapValid := (valid.2 block blockMember).2.2
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
        rw [assignedValue element elementAssigned, gapEq]
        exact (Analysis.transientContractedGap_self _).symm

/--
The value-normalization suffix turns any structurally complete shift-atomic
checkpoint into `RankPrepared`.

This is the reusable endpoint theorem for a structural atomicizer.  The
structural prefix need only establish validity, completeness, one empty
growing block per owner-side, and `ShiftAtomic`; all value repair is supplied
here by a checked trace.
-/
theorem exists_adjustValuesToOne_rankPrepared {n : ℕ}
    {state : State n} {params : Interface.Parameters}
    (atomic : state.ShiftAtomic)
    (valid : state.Valid params)
    (complete : state.Complete)
    (oneGrowing : state.OneGrowingPerSide)
    (rootValue : state.value state.view.root = 1) :
    ∃ events final,
      Trace params state events final ∧
        final.ShiftAtomic ∧ final.RankPrepared params ∧
          final.view = state.view ∧
          Interface.totalInserts (eraseOperations events) = 0 ∧
          Interface.totalIncreases (eraseOperations events) = 0 := by
  let elements := state.allElements
  let final := state.adjustValuesToOne elements
  let events := state.adjustValuesToOneEvents elements
  have trace : Trace params state events final :=
    state.adjustValuesToOne_trace elements valid
  have finalValid : final.Valid params := trace.final_valid
  have finalAtomic : final.ShiftAtomic := by
    intro block blockMember
    have beforeMember : block ∈ state.blocks := by
      simpa [final] using blockMember
    exact atomic block beforeMember
  have finalComplete : final.Complete := by
    intro element
    simpa [final] using complete element
  have finalOneGrowing : final.OneGrowingPerSide := by
    have blocksEq : final.blocks = state.blocks := by
      simp [final]
    rw [State.OneGrowingPerSide, blocksEq]
    exact oneGrowing
  have finalGrowingTopmost : final.GrowingTopmost := by
    intro id
    dsimp only
    intro growingMode
    have blockMember :
        final.blocks.get id ∈ final.blocks :=
      List.get_mem _ id
    rcases finalAtomic (final.blocks.get id) blockMember with
        growingCase | shrinkingCase
    · refine
        ⟨final.view.topDown
            (final.blocks.get id).owner
            (final.blocks.get id).side, ?_⟩
      rw [growingCase.2]
      simp
    · rw [growingMode] at shrinkingCase
      simp at shrinkingCase
  have rootNotMember : state.view.root ∉ elements := by
    exact valid.root_not_mem
  have finalRootValue : final.value final.view.root = 1 := by
    rw [show final.view.root = state.view.root by simp [final]]
    rw [show final.value state.view.root =
        state.value state.view.root by
      exact state.adjustValuesToOne_value_of_not_mem
        elements rootNotMember]
    exact rootValue
  have finalAssignedValue :
      ∀ element ∈ final.allElements, final.value element = 1 := by
    intro element member
    apply state.adjustValuesToOne_value_eq_one_of_mem
    simpa [elements, final] using member
  have finalValues :
      final.ValuesRealizeGaps :=
    valuesRealizeGaps_of_shiftAtomic_of_values_eq_one
      finalAtomic finalValid finalRootValue finalAssignedValue
  have finalPrepared : final.RankPrepared params :=
    ⟨finalValid, finalComplete, finalOneGrowing,
      finalGrowingTopmost, finalValues⟩
  exact
    ⟨events, final, trace, finalAtomic, finalPrepared,
      state.adjustValuesToOne_view elements,
      state.totalInserts_adjustValuesToOneEvents_eq_zero elements,
      state.totalIncreases_adjustValuesToOneEvents_eq_zero
        elements valid⟩

end State

/--
The exact structural prefix still required for universal atomicization.

Conversion, creation, and splitting preserve the heap view and values.  The
prefix therefore records those equalities explicitly, together with the four
structural facts needed by `exists_adjustValuesToOne_rankPrepared`.  No
semantic shortcut is hidden here: `trace` must be a genuine rich trace.
-/
structure StructuralShiftAtomicization {n : ℕ}
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
  complete : final.Complete
  oneGrowingPerSide : final.OneGrowingPerSide

/--
A structural atomicizer works for every stable state, without changing its
heap view.  This is the sole remaining list-induction obligation after the
checked local convert/create and split steps below.
-/
def StructuralShiftAtomicizer (params : Interface.Parameters) : Prop :=
  ∀ {n : ℕ} (initial : State n), initial.Stable params →
    Nonempty (StructuralShiftAtomicization params initial)

/-- Full trace certificate exported by structural atomicization plus values. -/
structure ShiftAtomicPreparation {n : ℕ}
    (params : Interface.Parameters) (initial : State n) where
  events : List (Event n)
  final : State n
  trace : Trace params initial events final
  shiftAtomic : final.ShiftAtomic
  rankPrepared : final.RankPrepared params
  view_eq : final.view = initial.view

/--
The structural list induction is sufficient for full shift-atomic
`RankPrepared` preparation.

The suffix is completely constructed: it adjusts every assigned value to one
by visible unit changes, proves that empty growing and singleton shrinking
blocks realize those values, and appends the two rich traces.
-/
theorem shiftAtomicPreparation_of_structuralAtomicizer
    {params : Interface.Parameters}
    (atomicizer : StructuralShiftAtomicizer params)
    {n : ℕ} (initial : State n) (stable : initial.Stable params) :
    Nonempty (ShiftAtomicPreparation params initial) := by
  obtain ⟨structural⟩ := atomicizer initial stable
  have structuralRootValue :
      structural.final.value structural.final.view.root = 1 := by
    rw [structural.view_eq, structural.value_eq]
    exact stable.2.2.2.2.2.1
  obtain ⟨suffixEvents, final, suffixTrace, finalAtomic,
      finalPrepared, suffixViewEq, _suffixInserts,
      _suffixIncreases⟩ :=
    State.exists_adjustValuesToOne_rankPrepared
      structural.shiftAtomic structural.trace.final_valid
      structural.complete structural.oneGrowingPerSide
      structuralRootValue
  refine ⟨{
    events := structural.events ++ suffixEvents
    final := final
    trace := structural.trace.append suffixTrace
    shiftAtomic := finalAtomic
    rankPrepared := finalPrepared
    view_eq := ?_
  }⟩
  exact suffixViewEq.trans structural.view_eq

/--
A structural atomicizer already suffices for every ordinary splay-tree
rotation.

After atomicizing at the original represented view, all singleton shrinking
blocks can be silently rebased to the canonical view of the target splay-tree
shape.  A fixed rank snapshot has the same canonical root for every tree
shape, so the checked same-root rebase theorem applies directly.
-/
theorem splayRotationTraceRealizer_of_structuralAtomicizer
    {n : ℕ} {params : Interface.Parameters} {snapshot : Rank.Snapshot n}
    (atomicizer : StructuralShiftAtomicizer params) :
    SplayRotationTraceRealizer params snapshot := by
  intro rotationDepth beforeTree afterTree initial _rotation
    initialRepresents
  obtain ⟨atomicPreparation⟩ :=
    shiftAtomicPreparation_of_structuralAtomicizer
      atomicizer initial initialRepresents.stable
  have atomicHeapOrdered :
      atomicPreparation.final.view.HeapOrdered := by
    rw [atomicPreparation.view_eq]
    exact initialRepresents.heapOrdered
  have atomicStable :
      atomicPreparation.final.Stable params :=
    atomicPreparation.rankPrepared.stable atomicHeapOrdered
  have atomicRepresents :
      atomicPreparation.final.Represents params snapshot beforeTree :=
    ⟨atomicStable,
      atomicPreparation.view_eq.trans initialRepresents.view_eq⟩
  let afterView :=
    Canonical.canonicalHeapView snapshot afterTree
  have rootEq :
      afterView.root = atomicPreparation.final.view.root := by
    change
      Canonical.canonicalRoot snapshot afterTree =
        atomicPreparation.final.view.root
    rw [atomicPreparation.view_eq, initialRepresents.view_eq]
    exact Canonical.canonicalRoot_eq snapshot afterTree beforeTree
  let final :=
    atomicPreparation.final.rebaseShiftAtomic afterView
  have rebaseTrace :
      Trace params atomicPreparation.final [.silent] final :=
    atomicPreparation.shiftAtomic.rebase_trace
      atomicPreparation.rankPrepared.valid rootEq
  have finalPrepared : final.RankPrepared params :=
    atomicPreparation.shiftAtomic.rebase_rankPrepared atomicStable rootEq
  have finalStable : final.Stable params :=
    finalPrepared.stable
      (Canonical.canonicalHeapView_heapOrdered snapshot afterTree)
  have finalRepresents :
      final.Represents params snapshot afterTree :=
    ⟨finalStable, rfl⟩
  exact
    ⟨{
      initial_represents := initialRepresents
      final := final
      events := atomicPreparation.events ++ [.silent]
      trace := atomicPreparation.trace.append rebaseTrace
      final_represents := finalRepresents
    }⟩

/--
Together with the explicit root-swap macro, structural atomicization also
closes the unrestricted comparison-rotation preparer.

Atomicization is first performed at the original represented view.  The
existing shift-atomic preparer handles the comparison rotation from that
intermediate state; reconstructing the certificate merely prepends the
checked atomicization trace.
-/
theorem comparisonRotationPreparer_of_structuralAtomicizer_and_rootSwap
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    (atomicizer : StructuralShiftAtomicizer params)
    (rootSwap : ComparisonRootSwapBuilder params splayTree) :
    ComparisonRotationPreparer params splayTree := by
  intro rotationDepth beforeComparison afterComparison initial
    rotation initialRepresents
  obtain ⟨atomicPreparation⟩ :=
    shiftAtomicPreparation_of_structuralAtomicizer
      atomicizer initial initialRepresents.stable
  have atomicHeapOrdered :
      atomicPreparation.final.view.HeapOrdered := by
    rw [atomicPreparation.view_eq]
    exact initialRepresents.heapOrdered
  have atomicStable :
      atomicPreparation.final.Stable params :=
    atomicPreparation.rankPrepared.stable atomicHeapOrdered
  have atomicRepresents :
      atomicPreparation.final.Represents params
        (Rank.Snapshot.ofTree beforeComparison) splayTree :=
    ⟨atomicStable,
      atomicPreparation.view_eq.trans initialRepresents.view_eq⟩
  have shiftAtomicPreparer :
      ShiftAtomicComparisonRotationPreparer params splayTree :=
    shiftAtomicComparisonRotationPreparer_of_rootSwapBuilder rootSwap
  obtain ⟨certificate⟩ :=
    shiftAtomicPreparer rotation atomicRepresents
      atomicPreparation.shiftAtomic
  exact
    ⟨{
      rotation := certificate.rotation
      initial_represents := initialRepresents
      elementShiftAt := certificate.elementShiftAt
      exactUpdate := certificate.exactUpdate
      unitShift := certificate.unitShift
      blockShift := certificate.blockShift
      prepared := certificate.prepared
      prefixEvents :=
        atomicPreparation.events ++ certificate.prefixEvents
      prefixTrace :=
        atomicPreparation.trace.append certificate.prefixTrace
      rankPrepared := certificate.rankPrepared
      view_eq := certificate.view_eq
      blocksAligned := certificate.blocksAligned
    }⟩

namespace State

private theorem converted_growingCount_add_one {n : ℕ}
    (blocks : List (Block n)) (index : ℕ) (selected : Block n)
    (intervalGap : ℤ)
    (found : blocks[index]? = some selected)
    (growing : selected.mode = .growing) :
    ((blocks.modify index fun block =>
          block.converted intervalGap).map Block.toInterface |>.filter
        fun block =>
          decide
            (block.mode = .growing ∧
              block.creator = selected.creator)).length + 1 =
      (blocks.map Block.toInterface |>.filter fun block =>
        decide
          (block.mode = .growing ∧
            block.creator = selected.creator)).length := by
  induction blocks generalizing index selected with
  | nil =>
      simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst selected
          rw [List.modify_zero_cons]
          simp [Block.converted, Block.toInterface, growing]
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          rw [List.modify_succ_cons]
          simp only [List.map_cons, List.filter_cons]
          split <;> simp_all

/--
Converting a found growing block frees one slot for its creator, independently
of the supplied signed interval gap.
-/
theorem convert_growingCount_add_one {n : ℕ}
    (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (intervalGap : ℤ)
    (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing) :
    (state.convert blockId intervalGap).toInterface.growingCount
          block.creator + 1 =
      state.toInterface.growingCount block.creator := by
  simpa [State.convert, State.toInterface,
    Interface.State.growingCount] using
    converted_growingCount_add_one state.blocks blockId block intervalGap
      found growing

/--
Convert one found growing block and immediately create its empty growing
replacement at the same creator-side placement.

The caller supplies the attained interval minimum for the converted block and
the exact post-conversion capacity fact follows automatically: conversion
removes the selected growing block before its replacement is created.  Both
primitive operations and both endpoint-validity checks remain visible in the
resulting two-event trace.
-/
theorem convertAndCreate_trace {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (blockId : Interface.BlockId) (block : Block n)
    (intervalGap : ℤ) (valid : state.Valid params)
    (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing)
    (gapValid :
      (block.converted intervalGap).GapValid state.view) :
    Trace params state
      [.operation (.convert blockId),
        .operation (.create block.creator)]
      ((state.convert blockId intervalGap).create
        block.creator block.side) := by
  have convertStep :
      Step params state (.operation (.convert blockId))
        (state.convert blockId intervalGap) :=
    state.convert_step blockId block intervalGap valid found growing gapValid
  have room :
      (state.convert blockId intervalGap).toInterface.growingCount
          block.creator <
        params.growingLimit := by
    have beforeBound :=
      valid.toInterface.2.2 block.creator
    have countEq :=
      state.convert_growingCount_add_one
        blockId block intervalGap found growing
    omega
  have createStep :
      Step params (state.convert blockId intervalGap)
        (.operation (.create block.creator))
        ((state.convert blockId intervalGap).create
          block.creator block.side) :=
    (state.convert blockId intervalGap).create_step
      block.creator block.side convertStep.after_valid room
  exact Trace.cons convertStep (Trace.singleton createStep)

/--
Every found growing block admits the convert-and-replace macro.

For an empty block the administrative shrinking gap is zero.  For a nonempty
block, finiteness supplies an attained minimum of its signed raw gaps.
-/
theorem exists_convertAndCreate_trace {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (blockId : Interface.BlockId) (block : Block n)
    (valid : state.Valid params)
    (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing) :
    ∃ intervalGap,
      Trace params state
        [.operation (.convert blockId),
          .operation (.create block.creator)]
        ((state.convert blockId intervalGap).create
          block.creator block.side) := by
  by_cases empty : block.elements = []
  · refine ⟨0, state.convertAndCreate_trace blockId block 0
      valid found growing ?_⟩
    simp [Block.GapValid, Block.converted, empty]
  · obtain ⟨intervalGap, minimum⟩ :=
      Block.exists_intervalGap state.view block.elements empty
    refine ⟨intervalGap,
      state.convertAndCreate_trace blockId block intervalGap
        valid found growing ?_⟩
    simp only [Block.GapValid, Block.converted]
    exact Or.inr ⟨empty, minimum⟩

/--
Split the head from a shrinking block with at least two elements.

The prefix becomes a singleton with interval gap equal to its raw gap.  A
finite-minimum witness supplies the recomputed suffix gap.  The suffix length
strictly decreases, which is the termination measure for the remaining
structural list induction.
-/
theorem exists_splitHead_trace {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (sourceId : Interface.BlockId) (source : Block n)
    (head : Element n) (tail : List (Element n))
    (valid : state.Valid params)
    (found : state.blocks[sourceId]? = some source)
    (shrinking : source.mode = .shrinking)
    (elementsEq : source.elements = head :: tail)
    (tailNonempty : tail ≠ []) :
    ∃ suffixGap,
      let final :=
        state.split sourceId source 1
          (state.view.rawGap head) suffixGap
      Trace params state
          [.operation (.split sourceId 1)] final ∧
        (source.splitPrefix 1
            (state.view.rawGap head)).elements = [head] ∧
        (source.splitSuffix 1 suffixGap).elements = tail ∧
        (source.splitSuffix 1 suffixGap).elements.length <
          source.elements.length := by
  obtain ⟨suffixGap, suffixMinimum⟩ :=
    Block.exists_intervalGap state.view tail tailNonempty
  have prefixGapValid :
      (source.splitPrefix 1
        (state.view.rawGap head)).GapValid state.view := by
    exact
      Block.singleton_shrinking_gapValid state.view
        (source.splitPrefix 1 (state.view.rawGap head))
        (by simp [Block.splitPrefix, shrinking])
        head
        (by simp [Block.splitPrefix, elementsEq])
        rfl
  have suffixGapValid :
      (source.splitSuffix 1 suffixGap).GapValid state.view := by
    simp only [Block.GapValid]
    rw [show
      (source.splitSuffix 1 suffixGap).mode =
          .shrinking by simp [Block.splitSuffix, shrinking]]
    right
    constructor
    · simpa [Block.splitSuffix, elementsEq] using tailNonempty
    · simpa [Block.splitSuffix, elementsEq] using suffixMinimum
  have step :
      Step params state (.operation (.split sourceId 1))
        (state.split sourceId source 1
          (state.view.rawGap head) suffixGap) :=
    state.split_step sourceId source 1
      (state.view.rawGap head) suffixGap valid found shrinking
      (by simp [elementsEq]) prefixGapValid suffixGapValid
  refine ⟨suffixGap, Trace.singleton step, ?_, ?_, ?_⟩
  · simp [Block.splitPrefix, elementsEq]
  · simp [Block.splitSuffix, elementsEq]
  · simp [Block.splitSuffix, elementsEq]

end State

end Splay.Lazy
