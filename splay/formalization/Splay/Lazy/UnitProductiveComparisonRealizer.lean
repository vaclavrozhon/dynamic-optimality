import Splay.Lazy.ProductiveFreeRealizers

namespace Splay.Lazy

open Splay.Rank

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

/--
One comparison rotation with at most one insert and at most one increase.
Thus its productive-event cost is at most two.
-/
structure UnitProductiveRepresentedTransition {n : ℕ}
    (params : Interface.Parameters)
    (beforeSnapshot : Snapshot n) (beforeTree : Tree.BST 0 n)
    (afterSnapshot : Snapshot n) (afterTree : Tree.BST 0 n)
    (initial : State n) where
  transition :
    RepresentedTransition params beforeSnapshot beforeTree
      afterSnapshot afterTree initial
  totalInserts_le_one :
    Interface.totalInserts (eraseOperations transition.events) ≤ 1
  totalIncreases_le_one :
    Interface.totalIncreases (eraseOperations transition.events) ≤ 1

namespace UnitProductiveRepresentedTransition

/-- Prepending a productive-free transition preserves the unit bounds. -/
def prependProductiveFree
    {n : ℕ} {params : Interface.Parameters}
    {firstSnapshot middleSnapshot finalSnapshot : Snapshot n}
    {firstTree middleTree finalTree : Tree.BST 0 n}
    {initial : State n}
    (first :
      ProductiveFreeRepresentedTransition params
        firstSnapshot firstTree middleSnapshot middleTree initial)
    (second :
      UnitProductiveRepresentedTransition params
        middleSnapshot middleTree finalSnapshot finalTree
        first.transition.final) :
    UnitProductiveRepresentedTransition params
      firstSnapshot firstTree finalSnapshot finalTree initial where
  transition := first.transition.trans second.transition
  totalInserts_le_one := by
    rw [RepresentedTransition.trans, eraseOperations_append,
      totalInserts_append, first.totalInserts_eq_zero, zero_add]
    exact second.totalInserts_le_one
  totalIncreases_le_one := by
    rw [RepresentedTransition.trans, eraseOperations_append,
      totalIncreases_append, first.totalIncreases_eq_zero, zero_add]
    exact second.totalIncreases_le_one

end UnitProductiveRepresentedTransition

private def preparationTransition
    {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n} {tree : Tree.BST 0 n}
    {initial : State n}
    (initialRepresents : initial.Represents params snapshot tree)
    (preparation :
      ProductiveFreeShiftAtomicPreparation params initial)
    (finalRepresents :
      preparation.final.Represents params snapshot tree) :
    ProductiveFreeRepresentedTransition params
      snapshot tree snapshot tree initial where
  transition :=
    { initial_represents := initialRepresents
      final := preparation.final
      events := preparation.events
      trace := preparation.trace
      final_represents := finalRepresents }
  totalInserts_eq_zero := preparation.totalInserts_eq_zero
  totalIncreases_eq_zero := preparation.totalIncreases_eq_zero

/--
Positive-depth comparison rotations preserve the selected heap root.  After
productive-free atomicization, both structural rebasing and the exact rank
update are silent.
-/
theorem exists_unitProductiveComparisonTransition_of_depth_succ
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
        (Snapshot.ofTree beforeComparison) splayTree) :
    Nonempty
      (UnitProductiveRepresentedTransition params
        (Snapshot.ofTree beforeComparison) splayTree
        (Snapshot.ofTree afterComparison) splayTree initial) := by
  obtain ⟨atomicPreparation⟩ :=
    exists_productiveFreeShiftAtomicPreparation
      initial initialRepresents.stable
  have atomicHeapOrdered :
      atomicPreparation.final.view.HeapOrdered := by
    rw [atomicPreparation.view_eq]
    exact initialRepresents.heapOrdered
  have atomicStable :
      atomicPreparation.final.Stable params :=
    atomicPreparation.rankPrepared.stable atomicHeapOrdered
  have atomicRepresents :
      atomicPreparation.final.Represents params
        (Snapshot.ofTree beforeComparison) splayTree :=
    ⟨atomicStable,
      atomicPreparation.view_eq.trans initialRepresents.view_eq⟩
  let prepPrefix :=
    preparationTransition initialRepresents atomicPreparation
      atomicRepresents
  have canonicalRootEq :
      Canonical.canonicalRoot
          (Snapshot.ofTree afterComparison) splayTree =
        Canonical.canonicalRoot
          (Snapshot.ofTree beforeComparison) splayTree :=
    canonicalRoot_eq_of_rotationAt_depth_succ rotation splayTree
  let mixedView :=
    Canonical.canonicalHeapViewWithRank
      (Snapshot.ofTree afterComparison)
      (Snapshot.ofTree beforeComparison).rank
      splayTree
  have mixedRootEq :
      mixedView.root = atomicPreparation.final.view.root := by
    change
      Canonical.canonicalRoot
          (Snapshot.ofTree afterComparison) splayTree =
        atomicPreparation.final.view.root
    rw [canonicalRootEq, atomicPreparation.view_eq,
      initialRepresents.view_eq]
    rfl
  let prepared :=
    atomicPreparation.final.rebaseShiftAtomic mixedView
  have preparedTrace :
      Trace params atomicPreparation.final [.silent] prepared :=
    atomicPreparation.shiftAtomic.rebase_trace
      atomicPreparation.rankPrepared.valid mixedRootEq
  have preparedRankPrepared :
      prepared.RankPrepared params :=
    atomicPreparation.shiftAtomic.rebase_rankPrepared
      atomicStable mixedRootEq
  have preparedAtomic : prepared.ShiftAtomic :=
    atomicPreparation.shiftAtomic.rebase mixedView
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
  let certificate :
      PreparedComparisonRotation params splayTree
        (rotationDepth := rotationDepth.succ)
        (beforeComparison := beforeComparison)
        (afterComparison := afterComparison)
        atomicPreparation.final :=
    { rotation := rotation
      initial_represents := atomicRepresents
      elementShiftAt := elementShiftAt
      exactUpdate := exactUpdate
      unitShift := unitShift
      blockShift := blockShift
      prepared := prepared
      prefixEvents := [.silent]
      prefixTrace := preparedTrace
      rankPrepared := preparedRankPrepared
      view_eq := rfl
      blocksAligned := blocksAligned }
  let afterView :=
    Canonical.canonicalHeapViewWithRank
      (Snapshot.ofTree afterComparison)
      (Snapshot.ofTree afterComparison).rank
      splayTree
  let final :=
    certificate.prepared.absorbRankUpdate
      afterView certificate.blockShift
  have suffix :=
    certificate.rankPrepared.absorbRankUpdate_trace_stable
      certificate.compatible
      (PreparedComparisonRotation.afterView_heapOrdered afterComparison)
  have finalRepresents :
      final.Represents params
        (Snapshot.ofTree afterComparison) splayTree := by
    refine ⟨suffix.2, ?_⟩
    change
      afterView =
        Canonical.canonicalHeapView
          (Snapshot.ofTree afterComparison) splayTree
    exact
      Canonical.canonicalHeapViewWithRank_trueRank
        (Snapshot.ofTree afterComparison) splayTree
  let localTransition :
      ProductiveFreeRepresentedTransition params
        (Snapshot.ofTree beforeComparison) splayTree
        (Snapshot.ofTree afterComparison) splayTree
        atomicPreparation.final :=
    { transition :=
        { initial_represents := atomicRepresents
          final := final
          events := [.silent, .silent]
          trace := preparedTrace.append suffix.1
          final_represents := finalRepresents }
      totalInserts_eq_zero := by
        simp [eraseOperations, Event.operations,
          Interface.totalInserts]
      totalIncreases_eq_zero := by
        simp [eraseOperations, Event.operations,
          Interface.totalIncreases] }
  let combined := prepPrefix.trans localTransition
  exact
    ⟨{
      transition := combined.transition
      totalInserts_le_one := by
        rw [combined.totalInserts_eq_zero]
        omega
      totalIncreases_le_one := by
        rw [combined.totalIncreases_eq_zero]
        omega
    }⟩

/--
A root comparison rotation uses the checked exact root exchange: one insert
and one increase after productive-free atomicization.
-/
theorem exists_unitProductiveComparisonTransition_of_root
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    {beforeComparison afterComparison : Tree.BST 0 n}
    {initial : State n}
    (rotation :
      Tree.BST.RootRotation beforeComparison afterComparison)
    (initialRepresents :
      initial.Represents params
        (Snapshot.ofTree beforeComparison) splayTree) :
    Nonempty
      (UnitProductiveRepresentedTransition params
        (Snapshot.ofTree beforeComparison) splayTree
        (Snapshot.ofTree afterComparison) splayTree initial) := by
  obtain ⟨atomicPreparation⟩ :=
    exists_productiveFreeShiftAtomicPreparation
      initial initialRepresents.stable
  have atomicHeapOrdered :
      atomicPreparation.final.view.HeapOrdered := by
    rw [atomicPreparation.view_eq]
    exact initialRepresents.heapOrdered
  have atomicStable :
      atomicPreparation.final.Stable params :=
    atomicPreparation.rankPrepared.stable atomicHeapOrdered
  have atomicRepresents :
      atomicPreparation.final.Represents params
        (Snapshot.ofTree beforeComparison) splayTree :=
    ⟨atomicStable,
      atomicPreparation.view_eq.trans initialRepresents.view_eq⟩
  let prepPrefix :=
    preparationTransition initialRepresents atomicPreparation
      atomicRepresents
  let afterView :=
    Canonical.canonicalHeapView
      (Snapshot.ofTree afterComparison) splayTree
  have afterOrdered : afterView.HeapOrdered :=
    Canonical.canonicalHeapView_heapOrdered
      (Snapshot.ofTree afterComparison) splayTree
  have rootsNe :
      afterView.root ≠ atomicPreparation.final.view.root := by
    rw [atomicPreparation.view_eq, initialRepresents.view_eq]
    change
      Canonical.canonicalRoot
          (Snapshot.ofTree afterComparison) splayTree ≠
        Canonical.canonicalRoot
          (Snapshot.ofTree beforeComparison) splayTree
    cases rotation with
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
  obtain ⟨swapped, swapEvents, swapTrace, swappedStable,
      swappedAtomic, swappedView, swapInserts, swapIncreases⟩ :=
    exists_rootSwap_trace_of_shiftAtomic
      atomicStable atomicPreparation.shiftAtomic afterView
      afterOrdered rootsNe
  let localTransition :
      UnitProductiveRepresentedTransition params
        (Snapshot.ofTree beforeComparison) splayTree
        (Snapshot.ofTree afterComparison) splayTree
        atomicPreparation.final :=
    { transition :=
        { initial_represents := atomicRepresents
          final := swapped
          events := swapEvents
          trace := swapTrace
          final_represents := ⟨swappedStable, swappedView⟩ }
      totalInserts_le_one := by
        rw [swapInserts]
      totalIncreases_le_one := by
        rw [swapIncreases] }
  exact
    ⟨UnitProductiveRepresentedTransition.prependProductiveFree
      prepPrefix localTransition⟩

/-- Cost-aware one-comparison-rotation realizer. -/
def UnitProductiveComparisonRotationTraceRealizer
    {n : ℕ} (params : Interface.Parameters)
    (splayTree : Tree.BST 0 n) : Prop :=
  ∀ {rotationDepth : ℕ}
      {beforeComparison afterComparison : Tree.BST 0 n}
      {initial : State n},
    Tree.BST.RotationAt rotationDepth
        beforeComparison afterComparison →
      initial.Represents params
        (Snapshot.ofTree beforeComparison) splayTree →
      Nonempty
        (UnitProductiveRepresentedTransition params
          (Snapshot.ofTree beforeComparison) splayTree
          (Snapshot.ofTree afterComparison) splayTree initial)

/-- Every comparison rotation has productive cost at most two. -/
theorem unitProductiveComparisonRotationTraceRealizer
    {n : ℕ} (params : Interface.Parameters)
    (splayTree : Tree.BST 0 n) :
    UnitProductiveComparisonRotationTraceRealizer params splayTree := by
  intro rotationDepth beforeComparison afterComparison initial
    rotation represents
  cases rotation with
  | root rootRotation =>
      exact
        exists_unitProductiveComparisonTransition_of_root
          rootRotation represents
  | leftContext inner right =>
      exact
        exists_unitProductiveComparisonTransition_of_depth_succ
          (.leftContext inner right) represents
  | rightContext left inner =>
      exact
        exists_unitProductiveComparisonTransition_of_depth_succ
          (.rightContext left inner) represents

end Splay.Lazy
