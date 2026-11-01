import Splay.Lazy.AtomicInitializationCost

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
Shift-atomic preparation with an authenticated productive-free event list.
The structural core uses only convert/create/split, while value repair lowers
valid values to one.
-/
structure ProductiveFreeShiftAtomicPreparation {n : ℕ}
    (params : Interface.Parameters) (initial : State n) extends
      ShiftAtomicPreparation params initial where
  totalInserts_eq_zero :
    Interface.totalInserts (eraseOperations events) = 0
  totalIncreases_eq_zero :
    Interface.totalIncreases (eraseOperations events) = 0

/-- The terminating structural atomicizer yields productive-free preparation. -/
theorem exists_productiveFreeShiftAtomicPreparation
    {n : ℕ} {params : Interface.Parameters}
    (initial : State n) (stable : initial.Stable params) :
    Nonempty (ProductiveFreeShiftAtomicPreparation params initial) := by
  obtain ⟨structural⟩ :=
    State.structuralShiftAtomicizer params initial stable
  have structuralRootValue :
      structural.final.value structural.final.view.root = 1 := by
    rw [structural.view_eq, structural.value_eq]
    exact stable.2.2.2.2.2.1
  obtain ⟨suffixEvents, final, suffixTrace, finalAtomic,
      finalPrepared, suffixViewEq, suffixInserts,
      suffixIncreases⟩ :=
    State.exists_adjustValuesToOne_rankPrepared
      structural.shiftAtomic structural.trace.final_valid
      structural.complete structural.oneGrowingPerSide
      structuralRootValue
  refine
    ⟨{
      events := structural.events ++ suffixEvents
      final := final
      trace := structural.trace.append suffixTrace
      shiftAtomic := finalAtomic
      rankPrepared := finalPrepared
      view_eq := suffixViewEq.trans structural.view_eq
      totalInserts_eq_zero := ?_
      totalIncreases_eq_zero := ?_
    }⟩
  · rw [eraseOperations_append, totalInserts_append,
      structural.totalInserts_eq_zero, suffixInserts, zero_add]
  · rw [eraseOperations_append, totalIncreases_append,
      structural.totalIncreases_eq_zero, suffixIncreases, zero_add]

/-- A represented transition whose exact event list is productive-free. -/
structure ProductiveFreeRepresentedTransition {n : ℕ}
    (params : Interface.Parameters)
    (beforeSnapshot : Snapshot n) (beforeTree : Tree.BST 0 n)
    (afterSnapshot : Snapshot n) (afterTree : Tree.BST 0 n)
    (initial : State n) where
  transition :
    RepresentedTransition params beforeSnapshot beforeTree
      afterSnapshot afterTree initial
  totalInserts_eq_zero :
    Interface.totalInserts (eraseOperations transition.events) = 0
  totalIncreases_eq_zero :
    Interface.totalIncreases (eraseOperations transition.events) = 0

namespace ProductiveFreeRepresentedTransition

/-- Empty represented transitions are productive-free. -/
def refl
    {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n} {tree : Tree.BST 0 n}
    {state : State n}
    (represents : state.Represents params snapshot tree) :
    ProductiveFreeRepresentedTransition params
      snapshot tree snapshot tree state where
  transition := RepresentedTransition.refl represents
  totalInserts_eq_zero := by
    rfl
  totalIncreases_eq_zero := by
    rfl

/-- Productive-free transitions compose productively freely. -/
def trans
    {n : ℕ} {params : Interface.Parameters}
    {firstSnapshot middleSnapshot finalSnapshot : Snapshot n}
    {firstTree middleTree finalTree : Tree.BST 0 n}
    {initial : State n}
    (first :
      ProductiveFreeRepresentedTransition params
        firstSnapshot firstTree middleSnapshot middleTree initial)
    (second :
      ProductiveFreeRepresentedTransition params
        middleSnapshot middleTree finalSnapshot finalTree
        first.transition.final) :
    ProductiveFreeRepresentedTransition params
      firstSnapshot firstTree finalSnapshot finalTree initial where
  transition := first.transition.trans second.transition
  totalInserts_eq_zero := by
    rw [RepresentedTransition.trans, eraseOperations_append,
      totalInserts_append, first.totalInserts_eq_zero,
      second.totalInserts_eq_zero, zero_add]
  totalIncreases_eq_zero := by
    rw [RepresentedTransition.trans, eraseOperations_append,
      totalIncreases_append, first.totalIncreases_eq_zero,
      second.totalIncreases_eq_zero, zero_add]

end ProductiveFreeRepresentedTransition

/--
At a fixed rank snapshot every change of splay-tree shape has a
productive-free exact transition.
-/
theorem existsProductiveFreeRepresentedTransition_fixedSnapshot
    {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n}
    {beforeTree afterTree : Tree.BST 0 n}
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (ProductiveFreeRepresentedTransition params
        snapshot beforeTree snapshot afterTree initial) := by
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
  have suffixTrace :
      Trace params atomicPreparation.final [.silent] final := by
    exact
      atomicPreparation.shiftAtomic.rebase_trace
        atomicPreparation.rankPrepared.valid rootEq
  have finalPrepared :
      final.RankPrepared params := by
    exact
      atomicPreparation.shiftAtomic.rebase_rankPrepared
        atomicStable rootEq
  have finalStable :
      final.Stable params := by
    exact
      finalPrepared.stable
        (Canonical.canonicalHeapView_heapOrdered snapshot afterTree)
  let transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial :=
    { initial_represents := initialRepresents
      final := final
      events := atomicPreparation.events ++ [.silent]
      trace := atomicPreparation.trace.append suffixTrace
      final_represents := ⟨finalStable, rfl⟩ }
  refine
    ⟨{
      transition := transition
      totalInserts_eq_zero := ?_
      totalIncreases_eq_zero := ?_
    }⟩
  · change
      Interface.totalInserts
          (eraseOperations (atomicPreparation.events ++ [.silent])) = 0
    rw [eraseOperations_append, totalInserts_append,
      atomicPreparation.totalInserts_eq_zero]
    simp [eraseOperations, Event.operations,
      Interface.totalInserts]
  · change
      Interface.totalIncreases
          (eraseOperations (atomicPreparation.events ++ [.silent])) = 0
    rw [eraseOperations_append, totalIncreases_append,
      atomicPreparation.totalIncreases_eq_zero]
    simp [eraseOperations, Event.operations,
      Interface.totalIncreases]

/-- Cost-aware one-rotation realizer used by recursive splay provenance. -/
def ProductiveFreeSplayRotationTraceRealizer
    {n : ℕ} (params : Interface.Parameters) (snapshot : Snapshot n) : Prop :=
  ∀ {rotationDepth : ℕ}
      {beforeTree afterTree : Tree.BST 0 n}
      {initial : State n},
    Tree.BST.RotationAt rotationDepth beforeTree afterTree →
      initial.Represents params snapshot beforeTree →
      Nonempty
        (ProductiveFreeRepresentedTransition params
          snapshot beforeTree snapshot afterTree initial)

/-- The concrete structural atomicizer supplies the cost-aware realizer. -/
theorem productiveFreeSplayRotationTraceRealizer
    {n : ℕ} (params : Interface.Parameters) (snapshot : Snapshot n) :
    ProductiveFreeSplayRotationTraceRealizer params snapshot := by
  intro rotationDepth beforeTree afterTree initial _rotation represents
  exact existsProductiveFreeRepresentedTransition_fixedSnapshot represents

end Splay.Lazy
