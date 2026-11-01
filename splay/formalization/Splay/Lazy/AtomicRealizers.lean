import Splay.Lazy.ShiftAtomicization
import Splay.Lazy.ComparisonRootSwap
import Splay.Lazy.SplayPairingSchedule

namespace Splay.Lazy

open Splay.Rank

/--
Atomicizing an arbitrary represented input is enough to expose the
shift-atomic comparison-rotation preparer supplied by a root-swap builder.

The structural/value-normalization trace is retained as the first part of the
prepared prefix.  In particular, this reduction does not replace the
historical input by a fresh canonical state.
-/
theorem comparisonRotationPreparer_of_structuralAtomicizer_of_rootSwapBuilder
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    (atomicizer : StructuralShiftAtomicizer params)
    (builder : ComparisonRootSwapBuilder params splayTree) :
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
  have atomicRepresents :
      atomicPreparation.final.Represents params
        (Snapshot.ofTree beforeComparison) splayTree := by
    exact
      ⟨atomicPreparation.rankPrepared.stable atomicHeapOrdered,
        atomicPreparation.view_eq.trans initialRepresents.view_eq⟩
  obtain ⟨certificate⟩ :=
    (shiftAtomicComparisonRotationPreparer_of_rootSwapBuilder builder)
      rotation atomicRepresents atomicPreparation.shiftAtomic
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

/--
The same two constructors discharge the public one-rotation comparison trace
API on every represented input.
-/
theorem comparisonRotationTraceRealizer_of_structuralAtomicizer_of_rootSwapBuilder
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    (atomicizer : StructuralShiftAtomicizer params)
    (builder : ComparisonRootSwapBuilder params splayTree) :
    ComparisonRotationTraceRealizer params splayTree :=
  comparisonRotationTraceRealizer_of_preparer
    (comparisonRotationPreparer_of_structuralAtomicizer_of_rootSwapBuilder
      atomicizer builder)

/--
A structural atomicizer together with root-swap builders for every finite
tree size yields the standard comparison preparer uniformly.
-/
theorem comparisonRotationPreparers_of_structuralAtomicizer
    {params : Interface.Parameters}
    (atomicizer : StructuralShiftAtomicizer params)
    (builders :
      ∀ {n : ℕ} (splayTree : Tree.BST 0 n),
        ComparisonRootSwapBuilder params splayTree) :
    ∀ {n : ℕ} (splayTree : Tree.BST 0 n),
      ComparisonRotationPreparer params splayTree := by
  intro n splayTree
  exact
    comparisonRotationPreparer_of_structuralAtomicizer_of_rootSwapBuilder
      atomicizer (builders splayTree)

/--
Uniform root-swap builders likewise yield the standard comparison trace
realizers uniformly.
-/
theorem comparisonRotationTraceRealizers_of_structuralAtomicizer
    {params : Interface.Parameters}
    (atomicizer : StructuralShiftAtomicizer params)
    (builders :
      ∀ {n : ℕ} (splayTree : Tree.BST 0 n),
        ComparisonRootSwapBuilder params splayTree) :
    ∀ {n : ℕ} (splayTree : Tree.BST 0 n),
      ComparisonRotationTraceRealizer params splayTree := by
  intro n splayTree
  exact
    comparisonRotationTraceRealizer_of_structuralAtomicizer_of_rootSwapBuilder
      atomicizer (builders splayTree)

/--
After atomicization, any change of splay-tree shape at a fixed comparison
snapshot is one same-root silent rebase.

The canonical heap root is determined only by the fixed snapshot, not by the
splay-tree shape.  Atomic rebasing therefore preserves validity, and the
canonical target heap order upgrades the endpoint back to a represented
stable state.
-/
theorem existsRepresentedTransition_of_structuralAtomicizer_fixedSnapshot
    {n : ℕ} {params : Interface.Parameters}
    (atomicizer : StructuralShiftAtomicizer params)
    {snapshot : Snapshot n}
    {beforeTree afterTree : Tree.BST 0 n}
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial) := by
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
  have finalRepresents :
      final.Represents params snapshot afterTree := by
    refine ⟨finalStable, ?_⟩
    exact State.rebaseShiftAtomic_view
      atomicPreparation.final afterView
  exact
    ⟨{
      initial_represents := initialRepresents
      final := final
      events := atomicPreparation.events ++ [.silent]
      trace := atomicPreparation.trace.append suffixTrace
      final_represents := finalRepresents
    }⟩

/--
Structural shift atomicization is sufficient for the whole rooted splay
obligation.  The root and splay-execution premises remain part of the public
API, but the fixed-snapshot rebase above works for the resulting endpoints
without any further pairing hypothesis.
-/
theorem rootedSplayTraceRealizer_of_structuralAtomicizer
    {params : Interface.Parameters}
    (atomicizer : StructuralShiftAtomicizer params) :
    ∀ {n : ℕ}, RootedSplayTraceRealizer (n := n) params := by
  intro n comparisonTree beforeTree afterTree key initial
    _rooted _execution initialRepresents
  exact
    existsRepresentedTransition_of_structuralAtomicizer_fixedSnapshot
      atomicizer initialRepresents

end Splay.Lazy
