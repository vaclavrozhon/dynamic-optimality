import Splay.Lazy.ShiftAtomicizationComplete
import Splay.Lazy.AtomicRealizers
import Splay.Lazy.ComparisonRootSwapComplete

namespace Splay.Lazy

open Splay.Rank

/--
Every stable state has a checked shift-atomic, rank-prepared continuation.

This is the assumption-free endpoint obtained by instantiating the generic
reduction with the terminating structural atomicizer.
-/
theorem existsShiftAtomicPreparation
    {n : ℕ} {params : Interface.Parameters}
    (initial : State n) (stable : initial.Stable params) :
    Nonempty (ShiftAtomicPreparation params initial) :=
  shiftAtomicPreparation_of_structuralAtomicizer
    (State.structuralShiftAtomicizer params) initial stable

/--
Every ordinary splay-tree rotation is realizable while the comparison-rank
snapshot is fixed.
-/
theorem splayRotationTraceRealizer
    {n : ℕ} (params : Interface.Parameters) (snapshot : Snapshot n) :
    SplayRotationTraceRealizer params snapshot :=
  splayRotationTraceRealizer_of_structuralAtomicizer
    (State.structuralShiftAtomicizer params)

/--
At a fixed comparison snapshot, every change of splay-tree shape has a rich
represented transition from any represented historical state.
-/
theorem existsRepresentedTransition_fixedSnapshot
    {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n}
    {beforeTree afterTree : Tree.BST 0 n}
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial) :=
  existsRepresentedTransition_of_structuralAtomicizer_fixedSnapshot
    (State.structuralShiftAtomicizer params) initialRepresents

/--
The structural endpoint obligation for a whole rooted splay is unconditional
in the interface parameters and the finite tree size.

The underlying reduction atomizes and uses the current projection-preserving
`Step.silent` relation to rebase to the execution's final fixed-snapshot view.
It proves represented reachability, but does not replay or classify the
individual rotations of the supplied `SplayExecution`.
-/
theorem rootedSplayTraceRealizer
    (params : Interface.Parameters) :
    ∀ {n : ℕ}, RootedSplayTraceRealizer (n := n) params :=
  rootedSplayTraceRealizer_of_structuralAtomicizer
    (State.structuralShiftAtomicizer params)

/--
Once the independent root-swap macro is supplied, the unrestricted
comparison-rotation preparer has no remaining atomicization premise.
-/
theorem comparisonRotationPreparer_of_rootSwapBuilder
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    (builder : ComparisonRootSwapBuilder params splayTree) :
    ComparisonRotationPreparer params splayTree :=
  comparisonRotationPreparer_of_structuralAtomicizer_of_rootSwapBuilder
    (State.structuralShiftAtomicizer params) builder

/--
Trace-level comparison-rotation realization has precisely the same remaining
root-swap premise.
-/
theorem comparisonRotationTraceRealizer_of_rootSwapBuilder
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    (builder : ComparisonRootSwapBuilder params splayTree) :
    ComparisonRotationTraceRealizer params splayTree :=
  comparisonRotationTraceRealizer_of_structuralAtomicizer_of_rootSwapBuilder
    (State.structuralShiftAtomicizer params) builder

/--
Every comparison-tree rotation has a prepared rich-trace prefix.  Both finite
implementation obligations are discharged by the concrete structural
atomicizer and root-swap macro.
-/
theorem comparisonRotationPreparer
    {n : ℕ} (params : Interface.Parameters)
    (splayTree : Tree.BST 0 n) :
    ComparisonRotationPreparer params splayTree :=
  comparisonRotationPreparer_of_rootSwapBuilder
    (comparisonRootSwapBuilder params splayTree)

/--
Every comparison-tree rotation is realizable from an arbitrary represented
historical state.
-/
theorem comparisonRotationTraceRealizer
    {n : ℕ} (params : Interface.Parameters)
    (splayTree : Tree.BST 0 n) :
    ComparisonRotationTraceRealizer params splayTree :=
  comparisonRotationTraceRealizer_of_rootSwapBuilder
    (comparisonRootSwapBuilder params splayTree)

end Splay.Lazy
