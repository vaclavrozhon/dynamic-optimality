import Splay.Lazy.InitializedExecution
import Splay.Rank.FromTree
import Splay.Tree.SplayExecution

namespace Splay.Lazy

open Splay.Rank

/--
The exact local obligation for one ordinary rotation of the **splay tree**.
The comparison-rank snapshot is fixed while the structural tree changes.

The input may retain any historical block list; a proof must produce the
actual final state and rich trace, again ending at a represented stable state.
-/
def SplayRotationTraceRealizer {n : ℕ}
    (params : Interface.Parameters) (snapshot : Snapshot n) : Prop :=
  ∀ {rotationDepth : ℕ}
      {beforeTree afterTree : Tree.BST 0 n}
      {initial : State n},
    Tree.BST.RotationAt rotationDepth beforeTree afterTree →
      initial.Represents params snapshot beforeTree →
        Nonempty
          (RepresentedTransition params
            snapshot beforeTree snapshot afterTree initial)

/--
The distinct local obligation for one rotation of the **comparison tree**.
Here the splay-tree shape is fixed while `Snapshot.ofTree` changes.

Keeping the two realizers separate prevents conflating the two tree roles in
the manuscript's dynamic construction.
-/
def ComparisonRotationTraceRealizer {n : ℕ}
    (params : Interface.Parameters) (splayTree : Tree.BST 0 n) : Prop :=
  ∀ {rotationDepth : ℕ}
      {beforeComparison afterComparison : Tree.BST 0 n}
      {initial : State n},
    Tree.BST.RotationAt rotationDepth
        beforeComparison afterComparison →
      initial.Represents params
        (Snapshot.ofTree beforeComparison) splayTree →
        Nonempty
          (RepresentedTransition params
            (Snapshot.ofTree beforeComparison) splayTree
            (Snapshot.ofTree afterComparison) splayTree initial)

end Splay.Lazy

namespace Splay.Tree.BST.RotationExecution

open Splay.Lazy
open Splay.Rank

/--
A one-rotation splay-tree realizer lifts to every flat splay-tree rotation
execution while keeping the comparison snapshot fixed.
-/
theorem existsRepresentedSplayTransition
    {params : Interface.Parameters}
    {n : ℕ} {snapshot : Snapshot n}
    (realizer : SplayRotationTraceRealizer params snapshot)
    {length : ℕ} {beforeTree afterTree : BST 0 n}
    (execution : RotationExecution length beforeTree afterTree)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial) := by
  induction length generalizing beforeTree afterTree initial with
  | zero =>
      cases execution
      exact ⟨RepresentedTransition.refl initialRepresents⟩
  | succ length ih =>
      cases execution with
      | step head tail =>
          obtain ⟨headTransition⟩ :=
            realizer head initialRepresents
          obtain ⟨tailTransition⟩ :=
            ih tail headTransition.final_represents
          exact
            ⟨headTransition.trans tailTransition⟩

/--
A one-rotation comparison-tree realizer likewise lifts to every flat
comparison-tree execution while keeping the splay-tree shape fixed.

Both lifts compose actual historical endpoints and never reset the block list
to the all-growing canonical list.
-/
theorem existsRepresentedComparisonTransition
    {params : Interface.Parameters}
    {n : ℕ} {splayTree : BST 0 n}
    (realizer : ComparisonRotationTraceRealizer params splayTree)
    {length : ℕ}
    {beforeComparison afterComparison : BST 0 n}
    (execution :
      RotationExecution length beforeComparison afterComparison)
    {initial : State n}
    (initialRepresents :
      initial.Represents params
        (Snapshot.ofTree beforeComparison) splayTree) :
    Nonempty
      (RepresentedTransition params
        (Snapshot.ofTree beforeComparison) splayTree
        (Snapshot.ofTree afterComparison) splayTree initial) := by
  induction length generalizing
      beforeComparison afterComparison initial with
  | zero =>
      cases execution
      exact ⟨RepresentedTransition.refl initialRepresents⟩
  | succ length ih =>
      cases execution with
      | step head tail =>
          obtain ⟨headTransition⟩ :=
            realizer head initialRepresents
          obtain ⟨tailTransition⟩ :=
            ih tail headTransition.final_represents
          exact
            ⟨headTransition.trans tailTransition⟩

end Splay.Tree.BST.RotationExecution

namespace Splay.Tree.BST.SplayExecution

open Splay.Lazy
open Splay.Rank

/--
The full contextual structural splay therefore has a rich represented trace
as soon as `SplayRotationTraceRealizer` is proved for the fixed comparison
snapshot.

`toRotationExecution` supplies exactly `beforeTree.depth key` ordinary
rotations; no separate global trace-composition or termination hypothesis is
needed here.
-/
theorem existsRepresentedTransition
    {params : Interface.Parameters}
    {n : ℕ} {snapshot : Snapshot n}
    (realizer : SplayRotationTraceRealizer params snapshot)
    {key : ℕ} {beforeTree afterTree : BST 0 n}
    (execution : SplayExecution key beforeTree afterTree)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial) :=
  execution.toRotationExecution.existsRepresentedSplayTransition
    realizer initialRepresents

/--
Prepending any genuine empty-block initialization certificate produces an
initialized full-splay execution whose interface projection starts at an
`Interface.State.Initial` state.
-/
theorem existsInitializedTransition
    {params : Interface.Parameters}
    {n : ℕ} {snapshot : Snapshot n}
    (realizer : SplayRotationTraceRealizer params snapshot)
    {key : ℕ} {beforeTree afterTree : BST 0 n}
    (execution : SplayExecution key beforeTree afterTree)
    (initialization :
      Initialization params snapshot beforeTree) :
    Nonempty
      (InitializedTransition params
        snapshot beforeTree snapshot afterTree) := by
  obtain ⟨transition⟩ :=
    execution.existsRepresentedTransition realizer
      initialization.final_represents
  exact
    ⟨{ initialization := initialization
       transition := transition }⟩

end Splay.Tree.BST.SplayExecution
