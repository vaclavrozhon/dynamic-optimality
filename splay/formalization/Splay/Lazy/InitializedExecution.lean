import Splay.Lazy.CanonicalInitial
import Splay.Lazy.CanonicalTrace
import Splay.Lazy.Dynamic
import Splay.Interface.Consequences

namespace Splay.Lazy

open Splay.Rank

/--
The initialization certificate required before the abstract activity theorem
can be applied.

It starts at the empty-block canonical view, whose projection is an
`Interface.State.Initial`, and ends at any stable representative.  The final
block list is retained because subsequent splits and conversions preserve
historical identities.
-/
structure Initialization {n : ℕ}
    (params : Interface.Parameters)
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) where
  valueBound :
    Analysis.contractedGap snapshot.maxRank ≤ params.valueBound
  final : State n
  events : List (Event n)
  trace :
    Trace params
      (Canonical.emptyCanonicalState snapshot tree) events final
  final_represents :
    final.Represents params snapshot tree

namespace Initialization

/-- The erased initialization begins at a genuine abstract initial state. -/
theorem initial_toInterface_initial {n : ℕ}
    {params : Interface.Parameters}
    {snapshot : Snapshot n} {tree : Tree.BST 0 n}
    (initialization : Initialization params snapshot tree) :
    (Canonical.emptyCanonicalState snapshot tree).toInterface.Initial
      params :=
  Canonical.emptyCanonicalState_toInterface_initial
    snapshot tree params initialization.valueBound

/-- Erasing rich initialization events gives an ordinary interface trace. -/
theorem toInterface {n : ℕ}
    {params : Interface.Parameters}
    {snapshot : Snapshot n} {tree : Tree.BST 0 n}
    (initialization : Initialization params snapshot tree) :
    Interface.Trace params
      (Canonical.emptyCanonicalState snapshot tree).toInterface
      (eraseOperations initialization.events)
      initialization.final.toInterface :=
  initialization.trace.toInterface

end Initialization

/--
An initialized represented execution: first populate the interface from its
empty state, then run a composable structural transition.
-/
structure InitializedTransition {n : ℕ}
    (params : Interface.Parameters)
    (beforeSnapshot : Snapshot n) (beforeTree : Tree.BST 0 n)
    (afterSnapshot : Snapshot n) (afterTree : Tree.BST 0 n) where
  initialization :
    Initialization params beforeSnapshot beforeTree
  transition :
    RepresentedTransition params
      beforeSnapshot beforeTree afterSnapshot afterTree
      initialization.final

namespace InitializedTransition

/-- Complete rich event sequence, including the initialization prefix. -/
def events {n : ℕ} {params : Interface.Parameters}
    {beforeSnapshot afterSnapshot : Snapshot n}
    {beforeTree afterTree : Tree.BST 0 n}
    (execution :
      InitializedTransition params
        beforeSnapshot beforeTree afterSnapshot afterTree) :
    List (Event n) :=
  execution.initialization.events ++ execution.transition.events

/-- The complete initialized rich execution is a valid compositional trace. -/
theorem trace {n : ℕ} {params : Interface.Parameters}
    {beforeSnapshot afterSnapshot : Snapshot n}
    {beforeTree afterTree : Tree.BST 0 n}
    (execution :
      InitializedTransition params
        beforeSnapshot beforeTree afterSnapshot afterTree) :
    Trace params
      (Canonical.emptyCanonicalState beforeSnapshot beforeTree)
      execution.events execution.transition.final := by
  exact
    execution.initialization.trace.append
      execution.transition.trace

/-- Its projection is directly eligible for `Interface.ActivityBound`. -/
theorem toInterface {n : ℕ} {params : Interface.Parameters}
    {beforeSnapshot afterSnapshot : Snapshot n}
    {beforeTree afterTree : Tree.BST 0 n}
    (execution :
      InitializedTransition params
        beforeSnapshot beforeTree afterSnapshot afterTree) :
    Interface.Trace params
      (Canonical.emptyCanonicalState beforeSnapshot beforeTree).toInterface
      (eraseOperations execution.events)
      execution.transition.final.toInterface :=
  execution.trace.toInterface

/-- The projected initial endpoint satisfies the activity theorem's premise. -/
theorem initial_toInterface_initial {n : ℕ}
    {params : Interface.Parameters}
    {beforeSnapshot afterSnapshot : Snapshot n}
    {beforeTree afterTree : Tree.BST 0 n}
    (execution :
      InitializedTransition params
        beforeSnapshot beforeTree afterSnapshot afterTree) :
    (Canonical.emptyCanonicalState beforeSnapshot beforeTree).toInterface.Initial
      params :=
  execution.initialization.initial_toInterface_initial

/--
Once the standalone interface activity theorem is supplied, an initialized
rich execution satisfies its verified insert/value-change consequence
directly; no canonical-state/initial-state mismatch remains.
-/
theorem activity_le_inserts_and_increases {n : ℕ}
    {params : Interface.Parameters}
    {beforeSnapshot afterSnapshot : Snapshot n}
    {beforeTree afterTree : Tree.BST 0 n}
    (execution :
      InitializedTransition params
        beforeSnapshot beforeTree afterSnapshot afterTree)
    (activityBound : Interface.ActivityBound params.toShape) :
    ∃ insertConstant valueChangeConstant : ℕ,
      0 < insertConstant ∧
        0 < valueChangeConstant ∧
        Interface.totalActivity
            (eraseOperations execution.events) ≤
          insertConstant * params.valueBound *
              Interface.totalInserts
                (eraseOperations execution.events) +
            valueChangeConstant *
                Nat.clog 2 params.valueBound *
              (2 * Interface.totalIncreases
                    (eraseOperations execution.events) +
                (2 * n + 1) * params.valueBound) := by
  exact
    Interface.activity_le_inserts_and_increases
      activityBound execution.initial_toInterface_initial
      execution.toInterface

end InitializedTransition

end Splay.Lazy
