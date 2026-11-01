import Splay.Lazy.CanonicalState
import Splay.Lazy.Trace

namespace Splay.Lazy

open Splay.Rank

namespace State

/--
A rich lazy state represents a concrete rank snapshot and splay-tree shape when
it is stable and its structural heap view is the canonical one induced by those
two objects.

The block list is deliberately not required to equal `Canonical.canonicalBlocks`.
Conversions and splits preserve block identities and leave shrinking history
behind, so a nontrivial execution generally cannot return to the fixed,
all-growing block list of `Canonical.canonicalState`.
-/
structure Represents {n : ℕ} (state : State n)
    (params : Interface.Parameters) (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) : Prop where
  stable : state.Stable params
  view_eq : state.view = Canonical.canonicalHeapView snapshot tree

namespace Represents

theorem valid {n : ℕ} {state : State n}
    {params : Interface.Parameters} {snapshot : Snapshot n}
    {tree : Tree.BST 0 n}
    (represents : state.Represents params snapshot tree) :
    state.Valid params :=
  represents.stable.valid

theorem complete {n : ℕ} {state : State n}
    {params : Interface.Parameters} {snapshot : Snapshot n}
    {tree : Tree.BST 0 n}
    (represents : state.Represents params snapshot tree) :
    state.Complete :=
  represents.stable.2.1

theorem heapOrdered {n : ℕ} {state : State n}
    {params : Interface.Parameters} {snapshot : Snapshot n}
    {tree : Tree.BST 0 n}
    (represents : state.Represents params snapshot tree) :
    state.view.HeapOrdered :=
  represents.stable.2.2.1

theorem oneGrowingPerSide {n : ℕ} {state : State n}
    {params : Interface.Parameters} {snapshot : Snapshot n}
    {tree : Tree.BST 0 n}
    (represents : state.Represents params snapshot tree) :
    state.OneGrowingPerSide :=
  represents.stable.2.2.2.1

theorem growingTopmost {n : ℕ} {state : State n}
    {params : Interface.Parameters} {snapshot : Snapshot n}
    {tree : Tree.BST 0 n}
    (represents : state.Represents params snapshot tree) :
    state.GrowingTopmost :=
  represents.stable.2.2.2.2.1

theorem valuesRealizeGaps {n : ℕ} {state : State n}
    {params : Interface.Parameters} {snapshot : Snapshot n}
    {tree : Tree.BST 0 n}
    (represents : state.Represents params snapshot tree) :
    state.ValuesRealizeGaps :=
  represents.stable.2.2.2.2.2

theorem view_rank_eq {n : ℕ} {state : State n}
    {params : Interface.Parameters} {snapshot : Snapshot n}
    {tree : Tree.BST 0 n}
    (represents : state.Represents params snapshot tree) :
    state.view.rank = snapshot.rank := by
  rw [represents.view_eq]
  rfl

theorem view_parent_eq {n : ℕ} {state : State n}
    {params : Interface.Parameters} {snapshot : Snapshot n}
    {tree : Tree.BST 0 n}
    (represents : state.Represents params snapshot tree) :
    state.view.parent = Canonical.canonicalParent snapshot tree := by
  rw [represents.view_eq]
  rfl

/-- Any represented state exposes the BST-laminar child order used by the
article's top-most pairing update. -/
theorem nestedChildOrder {n : ℕ} {state : State n}
    {params : Interface.Parameters} {snapshot : Snapshot n}
    {tree : Tree.BST 0 n}
    (represents : state.Represents params snapshot tree) :
    state.view.NestedChildOrder := by
  rw [represents.view_eq]
  exact Canonical.canonicalHeapView_nestedChildOrder snapshot tree

end Represents

end State

namespace Canonical

/-- The canonical all-growing state is the initial representative. -/
theorem canonicalState_represents {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    (canonicalState snapshot tree).Represents params snapshot tree :=
  ⟨canonicalState_stable
      snapshot tree params growingLimit valueBound,
    rfl⟩

end Canonical

/--
A finite rich execution between represented states.

The final state and its historical block list are part of the certificate.
This makes transitions composable without incorrectly requiring the final
block list to be the fixed list of `Canonical.canonicalState`.
-/
structure RepresentedTransition {n : ℕ}
    (params : Interface.Parameters)
    (beforeSnapshot : Snapshot n) (beforeTree : Tree.BST 0 n)
    (afterSnapshot : Snapshot n) (afterTree : Tree.BST 0 n)
    (initial : State n) where
  initial_represents :
    initial.Represents params beforeSnapshot beforeTree
  final : State n
  events : List (Event n)
  trace : Trace params initial events final
  final_represents :
    final.Represents params afterSnapshot afterTree

namespace RepresentedTransition

/-- A represented state has the empty represented transition to itself. -/
def refl {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n} {tree : Tree.BST 0 n}
    {state : State n}
    (represents : state.Represents params snapshot tree) :
    RepresentedTransition params snapshot tree snapshot tree state where
  initial_represents := represents
  final := state
  events := []
  trace := Trace.nil represents.valid
  final_represents := represents

/-- Concatenate two compatible rich traces. -/
theorem trace_append {n : ℕ} {params : Interface.Parameters}
    {initial middle final : State n}
    {first second : List (Event n)}
    (firstTrace : Trace params initial first middle)
    (secondTrace : Trace params middle second final) :
    Trace params initial (first ++ second) final := by
  induction firstTrace with
  | nil _ =>
      simpa using secondTrace
  | cons head tail ih =>
      exact Trace.cons head (ih secondTrace)

/-- Represented transitions compose while retaining all interface events. -/
def trans {n : ℕ} {params : Interface.Parameters}
    {firstSnapshot middleSnapshot finalSnapshot : Snapshot n}
    {firstTree middleTree finalTree : Tree.BST 0 n}
    {initial : State n}
    (first :
      RepresentedTransition params
        firstSnapshot firstTree middleSnapshot middleTree initial)
    (second :
      RepresentedTransition params
        middleSnapshot middleTree finalSnapshot finalTree first.final) :
    RepresentedTransition params
      firstSnapshot firstTree finalSnapshot finalTree initial where
  initial_represents := first.initial_represents
  final := second.final
  events := first.events ++ second.events
  trace := trace_append first.trace second.trace
  final_represents := second.final_represents

/-- Every represented transition erases to a genuine abstract-interface trace. -/
theorem toInterface {n : ℕ} {params : Interface.Parameters}
    {beforeSnapshot afterSnapshot : Snapshot n}
    {beforeTree afterTree : Tree.BST 0 n}
    {initial : State n}
    (transition :
      RepresentedTransition params
        beforeSnapshot beforeTree afterSnapshot afterTree initial) :
    Interface.Trace params initial.toInterface
      (eraseOperations transition.events) transition.final.toInterface :=
  transition.trace.toInterface

end RepresentedTransition

end Splay.Lazy
