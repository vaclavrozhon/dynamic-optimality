import Splay.Lazy.NormalFormSchedule

namespace Splay.Rank.Snapshot

/--
A request served at the comparison-tree root has rank zero at its value
external node.  This is the exact comparison-root/rank fact used by the
pairing argument.
-/
theorem ofTree_rank_valuePos_eq_zero_of_hasRoot
    {n : ℕ} {tree : Tree.BST 0 n} {key : Fin n}
    (rooted : tree.HasRoot key.val) :
    (Snapshot.ofTree tree).rank (valuePos key) = 0 := by
  obtain ⟨left, right, rfl⟩ := rooted
  exact Tree.BST.externalDepth_root left right

end Splay.Rank.Snapshot

namespace Splay.Assumptions.NormalForm.ComparisonTrace.RequestGroup

/--
Every access in a chronological request group has rank zero in that group's
comparison snapshot.
-/
theorem rank_valuePos_eq_zero
    {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses}
    (group : RequestGroup trace)
    {request : Fin n} (member : request ∈ group.requests) :
    (Rank.Snapshot.ofTree (trace.state group.time)).rank
        (Rank.valuePos request) = 0 :=
  Rank.Snapshot.ofTree_rank_valuePos_eq_zero_of_hasRoot
    (group.serves member)

end Splay.Assumptions.NormalForm.ComparisonTrace.RequestGroup

namespace Splay.Lazy

open Splay.Rank

namespace Canonical

/--
For a literal canonical state, transient validity is the only parameter-
dependent part of stability.
-/
theorem canonicalState_stable_of_valid
    {n : ℕ} {params : Interface.Parameters}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (valid : (canonicalState snapshot tree).Valid params) :
    (canonicalState snapshot tree).Stable params :=
  ⟨valid,
    canonicalState_complete snapshot tree,
    canonicalHeapView_heapOrdered snapshot tree,
    canonicalState_oneGrowingPerSide snapshot tree,
    canonicalState_growingTopmost snapshot tree,
    canonicalState_valuesRealizeGaps snapshot tree⟩

end Canonical

/--
The local splay-pairing obligation actually needed by the chronological
normal-form schedule.

Unlike `SplayRotationTraceRealizer`, this predicate does not require every
ordinary rotation to be realizable in isolation.  It permits the first and
second pairings of all zig-zigs in one complete splay to be batched, exactly
as in the manuscript.  It also records the hypothesis used there: the
accessed key is the root of the current comparison tree.

An implementation must construct only an ordinary rich represented
transition.  Consequently every conversion, split, pass, delete, insert,
value update, and silent transfer in the pairing schedule remains checked by
the existing `Trace` semantics.
-/
def RootedSplayTraceRealizer {n : ℕ}
    (params : Interface.Parameters) : Prop :=
  ∀ {comparisonTree beforeTree afterTree : Tree.BST 0 n}
      {key : ℕ} {initial : State n},
    comparisonTree.HasRoot key →
      Tree.BST.SplayExecution key beforeTree afterTree →
        initial.Represents params
          (Snapshot.ofTree comparisonTree) beforeTree →
          Nonempty
            (RepresentedTransition params
              (Snapshot.ofTree comparisonTree) beforeTree
              (Snapshot.ofTree comparisonTree) afterTree initial)

/--
A still weaker, literal-canonical implementation target.

It asks for the pairing macro only from the canonical stable block layout and
requires it to restore the canonical layout at the endpoint.  This form is
closed under sequential composition and starts directly after
`canonicalInitialization`.
-/
def CanonicalRootedSplayTraceRealizer {n : ℕ}
    (params : Interface.Parameters) : Prop :=
  ∀ {comparisonTree beforeTree afterTree : Tree.BST 0 n}
      {key : ℕ},
    comparisonTree.HasRoot key →
      Tree.BST.SplayExecution key beforeTree afterTree →
        (Canonical.canonicalState
          (Snapshot.ofTree comparisonTree) beforeTree).Valid params →
          ∃ events : List (Event n),
            Trace params
              (Canonical.canonicalState
                (Snapshot.ofTree comparisonTree) beforeTree)
              events
              (Canonical.canonicalState
                (Snapshot.ofTree comparisonTree) afterTree)

/--
Literal-canonical counterpart of the independent comparison-rotation
obligation.  It is used only by the canonical schedule reduction below.
-/
def CanonicalComparisonRotationTraceRealizer {n : ℕ}
    (params : Interface.Parameters) : Prop :=
  ∀ {splayTree beforeComparison afterComparison : Tree.BST 0 n}
      {rotationDepth : ℕ},
    Tree.BST.RotationAt rotationDepth
        beforeComparison afterComparison →
      (Canonical.canonicalState
        (Snapshot.ofTree beforeComparison) splayTree).Valid params →
        ∃ events : List (Event n),
          Trace params
            (Canonical.canonicalState
              (Snapshot.ofTree beforeComparison) splayTree)
            events
            (Canonical.canonicalState
              (Snapshot.ofTree afterComparison) splayTree)

/--
The older per-ordinary-rotation obligation implies the rooted whole-splay
obligation.  The converse is intentionally not claimed.
-/
theorem rootedSplayTraceRealizer_of_rotationRealizers
    {n : ℕ} {params : Interface.Parameters}
    (rotationRealizer :
      ∀ comparisonTree : Tree.BST 0 n,
        SplayRotationTraceRealizer params
          (Snapshot.ofTree comparisonTree)) :
    RootedSplayTraceRealizer (n := n) params := by
  intro comparisonTree beforeTree afterTree key initial
    _rooted execution initialRepresents
  exact
    execution.existsRepresentedTransition
      (rotationRealizer comparisonTree) initialRepresents

end Splay.Lazy

namespace Splay.Lazy.CanonicalRootedSplayTraceRealizer

open Splay.Rank

/--
The depth-zero canonical case needs no pairing macro at all.
-/
theorem trace_of_depth_eq_zero
    {n : ℕ} {params : Interface.Parameters}
    {comparisonTree beforeTree afterTree : Tree.BST 0 n}
    {key : ℕ}
    (execution :
      Tree.BST.SplayExecution key beforeTree afterTree)
    (depthZero : beforeTree.depth key = 0)
    (initialValid :
      (Canonical.canonicalState
        (Snapshot.ofTree comparisonTree) beforeTree).Valid params) :
    ∃ events : List (Event n),
      Trace params
        (Canonical.canonicalState
          (Snapshot.ofTree comparisonTree) beforeTree)
        events
        (Canonical.canonicalState
          (Snapshot.ofTree comparisonTree) afterTree) := by
  have rotations := execution.toRotationExecution
  rw [depthZero] at rotations
  cases rotations
  exact
    ⟨[], Trace.nil initialValid⟩

end Splay.Lazy.CanonicalRootedSplayTraceRealizer

namespace Splay.Lazy.RootedSplayCounterexample

/--
The comparison-root premise does not make the same key the root of the splay
tree.  Hence the rooted schedule cannot in general collapse to the
zero-rotation case above.
-/
theorem comparisonRoot_does_not_force_splayDepthZero :
    ∃ (comparisonTree splayTree : Tree.BST 0 2),
      comparisonTree.HasRoot 0 ∧
        splayTree.depth 0 = 1 := by
  let comparisonTree : Tree.BST 0 2 :=
    .node (.empty 0) (.node (.empty 1) (.empty 2))
  let splayTree : Tree.BST 0 2 :=
    .node (.node (.empty 0) (.empty 1)) (.empty 2)
  refine ⟨comparisonTree, splayTree, ?_, ?_⟩
  · exact ⟨.empty 0, .node (.empty 1) (.empty 2), rfl⟩
  · rfl

/--
The same two-key example carries a genuine positive-depth complete splay
execution, so the missing rooted pairing case is non-vacuous.
-/
theorem comparisonRoot_allows_positiveSplayExecution :
    ∃ (comparisonTree beforeTree afterTree : Tree.BST 0 2),
      comparisonTree.HasRoot 0 ∧
        Tree.BST.SplayExecution 0 beforeTree afterTree ∧
        beforeTree.depth 0 = 1 := by
  let comparisonTree : Tree.BST 0 2 :=
    .node (.empty 0) (.node (.empty 1) (.empty 2))
  let beforeTree : Tree.BST 0 2 :=
    .node (.node (.empty 0) (.empty 1)) (.empty 2)
  obtain ⟨afterTree, execution⟩ :=
    Tree.BST.SplayExecution.exists_splay beforeTree
      (key := 0) (by omega) (by omega)
  exact
    ⟨comparisonTree, beforeTree, afterTree,
      ⟨.empty 0, .node (.empty 1) (.empty 2), rfl⟩,
      execution, rfl⟩

end Splay.Lazy.RootedSplayCounterexample

namespace Splay.Tree.BST.SplayExecution

open Splay.Lazy
open Splay.Rank

/--
The zero-rotation part of the rooted obligation is already unconditional:
when the requested key starts at depth zero, the complete splay execution has
identical endpoints and the represented transition is empty.
-/
theorem existsRepresentedTransition_of_depth_eq_zero
    {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n}
    {key : ℕ} {beforeTree afterTree : BST 0 n}
    (execution : SplayExecution key beforeTree afterTree)
    (depthZero : beforeTree.depth key = 0)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial) := by
  have rotations := execution.toRotationExecution
  rw [depthZero] at rotations
  cases rotations
  exact
    ⟨RepresentedTransition.refl initialRepresents⟩

end Splay.Tree.BST.SplayExecution

namespace Splay.Tree.BST.SplaySequence

open Splay.Lazy
open Splay.Rank

/--
A rooted whole-splay realizer composes directly through a dependent request
sequence whose requests are all served by one comparison-tree root.

This induction is the batching-friendly replacement for flattening the
sequence into ordinary rotations.
-/
theorem existsRepresentedTransition_of_rooted
    {n : ℕ} {params : Interface.Parameters}
    (realizer : RootedSplayTraceRealizer (n := n) params)
    {comparisonTree : BST 0 n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    (sequence : SplaySequence accesses beforeTree afterTree)
    (rooted :
      ∀ access ∈ accesses,
        comparisonTree.HasRoot access.val)
    {initial : State n}
    (initialRepresents :
      initial.Represents params
        (Snapshot.ofTree comparisonTree) beforeTree) :
    Nonempty
      (RepresentedTransition params
        (Snapshot.ofTree comparisonTree) beforeTree
        (Snapshot.ofTree comparisonTree) afterTree initial) := by
  induction sequence generalizing initial with
  | done tree =>
      exact
        ⟨RepresentedTransition.refl initialRepresents⟩
  | @next access accesses before middle after head tail ih =>
      have headRooted :
          comparisonTree.HasRoot access.val :=
        rooted access (by simp)
      obtain ⟨headTransition⟩ :=
        realizer headRooted head initialRepresents
      have tailRooted :
          ∀ request ∈ accesses,
            comparisonTree.HasRoot request.val := by
        intro request requestMember
        exact rooted request (by simp [requestMember])
      obtain ⟨tailTransition⟩ :=
        ih tailRooted headTransition.final_represents
      exact
        ⟨headTransition.trans tailTransition⟩

/--
The literal-canonical whole-splay macro composes through an entire same-root
request sequence, preserving literal canonical endpoints.
-/
theorem exists_canonicalTrace_of_rooted
    {n : ℕ} {params : Interface.Parameters}
    (realizer :
      CanonicalRootedSplayTraceRealizer (n := n) params)
    {comparisonTree : BST 0 n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    (sequence : SplaySequence accesses beforeTree afterTree)
    (rooted :
      ∀ access ∈ accesses,
        comparisonTree.HasRoot access.val)
    (initialValid :
      (Canonical.canonicalState
        (Snapshot.ofTree comparisonTree) beforeTree).Valid params) :
    ∃ events : List (Event n),
      Trace params
        (Canonical.canonicalState
          (Snapshot.ofTree comparisonTree) beforeTree)
        events
        (Canonical.canonicalState
          (Snapshot.ofTree comparisonTree) afterTree) := by
  induction sequence with
  | done tree =>
      exact
        ⟨[], Trace.nil initialValid⟩
  | @next access accesses before middle after head tail ih =>
      have headRooted :
          comparisonTree.HasRoot access.val :=
        rooted access (by simp)
      obtain ⟨headEvents, headTrace⟩ :=
        realizer headRooted head initialValid
      have tailRooted :
          ∀ request ∈ accesses,
            comparisonTree.HasRoot request.val := by
        intro request requestMember
        exact rooted request (by simp [requestMember])
      obtain ⟨tailEvents, tailTrace⟩ :=
        ih tailRooted headTrace.final_valid
      exact
        ⟨headEvents ++ tailEvents,
          headTrace.append tailTrace⟩

/--
Starting with the checked empty-block initialization, a canonical rooted
pairing macro realizes the complete fixed-comparison request sequence.
-/
theorem existsInitializedTransition_of_canonicalRooted
    {n : ℕ} {params : Interface.Parameters}
    (realizer :
      CanonicalRootedSplayTraceRealizer (n := n) params)
    {comparisonTree : BST 0 n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    (sequence : SplaySequence accesses beforeTree afterTree)
    (rooted :
      ∀ access ∈ accesses,
        comparisonTree.HasRoot access.val)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap
          (Snapshot.ofTree comparisonTree).maxRank ≤
        params.valueBound) :
    Nonempty
      (InitializedTransition params
        (Snapshot.ofTree comparisonTree) beforeTree
        (Snapshot.ofTree comparisonTree) afterTree) := by
  let initialization :=
    Canonical.canonicalInitialization
      (Snapshot.ofTree comparisonTree) beforeTree params
      growingLimit valueBound
  obtain ⟨events, trace⟩ :=
    sequence.exists_canonicalTrace_of_rooted
      realizer rooted
      (Canonical.canonicalState_valid
        (Snapshot.ofTree comparisonTree) beforeTree params
        growingLimit valueBound)
  let transition :
      RepresentedTransition params
        (Snapshot.ofTree comparisonTree) beforeTree
        (Snapshot.ofTree comparisonTree) afterTree
        initialization.final := by
    change
      RepresentedTransition params
        (Snapshot.ofTree comparisonTree) beforeTree
        (Snapshot.ofTree comparisonTree) afterTree
        (Canonical.canonicalState
          (Snapshot.ofTree comparisonTree) beforeTree)
    exact
      { initial_represents :=
          Canonical.canonicalState_represents
            (Snapshot.ofTree comparisonTree) beforeTree params
            growingLimit valueBound
        final :=
          Canonical.canonicalState
            (Snapshot.ofTree comparisonTree) afterTree
        events := events
        trace := trace
        final_represents :=
          Canonical.canonicalState_represents
            (Snapshot.ofTree comparisonTree) afterTree params
            growingLimit valueBound }
  exact
    ⟨{ initialization := initialization
       transition := transition }⟩

end Splay.Tree.BST.SplaySequence

namespace Splay.Assumptions.NormalForm.ComparisonTrace.Schedule

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

/--
The rooted whole-splay pairing lemma and the independent comparison-rotation
realizer compose through an arbitrary chronological normal-form schedule.

At a `next` node, comparison rotations are realized first, then the whole
same-time request group is realized with batched splays, and finally the tail
schedule is realized from the actual historical endpoint.  No canonical
block-list reset occurs.
-/
theorem existsRepresentedTransition
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    (splayRealizer : RootedSplayTraceRealizer (n := n) params)
    (comparisonRealizer :
      ∀ splayTree : Tree.BST 0 n,
        ComparisonRotationTraceRealizer params splayTree)
    {trace : ComparisonTrace n accesses}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {beforeTree afterTree : Tree.BST 0 n}
    (schedule :
      Schedule trace groups time beforeTree afterTree)
    {initial : State n}
    (initialRepresents :
      initial.Represents params
        (Snapshot.ofTree (trace.state time)) beforeTree) :
    Nonempty
      (RepresentedTransition params
        (Snapshot.ofTree (trace.state time)) beforeTree
        (Snapshot.ofTree trace.finalTree) afterTree initial) := by
  induction schedule generalizing initial with
  | @finish finishTime tree comparison =>
      exact
        comparison.existsRepresentedComparisonTransition
          (comparisonRealizer tree) initialRepresents
  | @next group groups startTime before middle after
      ordered comparison splay tail ih =>
      obtain ⟨comparisonTransition⟩ :=
        comparison.existsRepresentedComparisonTransition
          (comparisonRealizer before) initialRepresents
      have groupRooted :
          ∀ request ∈ group.requests,
            (trace.state group.time).HasRoot request.val := by
        intro request requestMember
        exact group.serves requestMember
      obtain ⟨splayTransition⟩ :=
        splay.existsRepresentedTransition_of_rooted
          splayRealizer groupRooted
          comparisonTransition.final_represents
      obtain ⟨tailTransition⟩ :=
        ih splayTransition.final_represents
      exact
        ⟨(comparisonTransition.trans splayTransition).trans
          tailTransition⟩

end Splay.Assumptions.NormalForm.ComparisonTrace.Schedule

namespace Splay.Assumptions.NormalForm.ComparisonTrace

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

/--
Kernel-checked global reduction from the two local dynamic realizers to a
realized chronological normal-form schedule.

The returned structural facts are the same facts exported by
`exists_normalFormSchedule`; the additional transition contains the complete
interleaved rich execution.
-/
theorem exists_realizedNormalFormSchedule
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    (splayRealizer : RootedSplayTraceRealizer (n := n) params)
    (comparisonRealizer :
      ∀ splayTree : Tree.BST 0 n,
        ComparisonRotationTraceRealizer params splayTree)
    (trace : ComparisonTrace n accesses)
    (initialSplayTree : Tree.BST 0 n)
    {initial : State n}
    (initialRepresents :
      initial.Represents params
        (Snapshot.ofTree trace.initialTree) initialSplayTree) :
    ∃ (groups : List (RequestGroup trace))
        (finalSplayTree : Tree.BST 0 n)
        (schedule :
          Schedule trace groups 0
            initialSplayTree finalSplayTree),
      Nonempty
          (RepresentedTransition params
            (Snapshot.ofTree trace.initialTree) initialSplayTree
            (Snapshot.ofTree trace.finalTree) finalSplayTree initial) ∧
        groups.flatMap RequestGroup.requests = accesses ∧
        groups.Pairwise
          (fun left right => left.time < right.time) ∧
        (∀ group ∈ groups,
          ∀ request ∈ group.requests,
            (trace.state group.time).HasRoot request.val) ∧
        schedule.comparisonRotationCount =
          trace.rotationCount := by
  obtain
      ⟨groups, finalSplayTree, schedule, requestsEq,
        ordered, rooted, comparisonCount⟩ :=
    trace.exists_normalFormSchedule initialSplayTree
  have initialAtZero :
      initial.Represents params
        (Snapshot.ofTree (trace.state 0)) initialSplayTree := by
    simpa [initialTree] using initialRepresents
  have realized :=
    schedule.existsRepresentedTransition
      splayRealizer comparisonRealizer initialAtZero
  exact
    ⟨groups, finalSplayTree, schedule, realized, requestsEq,
      ordered, rooted, comparisonCount⟩

/--
The same reduction started from the concrete empty-block canonical
initialization.  Thus a proof of `RootedSplayTraceRealizer`, together with the
separate comparison-rotation realizer, is enough to obtain an actual
initialized rich execution of the entire normal-form schedule.
-/
theorem exists_initializedRealizedNormalFormSchedule
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    (splayRealizer : RootedSplayTraceRealizer (n := n) params)
    (comparisonRealizer :
      ∀ splayTree : Tree.BST 0 n,
        ComparisonRotationTraceRealizer params splayTree)
    (trace : ComparisonTrace n accesses)
    (initialSplayTree : Tree.BST 0 n)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap
          (Snapshot.ofTree trace.initialTree).maxRank ≤
        params.valueBound) :
    ∃ (groups : List (RequestGroup trace))
        (finalSplayTree : Tree.BST 0 n)
        (schedule :
          Schedule trace groups 0
            initialSplayTree finalSplayTree),
      Nonempty
          (InitializedTransition params
            (Snapshot.ofTree trace.initialTree) initialSplayTree
            (Snapshot.ofTree trace.finalTree) finalSplayTree) ∧
        groups.flatMap RequestGroup.requests = accesses ∧
        groups.Pairwise
          (fun left right => left.time < right.time) ∧
        (∀ group ∈ groups,
          ∀ request ∈ group.requests,
            (trace.state group.time).HasRoot request.val) ∧
        schedule.comparisonRotationCount =
          trace.rotationCount := by
  let initialization :=
    Canonical.canonicalInitialization
      (Snapshot.ofTree trace.initialTree) initialSplayTree params
      growingLimit valueBound
  obtain
      ⟨groups, finalSplayTree, schedule, ⟨transition⟩,
        requestsEq, ordered, rooted, comparisonCount⟩ :=
    exists_realizedNormalFormSchedule
      splayRealizer comparisonRealizer trace initialSplayTree
      initialization.final_represents
  let initialized :
      InitializedTransition params
        (Snapshot.ofTree trace.initialTree) initialSplayTree
        (Snapshot.ofTree trace.finalTree) finalSplayTree :=
    { initialization := initialization
      transition := transition }
  exact
    ⟨groups, finalSplayTree, schedule, ⟨initialized⟩,
      requestsEq, ordered, rooted, comparisonCount⟩

end Splay.Assumptions.NormalForm.ComparisonTrace
