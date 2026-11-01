import Splay.Lazy.AtomicRealizersComplete

namespace Splay.Assumptions.NormalForm.ComparisonTrace.Schedule

open Splay.Lazy
open Splay.Rank

/--
Every chronological normal-form schedule has a rich represented execution.
The structural atomicizer and comparison root-swap construction discharge
both local realizer arguments of `existsRepresentedTransition`.
-/
theorem existsRepresentedTransition_complete
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
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
        (Snapshot.ofTree trace.finalTree) afterTree initial) :=
  schedule.existsRepresentedTransition
    (rootedSplayTraceRealizer params)
    (comparisonRotationTraceRealizer params)
    initialRepresents

end Splay.Assumptions.NormalForm.ComparisonTrace.Schedule

namespace Splay.Assumptions.NormalForm.ComparisonTrace

open Splay.Lazy
open Splay.Rank

/--
Every comparison trace and initial splay tree carry a chronological
normal-form schedule together with its complete rich execution.
-/
theorem exists_realizedNormalFormSchedule_complete
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
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
          trace.rotationCount :=
  exists_realizedNormalFormSchedule
    (rootedSplayTraceRealizer params)
    (comparisonRotationTraceRealizer params)
    trace initialSplayTree initialRepresents

/--
Every comparison trace has a fully initialized chronological rich execution,
provided only the concrete canonical-initialization bounds.
-/
theorem exists_initializedRealizedNormalFormSchedule_complete
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
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
          trace.rotationCount :=
  exists_initializedRealizedNormalFormSchedule
    (rootedSplayTraceRealizer params)
    (comparisonRotationTraceRealizer params)
    trace initialSplayTree growingLimit valueBound

end Splay.Assumptions.NormalForm.ComparisonTrace
