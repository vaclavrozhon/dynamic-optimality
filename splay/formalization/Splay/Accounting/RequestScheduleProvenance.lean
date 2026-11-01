import Splay.Accounting.SplayRequestProvenance
import Splay.Accounting.ScheduleExecutionProvenance

namespace Splay.Assumptions.NormalForm.ComparisonTrace.Schedule

open Splay.Lazy Splay.Rank Splay.Tree.BST

/-- Exact schedule decomposition retaining whole-request event windows. -/
inductive RequestTransitionProvenance
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {trace : ComparisonTrace n accesses} :
    {groups : List (RequestGroup trace)} →
      {time : Fin (trace.rotationCount + 1)} →
      {beforeTree afterTree : Tree.BST 0 n} →
      (schedule :
        Schedule trace groups time beforeTree afterTree) →
      {initial : State n} →
      (execution :
        RepresentedTransition params
          (Snapshot.ofTree (trace.state time)) beforeTree
          (Snapshot.ofTree trace.finalTree) afterTree initial) →
      Type
  | finish
      {time : Fin (trace.rotationCount + 1)}
      (tree : Tree.BST 0 n)
      (comparison :
        RotationExecution
          (trace.rotationCount - time.val)
          (trace.state time) trace.finalTree)
      {initial : State n}
      (comparisonTransition :
        RepresentedTransition params
          (Snapshot.ofTree (trace.state time)) tree
          (Snapshot.ofTree trace.finalTree) tree initial)
      (comparisonProvenance :
        RotationExecution.RepresentedComparisonTransitionProvenance
          tree comparison comparisonTransition) :
      RequestTransitionProvenance
        (.finish tree comparison) comparisonTransition
  | next
      {group : RequestGroup trace}
      {groups : List (RequestGroup trace)}
      {time : Fin (trace.rotationCount + 1)}
      {beforeTree middleTree afterTree : Tree.BST 0 n}
      (ordered : time ≤ group.time)
      (comparison :
        RotationExecution
          (group.time.val - time.val)
          (trace.state time) (trace.state group.time))
      (splay :
        SplaySequence group.requests beforeTree middleTree)
      (tail :
        Schedule trace groups group.time middleTree afterTree)
      {initial : State n}
      (comparisonTransition :
        RepresentedTransition params
          (Snapshot.ofTree (trace.state time)) beforeTree
          (Snapshot.ofTree (trace.state group.time)) beforeTree
          initial)
      (comparisonProvenance :
        RotationExecution.RepresentedComparisonTransitionProvenance
          beforeTree comparison comparisonTransition)
      (splayTransition :
        RepresentedTransition params
          (Snapshot.ofTree (trace.state group.time)) beforeTree
          (Snapshot.ofTree (trace.state group.time)) middleTree
          comparisonTransition.final)
      (splayProvenance :
        SplaySequence.RequestTransitionProvenance
          splay splayTransition)
      (tailTransition :
        RepresentedTransition params
          (Snapshot.ofTree (trace.state group.time)) middleTree
          (Snapshot.ofTree trace.finalTree) afterTree
          splayTransition.final)
      (tailProvenance :
        RequestTransitionProvenance tail tailTransition) :
      RequestTransitionProvenance
        (.next ordered comparison splay tail)
        ((comparisonTransition.trans splayTransition).trans
          tailTransition)

/-- Forget the finer splay-step decomposition of an existing schedule while
retaining its exact comparison macros and event lists. -/
noncomputable def RepresentedTransitionProvenance.toRequest
    {n : ℕ} {accesses : List (Fin n)} {params : Interface.Parameters}
    {trace : ComparisonTrace n accesses} {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)} {before after : Tree.BST 0 n}
    {schedule : Schedule trace groups time before after} {initial : State n}
    {transition : RepresentedTransition params
      (Snapshot.ofTree (trace.state time)) before (Snapshot.ofTree trace.finalTree) after initial}
    (provenance : RepresentedTransitionProvenance schedule transition) :
    RequestTransitionProvenance schedule transition := by
  induction provenance with
  | finish tree comparison transition comparisonProvenance =>
      exact .finish tree comparison transition comparisonProvenance
  | next ordered comparison splay tail comparisonTransition comparisonProvenance
      splayTransition splayProvenance tailTransition _ ih =>
      exact .next ordered comparison splay tail comparisonTransition comparisonProvenance
        splayTransition splayProvenance.toRequest tailTransition ih

namespace RequestTransitionProvenance

/--
Complete request macros and comparison rotation macros compose in the
chronological schedule, including its final comparison-only suffix.
-/
theorem exists_of_realizers
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {trace : ComparisonTrace n accesses}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {beforeTree afterTree : Tree.BST 0 n}
    (comparisonRealizer : ∀ tree : Tree.BST 0 n,
      ComparisonRotationTraceRealizer params tree)
    (requestRealizer : ∀ snapshot : Snapshot n,
      SplayRequestTraceRealizer params snapshot)
    (schedule :
      Schedule trace groups time beforeTree afterTree)
    {initial : State n}
    (initialRepresents :
      initial.Represents params
        (Snapshot.ofTree (trace.state time)) beforeTree) :
    Nonempty
      (Σ execution :
          RepresentedTransition params
            (Snapshot.ofTree (trace.state time)) beforeTree
            (Snapshot.ofTree trace.finalTree) afterTree initial,
        RequestTransitionProvenance schedule execution) := by
  induction schedule generalizing initial with
  | @finish finishTime tree comparison =>
      obtain ⟨⟨comparisonTransition, comparisonProvenance⟩⟩ :=
        RotationExecution.RepresentedComparisonTransitionProvenance.exists_of_realizer
          (comparisonRealizer _) comparison initialRepresents
      exact
        ⟨⟨comparisonTransition,
          .finish tree comparison comparisonTransition
            comparisonProvenance⟩⟩
  | @next group groups startTime before middle after
      ordered comparison splay tail ih =>
      obtain ⟨⟨comparisonTransition, comparisonProvenance⟩⟩ :=
        RotationExecution.RepresentedComparisonTransitionProvenance.exists_of_realizer
          (comparisonRealizer _) comparison initialRepresents
      obtain ⟨⟨splayTransition, splayProvenance⟩⟩ :=
        SplaySequence.RequestTransitionProvenance.exists_of_realizer
          (requestRealizer _) splay comparisonTransition.final_represents
      obtain ⟨⟨tailTransition, tailProvenance⟩⟩ :=
        ih splayTransition.final_represents
      exact
        ⟨⟨(comparisonTransition.trans splayTransition).trans
              tailTransition,
          .next ordered comparison splay tail
            comparisonTransition comparisonProvenance
            splayTransition splayProvenance
            tailTransition tailProvenance⟩⟩

end RequestTransitionProvenance

end Splay.Assumptions.NormalForm.ComparisonTrace.Schedule
