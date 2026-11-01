import Splay.Accounting.CostSensitiveProductiveSchedule
import Splay.Lazy.AtomicInitializationCost

namespace Splay.Accounting

open Assumptions.NormalForm
open Assumptions.NormalForm.ComparisonTrace
open Splay.Rank
open Splay.Tree.BST

/-- The productive-efficient canonical initializer has exact cost `4 * n`. -/
theorem productiveEvents_atomicInitialization
    {n : ℕ} (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    productiveEvents
        (Lazy.eraseOperations
          (Lazy.Canonical.atomicInitialization snapshot tree params
            growingLimit valueBound).events) =
      4 * n := by
  unfold productiveEvents
  rw [Lazy.Canonical.atomicInitialization_totalInserts,
    Lazy.Canonical.atomicInitialization_totalIncreases]
  omega

/--
The exact initializer count fits the cost-sensitive schedule format with
coefficient four at every height.
-/
theorem productiveEvents_atomicInitialization_le
    {n : ℕ} (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound)
    (height : ℕ) :
    productiveEvents
        (Lazy.eraseOperations
          (Lazy.Canonical.atomicInitialization snapshot tree params
            growingLimit valueBound).events) ≤
      4 * n * gapLog height := by
  rw [productiveEvents_atomicInitialization]
  have logOne : 1 ≤ gapLog height :=
    gapLog_pos height
  nlinarith

end Splay.Accounting

namespace Splay.Assumptions.NormalForm.ComparisonTrace.Schedule

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

namespace InitializedTransitionProvenance

/--
The schedule-provenance constructor using the productive-efficient atomic
initializer.  The transition suffix is the same exact recursively decomposed
schedule realizer as in `exists_complete`.
-/
theorem exists_complete_atomic
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {trace : ComparisonTrace n accesses}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {beforeTree afterTree : Tree.BST 0 n}
    (schedule :
      Schedule trace groups time beforeTree afterTree)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap
          (Snapshot.ofTree (trace.state time)).maxRank ≤
        params.valueBound) :
    Nonempty
      { result :
          Σ execution :
            InitializedTransition params
              (Snapshot.ofTree (trace.state time)) beforeTree
              (Snapshot.ofTree trace.finalTree) afterTree,
          InitializedTransitionProvenance schedule execution //
        Splay.Accounting.productiveEvents
            (eraseOperations result.1.initialization.events) =
          4 * n } := by
  let initialization :=
    Canonical.atomicInitialization
      (Snapshot.ofTree (trace.state time)) beforeTree params
      growingLimit valueBound
  obtain ⟨⟨transition, provenance⟩⟩ :=
    RepresentedTransitionProvenance.exists_complete
      schedule initialization.final_represents
  let execution :
      InitializedTransition params
        (Snapshot.ofTree (trace.state time)) beforeTree
        (Snapshot.ofTree trace.finalTree) afterTree :=
    { initialization := initialization
      transition := transition }
  refine
    ⟨⟨⟨execution,
      { transitionProvenance := provenance }⟩, ?_⟩⟩
  change
    Splay.Accounting.productiveEvents
        (eraseOperations
          (Canonical.atomicInitialization
            (Snapshot.ofTree (trace.state time)) beforeTree params
            growingLimit valueBound).events) =
      4 * n
  exact
    Splay.Accounting.productiveEvents_atomicInitialization
      (Snapshot.ofTree (trace.state time)) beforeTree params
      growingLimit valueBound

end InitializedTransitionProvenance

end Splay.Assumptions.NormalForm.ComparisonTrace.Schedule

namespace Splay.Accounting

open Assumptions.NormalForm
open Assumptions.NormalForm.ComparisonTrace
open Splay.Rank
open Splay.Tree.BST

namespace ProvenancedInitializedRealizedNormalFormSchedule

/--
Normal-form realization whose exact initialization prefix is the atomic
`4 * n` construction.
-/
structure AtomicWitness
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : ComparisonTrace n accesses}
    (provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison) : Prop where
  initialization_productive_eq :
    productiveEvents
        (Lazy.eraseOperations
          provenanced.realized.execution.initialization.events) =
      4 * n

/--
Every complete comparison trace has a provenanced realization with the exact
atomic initialization count.
-/
theorem exists_atomic_of_complete
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    (comparison : ComparisonTrace n accesses)
    (initialTree : Tree.BST 0 n)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap
          (Snapshot.ofTree comparison.initialTree).maxRank ≤
        params.valueBound) :
    Nonempty
      { provenanced :
          ProvenancedInitializedRealizedNormalFormSchedule
            params initialTree comparison //
        AtomicWitness provenanced } := by
  obtain
      ⟨groups, finalSplayTree, schedule,
        requestsEq, ordered, serves, comparisonCount⟩ :=
    comparison.exists_normalFormSchedule initialTree
  have valueAtZero :
      Analysis.contractedGap
          (Snapshot.ofTree (comparison.state 0)).maxRank ≤
        params.valueBound := by
    simpa [ComparisonTrace.initialTree] using valueBound
  obtain ⟨⟨⟨execution, provenance⟩, initializationEq⟩⟩ :=
    Schedule.InitializedTransitionProvenance.exists_complete_atomic
      schedule growingLimit valueAtZero
  let realized :
      InitializedRealizedNormalFormSchedule
        params initialTree comparison :=
    { groups := groups
      finalSplayTree := finalSplayTree
      schedule := schedule
      execution := execution
      requests_eq := requestsEq
      groups_ordered := ordered
      comparison_serves := serves
      comparisonRotationCount_eq := comparisonCount }
  let provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison :=
    { realized := realized
      provenance := provenance }
  exact
    ⟨⟨provenanced,
      ⟨by
        simpa [provenanced, realized] using initializationEq⟩⟩⟩

namespace AtomicWitness

/-- Atomic initialization supplies the initialization field of cost provenance. -/
theorem initialization_le
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : ComparisonTrace n accesses}
    {provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison}
    (atomic : AtomicWitness provenanced)
    (height : ℕ) :
    productiveEvents
        (Lazy.eraseOperations
          provenanced.realized.execution.initialization.events) ≤
      4 * n * gapLog height := by
  rw [atomic.initialization_productive_eq]
  have logOne : 1 ≤ gapLog height :=
    gapLog_pos height
  nlinarith

/--
Once the recursively authenticated local transition cost is available,
atomic initialization completes coefficient-four productive provenance.
-/
def toCostSensitiveProductiveProvenance
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : ComparisonTrace n accesses}
    {provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison}
    (atomic : AtomicWitness provenanced)
    (height : ℕ)
    (transition :
      ScheduleProductiveCost.Holds 4 height
        provenanced.provenance.transitionProvenance) :
    CostSensitiveProductiveProvenance
      provenanced 4 height :=
  { initialization_le := atomic.initialization_le height
    transition := transition }

end AtomicWitness

end ProvenancedInitializedRealizedNormalFormSchedule

end Splay.Accounting
