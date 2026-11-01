import Splay.Accounting.AtomicProductiveInitialization
import Splay.Accounting.ProductiveFreeSplayProvenance
import Splay.Accounting.UnitProductiveComparisonProvenance

namespace Splay.Accounting

open Assumptions.NormalForm
open Assumptions.NormalForm.ComparisonTrace
open Splay.Rank
open Splay.Tree.BST

/--
A costed comparison execution has productive cost at most
`4 * length * gapLog`.  The concrete construction is actually bounded by
`2 * length`; coefficient four is shared with atomic initialization.
-/
theorem productiveEvents_le_four_mul_rotationLength
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    {length : ℕ}
    {beforeComparison afterComparison : Tree.BST 0 n}
    {execution :
      RotationExecution length beforeComparison afterComparison}
    {initial : Lazy.State n}
    (costed :
      RotationExecution.UnitProductiveComparisonProvenance
        (params := params) splayTree execution initial)
    (height : ℕ) :
    productiveEvents
        (Lazy.eraseOperations costed.transition.events) ≤
      4 * length * gapLog height := by
  have localBound :
      productiveEvents
          (Lazy.eraseOperations costed.transition.events) ≤
        2 * length := by
    unfold productiveEvents
    calc
      Interface.totalInserts
            (Lazy.eraseOperations costed.transition.events) +
          Interface.totalIncreases
            (Lazy.eraseOperations costed.transition.events) ≤
          length + length :=
        Nat.add_le_add costed.totalInserts_le costed.totalIncreases_le
      _ = 2 * length := by omega
  have logOne : 1 ≤ gapLog height :=
    gapLog_pos height
  calc
    productiveEvents
        (Lazy.eraseOperations costed.transition.events) ≤
      2 * length :=
        localBound
    _ ≤ 4 * length * gapLog height := by
      nlinarith

/-- Productive-free rich transitions have zero productive-event count. -/
theorem productiveEvents_eq_zero_of_productiveFree
    {n : ℕ} {params : Interface.Parameters}
    {beforeSnapshot afterSnapshot : Snapshot n}
    {beforeTree afterTree : Tree.BST 0 n}
    {initial : Lazy.State n}
    (free :
      Lazy.ProductiveFreeRepresentedTransition params
        beforeSnapshot beforeTree afterSnapshot afterTree initial) :
    productiveEvents
        (Lazy.eraseOperations free.transition.events) = 0 := by
  unfold productiveEvents
  rw [free.totalInserts_eq_zero, free.totalIncreases_eq_zero]

end Splay.Accounting

namespace Splay.Assumptions.NormalForm.ComparisonTrace.Schedule

open Splay.Accounting
open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

/--
An exact schedule transition, its ordinary standard provenance, and the
fully discharged coefficient-four productive-cost recursion.
-/
structure ConcreteCostedTransition
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {trace : ComparisonTrace n accesses}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {beforeTree afterTree : Tree.BST 0 n}
    (schedule :
      Schedule trace groups time beforeTree afterTree)
    (initial : State n) (height : ℕ) where
  transition :
    RepresentedTransition params
      (Snapshot.ofTree (trace.state time)) beforeTree
      (Snapshot.ofTree trace.finalTree) afterTree initial
  provenance :
    RepresentedTransitionProvenance schedule transition
  productiveCost :
    ScheduleProductiveCost.Holds 4 height provenance

namespace ConcreteCostedTransition

/--
Concrete comparison and splay realizers recursively construct a costed exact
transition for every normal-form schedule.
-/
theorem exists_complete
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
        (Snapshot.ofTree (trace.state time)) beforeTree)
    (height : ℕ) :
    Nonempty
      (ConcreteCostedTransition
        (params := params) schedule initial height) := by
  induction schedule generalizing initial with
  | @finish finishTime tree comparison =>
      obtain ⟨comparisonCosted⟩ :=
        RotationExecution.UnitProductiveComparisonProvenance.exists_complete
          comparison initialRepresents
      let provenance :
          RepresentedTransitionProvenance
            (.finish tree comparison) comparisonCosted.transition :=
        .finish tree comparison comparisonCosted.transition
          comparisonCosted.provenance
      have comparisonBound :
          productiveEvents
              (eraseOperations comparisonCosted.transition.events) ≤
            4 * (trace.rotationCount - finishTime.val) *
              gapLog height :=
        productiveEvents_le_four_mul_rotationLength
          comparisonCosted height
      exact
        ⟨{
          transition := comparisonCosted.transition
          provenance := provenance
          productiveCost := by
            exact comparisonBound
        }⟩
  | @next group groups startTime before middle after
      ordered comparison splay tail ih =>
      obtain ⟨comparisonCosted⟩ :=
        RotationExecution.UnitProductiveComparisonProvenance.exists_complete
          comparison initialRepresents
      obtain ⟨splayCosted⟩ :=
        SplaySequence.ProductiveFreeProvenance.exists_complete
          splay comparisonCosted.transition.final_represents
      obtain ⟨tailCosted⟩ :=
        ih splayCosted.realized.transition.final_represents
      let transition :=
        (comparisonCosted.transition.trans
          splayCosted.realized.transition).trans
            tailCosted.transition
      let provenance :
          RepresentedTransitionProvenance
            (.next ordered comparison splay tail) transition :=
        .next ordered comparison splay tail
          comparisonCosted.transition comparisonCosted.provenance
          splayCosted.realized.transition splayCosted.provenance
          tailCosted.transition tailCosted.provenance
      have comparisonBound :
          productiveEvents
              (eraseOperations comparisonCosted.transition.events) ≤
            4 * (group.time.val - startTime.val) *
              gapLog height :=
        productiveEvents_le_four_mul_rotationLength
          comparisonCosted height
      have splayZero :
          productiveEvents
              (eraseOperations
                splayCosted.realized.transition.events) = 0 :=
        productiveEvents_eq_zero_of_productiveFree
          splayCosted.realized
      exact
        ⟨{
          transition := transition
          provenance := provenance
          productiveCost := by
            refine ⟨?_, splayZero, tailCosted.productiveCost⟩
            simpa [Schedule.comparisonRotationCount] using
              comparisonBound
        }⟩

end ConcreteCostedTransition

/--
Atomic initialization followed by the concrete costed schedule transition.
-/
structure ConcreteCostedInitializedTransition
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {trace : ComparisonTrace n accesses}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {beforeTree afterTree : Tree.BST 0 n}
    (schedule :
      Schedule trace groups time beforeTree afterTree)
    (height : ℕ) where
  execution :
    InitializedTransition params
      (Snapshot.ofTree (trace.state time)) beforeTree
      (Snapshot.ofTree trace.finalTree) afterTree
  provenance :
    InitializedTransitionProvenance schedule execution
  initialization_productive_eq :
    productiveEvents
        (eraseOperations execution.initialization.events) =
      4 * n
  transitionCost :
    ScheduleProductiveCost.Holds 4 height
      provenance.transitionProvenance

namespace ConcreteCostedInitializedTransition

theorem exists_complete
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
        params.valueBound)
    (height : ℕ) :
    Nonempty
      (ConcreteCostedInitializedTransition
        (params := params) schedule height) := by
  let initialization :=
    Canonical.atomicInitialization
      (Snapshot.ofTree (trace.state time)) beforeTree params
      growingLimit valueBound
  obtain ⟨costedTransition⟩ :=
    ConcreteCostedTransition.exists_complete schedule
      initialization.final_represents height
  let execution :
      InitializedTransition params
        (Snapshot.ofTree (trace.state time)) beforeTree
        (Snapshot.ofTree trace.finalTree) afterTree :=
    { initialization := initialization
      transition := costedTransition.transition }
  let provenance :
      InitializedTransitionProvenance schedule execution :=
    { transitionProvenance := costedTransition.provenance }
  exact
    ⟨{
      execution := execution
      provenance := provenance
      initialization_productive_eq := by
        exact
          productiveEvents_atomicInitialization
            (Snapshot.ofTree (trace.state time)) beforeTree params
            growingLimit valueBound
      transitionCost := costedTransition.productiveCost
    }⟩

end ConcreteCostedInitializedTransition

end Splay.Assumptions.NormalForm.ComparisonTrace.Schedule

namespace Splay.Accounting

open Assumptions.NormalForm
open Assumptions.NormalForm.ComparisonTrace
open Splay.Rank
open Splay.Tree.BST

namespace ProvenancedInitializedRealizedNormalFormSchedule

/--
An assumption-free normal-form realization carrying fully proved
coefficient-four productive provenance.
-/
structure ConcreteCostSensitiveRealization
    {n : ℕ} {accesses : List (Fin n)}
    (params : Interface.Parameters)
    (initialTree : Tree.BST 0 n)
    (comparison : ComparisonTrace n accesses)
    (height : ℕ) where
  provenanced :
    ProvenancedInitializedRealizedNormalFormSchedule
      params initialTree comparison
  productive :
    CostSensitiveProductiveProvenance provenanced 4 height

namespace ConcreteCostSensitiveRealization

/--
Every complete comparison trace admits an exact normal-form realization with
global productive-event cost

`4 * (n + comparisonRotationCount) * gapLog height`.
-/
theorem exists_of_complete
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    (comparison : ComparisonTrace n accesses)
    (initialTree : Tree.BST 0 n)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap
          (Snapshot.ofTree comparison.initialTree).maxRank ≤
        params.valueBound)
    (height : ℕ) :
    Nonempty
      (ConcreteCostSensitiveRealization
        params initialTree comparison height) := by
  obtain
      ⟨groups, finalSplayTree, schedule,
        requestsEq, ordered, serves, comparisonCount⟩ :=
    comparison.exists_normalFormSchedule initialTree
  have valueAtZero :
      Analysis.contractedGap
          (Snapshot.ofTree (comparison.state 0)).maxRank ≤
        params.valueBound := by
    simpa [ComparisonTrace.initialTree] using valueBound
  obtain ⟨costed⟩ :=
    Schedule.ConcreteCostedInitializedTransition.exists_complete
      schedule growingLimit valueAtZero height
  let realized :
      InitializedRealizedNormalFormSchedule
        params initialTree comparison :=
    { groups := groups
      finalSplayTree := finalSplayTree
      schedule := schedule
      execution := costed.execution
      requests_eq := requestsEq
      groups_ordered := ordered
      comparison_serves := serves
      comparisonRotationCount_eq := comparisonCount }
  let provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison :=
    { realized := realized
      provenance := costed.provenance }
  have initializationBound :
      productiveEvents
          (Lazy.eraseOperations
            provenanced.realized.execution.initialization.events) ≤
        4 * n * gapLog height := by
    rw [show
      productiveEvents
          (Lazy.eraseOperations
            provenanced.realized.execution.initialization.events) =
        4 * n by
      simpa [provenanced, realized] using
        costed.initialization_productive_eq]
    have logOne : 1 ≤ gapLog height :=
      gapLog_pos height
    nlinarith
  exact
    ⟨{
      provenanced := provenanced
      productive :=
        { initialization_le := initializationBound
          transition := by
            simpa [provenanced, realized] using
              costed.transitionCost }
    }⟩

/-- The concrete realization's exact initialized event list obeys the global bound. -/
theorem productiveEvents_le
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : ComparisonTrace n accesses}
    {height : ℕ}
    (realization :
      ConcreteCostSensitiveRealization
        params initialTree comparison height) :
    productiveEvents
        (Lazy.eraseOperations
          realization.provenanced.realized.execution.events) ≤
      4 *
        (n +
          realization.provenanced.realized.schedule.comparisonRotationCount) *
        gapLog height :=
  realization.productive.productiveEvents_le

/--
The concrete realization closes the semantic productive-event envelopes:
all productive events are charged to the paid class, and the unimportant
class is empty.
-/
def toSemanticProductiveCharge
    {constants : TranslationConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : ComparisonTrace n accesses}
    {height nearCost : ℕ}
    (realization :
      ConcreteCostSensitiveRealization
        params initialTree comparison height)
    (four_le_paid : 4 ≤ constants.semantic.paid)
    (comparisonCost_le : comparison.cost ≤ nearCost) :
    realization.provenanced.SemanticProductiveCharge
      constants nearCost height :=
  realization.productive.toSemanticProductiveCharge
    four_le_paid comparisonCost_le

/--
Consequently the concrete realization supplies the complete witnessed
potential residue consumed by the global accounting reduction.
-/
def toWitnessedEnvelopePotentialResidue
    {constants : TranslationConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : ComparisonTrace n accesses}
    {height nearCost : ℕ}
    (realization :
      ConcreteCostSensitiveRealization
        params initialTree comparison height)
    (four_le_paid : 4 ≤ constants.semantic.paid)
    (comparisonCost_le : comparison.cost ≤ nearCost)
    (valueBound_le : params.valueBound ≤ gapBound height) :
    WitnessedEnvelopePotentialResidue constants params
      (Lazy.eraseOperations
        realization.provenanced.realized.execution.events)
      nearCost height :=
  realization.productive.toWitnessedEnvelopePotentialResidue
    four_le_paid comparisonCost_le valueBound_le

end ConcreteCostSensitiveRealization

end ProvenancedInitializedRealizedNormalFormSchedule

end Splay.Accounting
