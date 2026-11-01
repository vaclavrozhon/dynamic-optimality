import Splay.Accounting.RealizedWitnessedThreeLaw
import Splay.Accounting.SplayExecutionProvenance

namespace Splay.Assumptions.NormalForm.ComparisonTrace.Schedule

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

/--
Proof-relevant provenance connecting one concrete normal-form schedule to the
exact represented transition assembled from its pieces.

The output transition is an index of this type.  In the `next` constructor it
is definitionally

`(comparisonTransition.trans splayTransition).trans tailTransition`.

Thus the witness retains the decomposition that `RepresentedTransition`
itself intentionally erases.
-/
inductive RepresentedTransitionProvenance
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
      RepresentedTransitionProvenance
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
        SplaySequence.RepresentedTransitionProvenance
          splay splayTransition)
      (tailTransition :
        RepresentedTransition params
          (Snapshot.ofTree (trace.state group.time)) middleTree
          (Snapshot.ofTree trace.finalTree) afterTree
          splayTransition.final)
      (tailProvenance :
        RepresentedTransitionProvenance tail tailTransition) :
      RepresentedTransitionProvenance
        (.next ordered comparison splay tail)
        ((comparisonTransition.trans splayTransition).trans
          tailTransition)

namespace RepresentedTransitionProvenance

/--
Unconditional complete realizers produce a transition together with its exact
schedule decomposition.
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
        (Snapshot.ofTree (trace.state time)) beforeTree) :
    Nonempty
      (Σ execution :
          RepresentedTransition params
            (Snapshot.ofTree (trace.state time)) beforeTree
            (Snapshot.ofTree trace.finalTree) afterTree initial,
        RepresentedTransitionProvenance schedule execution) := by
  induction schedule generalizing initial with
  | @finish finishTime tree comparison =>
      obtain ⟨⟨comparisonTransition, comparisonProvenance⟩⟩ :=
        RotationExecution.RepresentedComparisonTransitionProvenance.exists_complete
          comparison initialRepresents
      exact
        ⟨⟨comparisonTransition,
          .finish tree comparison comparisonTransition
            comparisonProvenance⟩⟩
  | @next group groups startTime before middle after
      ordered comparison splay tail ih =>
      obtain ⟨⟨comparisonTransition, comparisonProvenance⟩⟩ :=
        RotationExecution.RepresentedComparisonTransitionProvenance.exists_complete
          comparison initialRepresents
      obtain ⟨⟨splayTransition, splayProvenance⟩⟩ :=
        SplaySequence.RepresentedTransitionProvenance.exists_complete
          splay comparisonTransition.final_represents
      obtain ⟨⟨tailTransition, tailProvenance⟩⟩ :=
        ih splayTransition.final_represents
      exact
        ⟨⟨(comparisonTransition.trans splayTransition).trans
              tailTransition,
          .next ordered comparison splay tail
            comparisonTransition comparisonProvenance
            splayTransition splayProvenance
            tailTransition tailProvenance⟩⟩

end RepresentedTransitionProvenance

/--
Initialized provenance packages the canonical initialization prefix together
with proof-relevant provenance for its represented transition suffix.
-/
structure InitializedTransitionProvenance
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {trace : ComparisonTrace n accesses}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {beforeTree afterTree : Tree.BST 0 n}
    (schedule :
      Schedule trace groups time beforeTree afterTree)
    (execution :
      InitializedTransition params
        (Snapshot.ofTree (trace.state time)) beforeTree
        (Snapshot.ofTree trace.finalTree) afterTree) : Type where
  transitionProvenance :
    RepresentedTransitionProvenance
      schedule execution.transition

namespace InitializedTransitionProvenance

/--
Canonical initialization plus the unconditional schedule realizer yields an
initialized transition with retained compositional provenance.
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
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap
          (Snapshot.ofTree (trace.state time)).maxRank ≤
        params.valueBound) :
    Nonempty
      (Σ execution :
          InitializedTransition params
            (Snapshot.ofTree (trace.state time)) beforeTree
            (Snapshot.ofTree trace.finalTree) afterTree,
        InitializedTransitionProvenance schedule execution) := by
  let initialization :=
    Canonical.canonicalInitialization
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
  exact
    ⟨⟨execution,
      { transitionProvenance := provenance }⟩⟩

end InitializedTransitionProvenance

end Splay.Assumptions.NormalForm.ComparisonTrace.Schedule

namespace Splay.Accounting

open Splay.Assumptions.NormalForm
open Splay.Assumptions.NormalForm.ComparisonTrace
open Splay.Rank
open Splay.Tree.BST

/--
The existing realized normal-form package, strengthened by proof-relevant
evidence that its exact transition is the recursive composition of its exact
schedule.
-/
structure ProvenancedInitializedRealizedNormalFormSchedule
    {n : ℕ} {accesses : List (Fin n)}
    (params : Interface.Parameters)
    (initialTree : Tree.BST 0 n)
    (comparison : ComparisonTrace n accesses) where
  realized :
    InitializedRealizedNormalFormSchedule
      params initialTree comparison
  provenance :
    Schedule.InitializedTransitionProvenance
      realized.schedule realized.execution

namespace ProvenancedInitializedRealizedNormalFormSchedule

/--
Every normal-form schedule obtained from the comparison trace admits a
canonical initialized rich execution with retained schedule provenance.
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
        params.valueBound) :
    Nonempty
      (ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison) := by
  obtain
      ⟨groups, finalSplayTree, schedule,
        requestsEq, ordered, serves, comparisonCount⟩ :=
    comparison.exists_normalFormSchedule initialTree
  have valueAtZero :
      Analysis.contractedGap
          (Snapshot.ofTree (comparison.state 0)).maxRank ≤
        params.valueBound := by
    simpa [ComparisonTrace.initialTree] using valueBound
  obtain ⟨⟨execution, provenance⟩⟩ :=
    Schedule.InitializedTransitionProvenance.exists_complete
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
  exact
    ⟨{ realized := realized
       provenance := provenance }⟩

end ProvenancedInitializedRealizedNormalFormSchedule

/--
Strictest current three-law witness: the accounting certificate uses the
exact events of an initialized transition, and this additional field retains
the recursive proof that the transition was assembled from the exact packaged
normal-form schedule.
-/
structure ProvenancedRealizedWitnessedThreeLawCertificate
    (constants : TranslationConstants)
    (bendConstants : BendConstants)
    (shape : Interface.Shape)
    (insertConstant valueChangeConstant : ℕ)
    (n nearCost height : ℕ)
    (initialTree : Tree.BST 0 n) (accesses : List (Fin n))
    (comparison : ComparisonTrace n accesses) where
  certificate :
    RealizedWitnessedThreeLawCertificate
      constants bendConstants shape
      insertConstant valueChangeConstant
      n nearCost height initialTree accesses comparison
  provenance :
    Schedule.InitializedTransitionProvenance
      certificate.realized.schedule
      certificate.realized.execution

namespace ProvenancedRealizedWitnessedThreeLawCertificate

/-- Forget only recursive execution provenance. -/
def toRealized
    {constants : TranslationConstants}
    {bendConstants : BendConstants}
    {shape : Interface.Shape}
    {insertConstant valueChangeConstant : ℕ}
    {n nearCost height : ℕ}
    {initialTree : Tree.BST 0 n} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses}
    (certificate :
      ProvenancedRealizedWitnessedThreeLawCertificate
        constants bendConstants shape
        insertConstant valueChangeConstant
        n nearCost height initialTree accesses comparison) :
    RealizedWitnessedThreeLawCertificate
      constants bendConstants shape
      insertConstant valueChangeConstant
      n nearCost height initialTree accesses comparison :=
  certificate.certificate

/-- Forget provenance and the explicit schedule to recover the old witness. -/
noncomputable def toWitnessed
    {constants : TranslationConstants}
    {bendConstants : BendConstants}
    {shape : Interface.Shape}
    {insertConstant valueChangeConstant : ℕ}
    {n nearCost height : ℕ}
    {initialTree : Tree.BST 0 n} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses}
    (certificate :
      ProvenancedRealizedWitnessedThreeLawCertificate
        constants bendConstants shape
        insertConstant valueChangeConstant
        n nearCost height initialTree accesses comparison) :
    WitnessedThreeLawCertificate
      constants bendConstants shape
      insertConstant valueChangeConstant
      n nearCost height initialTree accesses comparison :=
  certificate.certificate.toWitnessed

end ProvenancedRealizedWitnessedThreeLawCertificate

/--
Uniform version of the schedule-provenanced witnessed translation premise.
All count and envelope premises are unchanged.
-/
def ProvenancedRealizedWitnessedThreeLawTranslationHypothesis
    (comparisonProfile : ComparisonProfile)
    (shape : Interface.Shape) : Prop :=
  ∀ (insertConstant valueChangeConstant : ℕ),
    0 < insertConstant →
    0 < valueChangeConstant →
    ∃ (constants : TranslationConstants)
        (bendConstants : BendConstants),
      PotentialCoefficientDominance constants
          insertConstant valueChangeConstant ∧
        ∀ (n : ℕ), 0 < n →
          ∀ (initialTree : Tree.BST 0 n)
            (accesses : List (Fin n)),
            ∃ comparison : ComparisonTrace n accesses,
              Nonempty
                (ProvenancedRealizedWitnessedThreeLawCertificate
                  constants bendConstants shape
                  insertConstant valueChangeConstant
                  n (comparisonProfile.cost accesses)
                  (comparisonProfile.maxHeight accesses)
                  initialTree accesses comparison)

/-- Forget schedule provenance and recover the schedule-tied hypothesis. -/
theorem realizedWitnessedThreeLawTranslationHypothesis_of_provenanced
    {comparisonProfile : ComparisonProfile}
    {shape : Interface.Shape}
    (provenanced :
      ProvenancedRealizedWitnessedThreeLawTranslationHypothesis
        comparisonProfile shape) :
    RealizedWitnessedThreeLawTranslationHypothesis
      comparisonProfile shape := by
  intro insertConstant valueChangeConstant
    insertPositive valueChangePositive
  obtain ⟨constants, bendConstants, dominance, certificates⟩ :=
    provenanced insertConstant valueChangeConstant
      insertPositive valueChangePositive
  refine ⟨constants, bendConstants, dominance, ?_⟩
  intro n nPositive initialTree accesses
  obtain ⟨comparison, ⟨certificate⟩⟩ :=
    certificates n nPositive initialTree accesses
  exact ⟨comparison, ⟨certificate.toRealized⟩⟩

/--
Endpoint with no remaining schedule/execution provenance gap.
-/
theorem targetBound_of_offlineNormalForm_and_provenancedRealizedTranslation
    (normalForm :
      Assumptions.NormalForm.Hypothesis OfflineOptimum.concreteOfflineCostModel)
    (shape : Interface.Shape)
    (translation :
      ProvenancedRealizedWitnessedThreeLawTranslationHypothesis
        normalForm.realize.comparisonProfile shape) :
    TargetBound OfflineOptimum.concreteOfflineCostModel :=
  targetBound_of_offlineNormalForm_and_realizedWitnessedTranslation
    normalForm shape
      (realizedWitnessedThreeLawTranslationHypothesis_of_provenanced
        translation)

end Splay.Accounting
