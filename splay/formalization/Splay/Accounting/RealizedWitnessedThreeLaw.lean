import Splay.Accounting.SplayDeterminism
import Splay.Accounting.WitnessedOfflineEndpoint
import Splay.Lazy.ScheduleRealizersComplete

namespace Splay.Accounting

open Splay.Assumptions.NormalForm
open Splay.Assumptions.NormalForm.ComparisonTrace
open Splay.Rank
open Splay.Tree.BST
open OfflineOptimum

/--
An initialized normal-form realization exposed by the schedule API.

The schedule and initialized transition share the comparison snapshots and
the exact initial/final splay trees.  The structural facts are retained
alongside the rich execution rather than being discarded after the existence
theorem.
-/
structure InitializedRealizedNormalFormSchedule
    {n : ℕ} {accesses : List (Fin n)}
    (params : Interface.Parameters)
    (initialTree : Tree.BST 0 n)
    (comparison : ComparisonTrace n accesses) where
  groups : List (RequestGroup comparison)
  finalSplayTree : Tree.BST 0 n
  schedule :
    Schedule comparison groups 0 initialTree finalSplayTree
  execution :
    Lazy.InitializedTransition params
      (Snapshot.ofTree comparison.initialTree) initialTree
      (Snapshot.ofTree comparison.finalTree) finalSplayTree
  requests_eq :
    groups.flatMap RequestGroup.requests = accesses
  groups_ordered :
    groups.Pairwise (fun left right => left.time < right.time)
  comparison_serves :
    ∀ group ∈ groups,
      ∀ request ∈ group.requests,
        (comparison.state group.time).HasRoot request.val
  comparisonRotationCount_eq :
    schedule.comparisonRotationCount = comparison.rotationCount

namespace InitializedRealizedNormalFormSchedule

/--
Package the concrete initialized schedule returned by the complete realizer
theorem.
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
      (InitializedRealizedNormalFormSchedule
        params initialTree comparison) := by
  obtain
      ⟨groups, finalSplayTree, schedule, ⟨execution⟩,
        requestsEq, ordered, serves, comparisonCount⟩ :=
    comparison.exists_initializedRealizedNormalFormSchedule_complete
      initialTree growingLimit valueBound
  exact
    ⟨{ groups := groups
       finalSplayTree := finalSplayTree
       schedule := schedule
       execution := execution
       requests_eq := requestsEq
       groups_ordered := ordered
       comparison_serves := serves
       comparisonRotationCount_eq := comparisonCount }⟩

/-- The schedule serves exactly the original request list. -/
theorem servedRequests_eq
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : ComparisonTrace n accesses}
    (realized :
      InitializedRealizedNormalFormSchedule
        params initialTree comparison) :
    realized.schedule.servedRequests = accesses := by
  simpa [Schedule.servedRequests] using realized.requests_eq

/--
Determinism identifies the schedule's final splay tree with the concrete cost
model's chosen final tree.
-/
theorem finalSplayTree_eq_chosen
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : ComparisonTrace n accesses}
    (realized :
      InitializedRealizedNormalFormSchedule
        params initialTree comparison) :
    realized.finalSplayTree =
      (chosenSplaySequenceWitness initialTree accesses).1 :=
  realized.schedule.final_eq_chosen realized.servedRequests_eq

/--
The exact rich final state represents the comparison trace's final rank
snapshot together with the concrete chosen splay tree.
-/
theorem richFinal_represents_chosen
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : ComparisonTrace n accesses}
    (realized :
      InitializedRealizedNormalFormSchedule
        params initialTree comparison) :
    realized.execution.transition.final.Represents params
      (Snapshot.ofTree comparison.finalTree)
      (chosenSplaySequenceWitness initialTree accesses).1 := by
  rw [← realized.finalSplayTree_eq_chosen]
  exact realized.execution.transition.final_represents

end InitializedRealizedNormalFormSchedule

/--
The three-law semantic certificate tied definitionally to one concrete
initialized realized normal-form schedule.

Unlike `WitnessedThreeLawCertificate`, the rich endpoints and event list are
not free fields:

* the initial state is the canonical empty-block state of the comparison
  trace's initial snapshot and the supplied initial splay tree;
* the final state is the exact final state of the realized transition; and
* the event list is definitionally `realized.execution.events`.
-/
structure RealizedWitnessedThreeLawCertificate
    (constants : TranslationConstants)
    (bendConstants : BendConstants)
    (shape : Interface.Shape)
    (insertConstant valueChangeConstant : ℕ)
    (n nearCost height : ℕ)
    (initialTree : Tree.BST 0 n) (accesses : List (Fin n))
    (comparison : ComparisonTrace n accesses) where
  params : Interface.Parameters
  shape_eq : params.toShape = shape
  realized :
    InitializedRealizedNormalFormSchedule
      params initialTree comparison

  pairingClassification :
    BoundaryPassPairingClassification
      (concreteSplayTranscript initialTree accesses).transcript
      params
      (Lazy.Canonical.emptyCanonicalState
        (Snapshot.ofTree comparison.initialTree) initialTree)
      realized.execution.transition.final
      realized.execution.events

  important_le :
    pairingClassification.importantMoves.length ≤
      importantEnvelope constants n nearCost height
  unimportant_le :
    pairingClassification.unimportantMoves.length ≤
      unimportantEnvelope constants height
        (Interface.totalActivity
          (Lazy.eraseOperations realized.execution.events))

  potentialResidue :
    WitnessedEnvelopePotentialResidue constants params
      (Lazy.eraseOperations realized.execution.events)
      nearCost height

  bendWitness :
    ConcreteZigZagBendWitness bendConstants
      initialTree accesses comparison
  comparisonCost_le :
    comparison.cost ≤ nearCost
  bendCoefficient_le :
    bendConstants.coefficient ≤ constants.semantic.bends

namespace RealizedWitnessedThreeLawCertificate

/--
Forget only the explicit normal-form schedule.  The old rich initial state,
final state, and event list are filled by the exact initialized execution.
-/
noncomputable def toWitnessed
    {constants : TranslationConstants}
    {bendConstants : BendConstants}
    {shape : Interface.Shape}
    {insertConstant valueChangeConstant : ℕ}
    {n nearCost height : ℕ}
    {initialTree : Tree.BST 0 n} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses}
    (certificate :
      RealizedWitnessedThreeLawCertificate
        constants bendConstants shape
        insertConstant valueChangeConstant
        n nearCost height initialTree accesses comparison) :
    WitnessedThreeLawCertificate
      constants bendConstants shape
      insertConstant valueChangeConstant
      n nearCost height initialTree accesses comparison where
  params := certificate.params
  richInitial :=
    Lazy.Canonical.emptyCanonicalState
      (Snapshot.ofTree comparison.initialTree) initialTree
  richFinal := certificate.realized.execution.transition.final
  events := certificate.realized.execution.events
  shape_eq := certificate.shape_eq
  pairingClassification := certificate.pairingClassification
  important_le := certificate.important_le
  unimportant_le := certificate.unimportant_le
  potentialResidue := certificate.potentialResidue
  bendWitness := certificate.bendWitness
  comparisonCost_le := certificate.comparisonCost_le
  bendCoefficient_le := certificate.bendCoefficient_le

/-- The forgotten certificate retains the exact realized event list. -/
@[simp]
theorem toWitnessed_events
    {constants : TranslationConstants}
    {bendConstants : BendConstants}
    {shape : Interface.Shape}
    {insertConstant valueChangeConstant : ℕ}
    {n nearCost height : ℕ}
    {initialTree : Tree.BST 0 n} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses}
    (certificate :
      RealizedWitnessedThreeLawCertificate
        constants bendConstants shape
        insertConstant valueChangeConstant
        n nearCost height initialTree accesses comparison) :
    certificate.toWitnessed.events =
      certificate.realized.execution.events :=
  rfl

/--
The trace used by all pairing and boundary witnesses is the complete trace of
the packaged initialized transition.  The equality is proof irrelevance;
its endpoints and event list are already definitionally identical.
-/
theorem pairingTrace_eq_executionTrace
    {constants : TranslationConstants}
    {bendConstants : BendConstants}
    {shape : Interface.Shape}
    {insertConstant valueChangeConstant : ℕ}
    {n nearCost height : ℕ}
    {initialTree : Tree.BST 0 n} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses}
    (certificate :
      RealizedWitnessedThreeLawCertificate
        constants bendConstants shape
        insertConstant valueChangeConstant
        n nearCost height initialTree accesses comparison) :
    certificate.pairingClassification.trace =
      certificate.realized.execution.trace :=
  Subsingleton.elim _ _

/-- Directly recover the existing checked numerical three-law certificate. -/
noncomputable def toThreeLaw
    {constants : TranslationConstants}
    {bendConstants : BendConstants}
    {shape : Interface.Shape}
    {insertConstant valueChangeConstant : ℕ}
    {n nearCost height : ℕ}
    {initialTree : Tree.BST 0 n} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses}
    (n_pos : 0 < n)
    (dominance :
      PotentialCoefficientDominance constants
        insertConstant valueChangeConstant)
    (certificate :
      RealizedWitnessedThreeLawCertificate
        constants bendConstants shape
        insertConstant valueChangeConstant
        n nearCost height initialTree accesses comparison) :
    ThreeLawTranslationCertificate constants shape
      insertConstant valueChangeConstant n nearCost height
      initialTree accesses :=
  certificate.toWitnessed.toThreeLaw n_pos dominance

end RealizedWitnessedThreeLawCertificate

/--
Uniform witnessed translation hypothesis with the same count/envelope
premises as before, but with every rich execution tied to a concrete
initialized realized normal-form schedule.
-/
def RealizedWitnessedThreeLawTranslationHypothesis
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
                (RealizedWitnessedThreeLawCertificate
                  constants bendConstants shape
                  insertConstant valueChangeConstant
                  n (comparisonProfile.cost accesses)
                  (comparisonProfile.maxHeight accesses)
                  initialTree accesses comparison)

/-- Forgetting the concrete schedule recovers the existing witnessed premise. -/
theorem witnessedThreeLawTranslationHypothesis_of_realized
    {comparisonProfile : ComparisonProfile}
    {shape : Interface.Shape}
    (realized :
      RealizedWitnessedThreeLawTranslationHypothesis
        comparisonProfile shape) :
    WitnessedThreeLawTranslationHypothesis comparisonProfile shape := by
  intro insertConstant valueChangeConstant
    insertPositive valueChangePositive
  obtain ⟨constants, bendConstants, dominance, certificates⟩ :=
    realized insertConstant valueChangeConstant
      insertPositive valueChangePositive
  refine ⟨constants, bendConstants, dominance, ?_⟩
  intro n nPositive initialTree accesses
  obtain ⟨comparison, ⟨certificate⟩⟩ :=
    certificates n nPositive initialTree accesses
  exact ⟨comparison, ⟨certificate.toWitnessed⟩⟩

/--
Schedule-tied concrete endpoint: exact offline optimum, uniform normal form,
and the rich three-law witness imply the target bound.
-/
theorem targetBound_of_offlineNormalForm_and_realizedWitnessedTranslation
    (normalForm :
      Assumptions.NormalForm.Hypothesis concreteOfflineCostModel)
    (shape : Interface.Shape)
    (translation :
      RealizedWitnessedThreeLawTranslationHypothesis
        normalForm.realize.comparisonProfile shape) :
    TargetBound concreteOfflineCostModel :=
  targetBound_of_offlineNormalForm_and_witnessedTranslation
    normalForm shape
      (witnessedThreeLawTranslationHypothesis_of_realized translation)

end Splay.Accounting
