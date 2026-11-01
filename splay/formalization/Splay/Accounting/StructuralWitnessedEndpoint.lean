import Splay.Accounting.ExactNormalFormWitnessedEndpoint
import Splay.Assumptions.StructuralNormalForm

namespace Splay.Assumptions.NormalForm

/--
Reusable data selected from the strengthened structural normal-form
hypothesis.

Besides ordinary logarithmic height and bounded rotation depth, every chosen
state carries the adjacent-null depth consequence used later in the
heavy-path geometry.
-/
structure StructuralRealization (model : CostModel) where
  bounds : StructuralBounds
  trace :
    ∀ (n : ℕ), 0 < n →
      ∀ accesses : List (Fin n), ComparisonTrace n accesses
  isStructurallyNormal :
    ∀ (n : ℕ), ∀ n_pos : 0 < n, ∀ accesses : List (Fin n),
      IsStructurallyNormal bounds (trace n n_pos accesses)
  cost_le :
    ∀ (n : ℕ), ∀ n_pos : 0 < n, ∀ accesses : List (Fin n),
      (trace n n_pos accesses).cost ≤
        bounds.costMultiplier * model.optCost accesses

namespace StructuralRealization

/-- Forgetting the adjacent-null invariant yields an ordinary realization. -/
def toRealization
    {model : CostModel}
    (realization : StructuralRealization model) :
    Realization model where
  bounds := realization.bounds.toBounds
  trace := realization.trace
  isNormal := fun n n_pos accesses =>
    (realization.isStructurallyNormal n n_pos accesses).normal
  cost_le := realization.cost_le

/-- Every selected state exports the rank-level neighbor bound. -/
theorem state_neighborRankBound
    {model : CostModel}
    (realization : StructuralRealization model)
    {n : ℕ} (n_pos : 0 < n) (accesses : List (Fin n))
    (time :
      Fin ((realization.trace n n_pos accesses).rotationCount + 1)) :
    HasRelevantNeighborRankBound
      (Rank.Snapshot.ofTree
        ((realization.trace n n_pos accesses).state time))
      realization.bounds.neighborDepthSlack :=
  IsStructurallyNormal.state_neighborRankBound
    (realization.isStructurallyNormal n n_pos accesses) time

end StructuralRealization

/-- Choice turns the strengthened proposition into reusable structural data. -/
noncomputable def StructuralHypothesis.realize
    {model : CostModel}
    (hypothesis : StructuralHypothesis model) :
    StructuralRealization model := by
  classical
  let bounds := Classical.choose hypothesis
  have certificates := Classical.choose_spec hypothesis
  exact
    { bounds := bounds
      trace := fun n n_pos accesses =>
        Classical.choose (certificates n n_pos accesses)
      isStructurallyNormal := fun n n_pos accesses =>
        (Classical.choose_spec
          (certificates n n_pos accesses)).1
      cost_le := fun n n_pos accesses =>
        (Classical.choose_spec
          (certificates n n_pos accesses)).2 }

end Splay.Assumptions.NormalForm

namespace Splay.Accounting

open Splay.Assumptions.NormalForm
open OfflineOptimum

/--
Exact schedule-bound translation for a structurally normal realization.

This is definitionally the exact-trace hypothesis for the ordinary
realization obtained by forgetting the structural invariant.  A constructor
of the hypothesis still has the full structural realization available, so
the adjacent-null rank bound need not be reintroduced as an unrelated
translation assumption.
-/
def ExactStructuralNormalFormWitnessedTranslationHypothesis
    {model : CostModel}
    (realization : StructuralRealization model)
    (shape : Interface.Shape) : Prop :=
  ExactNormalFormRealizedWitnessedTranslationHypothesis
    realization.toRealization shape

/--
Target bound from an explicit structurally normal realization and witnesses
tied to its exact comparison traces and initialized rich schedules.
-/
theorem
    targetBound_of_offlineStructuralNormalFormRealization_and_witnessedTranslation
    (realization :
      StructuralRealization concreteOfflineCostModel)
    (shape : Interface.Shape)
    (translation :
      ExactStructuralNormalFormWitnessedTranslationHypothesis
        realization shape) :
    TargetBound concreteOfflineCostModel := by
  apply
    targetBound_of_offlineNormalFormRealization_and_threeLawTranslation
      realization.toRealization shape
  exact
    threeLawTranslationHypothesis_of_witnessed
      (witnessedThreeLawTranslationHypothesis_of_realized
        (realizedWitnessedTranslationHypothesis_of_exactNormalForm
          translation))

/--
Manuscript-shaped endpoint from strengthened normal form and an exact
schedule-bound semantic translation.
-/
theorem
    targetBound_of_offlineStructuralNormalForm_and_witnessedTranslation
    (normalForm :
      StructuralHypothesis concreteOfflineCostModel)
    (shape : Interface.Shape)
    (translation :
      ExactStructuralNormalFormWitnessedTranslationHypothesis
        normalForm.realize shape) :
    TargetBound concreteOfflineCostModel :=
  targetBound_of_offlineStructuralNormalFormRealization_and_witnessedTranslation
    normalForm.realize shape translation

/--
Schedule-provenanced counterpart of the exact structural translation
hypothesis.
-/
def ExactStructuralNormalFormProvenancedWitnessedTranslationHypothesis
    {model : CostModel}
    (realization : StructuralRealization model)
    (shape : Interface.Shape) : Prop :=
  ExactNormalFormProvenancedWitnessedTranslationHypothesis
    realization.toRealization shape

/--
The manuscript-shaped endpoint with every currently expressible semantic
link retained: structural normal form, the exact selected comparison trace,
the exact rich events, and recursive provenance through the concrete
normal-form schedule.
-/
theorem
    targetBound_of_offlineStructuralNormalForm_and_exactProvenancedWitnessedTranslation
    (normalForm :
      StructuralHypothesis concreteOfflineCostModel)
    (shape : Interface.Shape)
    (translation :
      ExactStructuralNormalFormProvenancedWitnessedTranslationHypothesis
        normalForm.realize shape) :
    TargetBound concreteOfflineCostModel := by
  apply
    targetBound_of_offlineNormalFormRealization_and_threeLawTranslation
      normalForm.realize.toRealization shape
  exact
    threeLawTranslationHypothesis_of_witnessed
      (witnessedThreeLawTranslationHypothesis_of_realized
        (realizedWitnessedThreeLawTranslationHypothesis_of_provenanced
          (provenancedRealizedWitnessedTranslationHypothesis_of_exactNormalForm
            translation)))

end Splay.Accounting
