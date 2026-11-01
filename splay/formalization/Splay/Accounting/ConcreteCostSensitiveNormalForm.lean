import Splay.Accounting.ConcreteCostSensitiveSchedule
import Splay.Accounting.ExactNormalFormWitnessedEndpoint

namespace Splay.Accounting

open Splay.Assumptions.NormalForm
open Splay.Tree.BST

/--
The exact trace chosen by any normal-form realization has a fully concrete
coefficient-four productive-event realization at the natural height-scaled
parameters.
-/
theorem exists_concreteCostSensitiveSchedule_of_normalForm
    {model : CostModel}
    (normalForm : Realization model)
    (shape : Interface.Shape)
    (growingLimit : 2 ≤ shape.growingLimit)
    {n : ℕ} (n_pos : 0 < n)
    (initialTree : BST 0 n)
    (accesses : List (Fin n)) :
    let comparison := normalForm.trace n n_pos accesses
    let height := normalForm.comparisonProfile.maxHeight accesses
    Nonempty
      (ProvenancedInitializedRealizedNormalFormSchedule.ConcreteCostSensitiveRealization
        (heightParameters shape height)
        initialTree comparison height) := by
  let comparison := normalForm.trace n n_pos accesses
  let height := normalForm.comparisonProfile.maxHeight accesses
  have traceHeight :
      comparison.initialTree.height ≤ height := by
    simpa [comparison, height, ComparisonTrace.initialTree] using
      normalForm.trace_height_le_profile n_pos accesses 0
  have initializationBound :
      Analysis.contractedGap
          (Rank.Snapshot.ofTree comparison.initialTree).maxRank ≤
        (heightParameters shape height).valueBound :=
    ofTree_contractedGap_le_heightParameters traceHeight shape
  have parameterGrowingLimit :
      2 ≤ (heightParameters shape height).growingLimit :=
    growingLimit
  exact
    ProvenancedInitializedRealizedNormalFormSchedule.ConcreteCostSensitiveRealization.exists_of_complete
      comparison initialTree parameterGrowingLimit
      initializationBound height

/--
For any paid coefficient at least four, the concrete normal-form realization
also supplies the complete witnessed potential residue.  Its unimportant
productive class is empty.
-/
theorem exists_concreteWitnessedEnvelopePotentialResidue_of_normalForm
    {model : CostModel}
    (normalForm : Realization model)
    (shape : Interface.Shape)
    (growingLimit : 2 ≤ shape.growingLimit)
    {constants : TranslationConstants}
    (four_le_paid : 4 ≤ constants.semantic.paid)
    {n : ℕ} (n_pos : 0 < n)
    (initialTree : BST 0 n)
    (accesses : List (Fin n)) :
    let comparison := normalForm.trace n n_pos accesses
    let height := normalForm.comparisonProfile.maxHeight accesses
    let params := heightParameters shape height
    Nonempty
      (Σ realization :
        ProvenancedInitializedRealizedNormalFormSchedule.ConcreteCostSensitiveRealization
          params initialTree comparison height,
      WitnessedEnvelopePotentialResidue constants params
        (Lazy.eraseOperations
          realization.provenanced.realized.execution.events)
        (normalForm.comparisonProfile.cost accesses) height) := by
  let comparison := normalForm.trace n n_pos accesses
  let height := normalForm.comparisonProfile.maxHeight accesses
  let params := heightParameters shape height
  obtain ⟨realization⟩ :=
    exists_concreteCostSensitiveSchedule_of_normalForm
      normalForm shape growingLimit n_pos initialTree accesses
  refine ⟨⟨realization, realization.toWitnessedEnvelopePotentialResidue
    four_le_paid ?_ ?_⟩⟩
  · simp [comparison, Realization.comparisonProfile, n_pos]
  · exact (heightParameters_valueBound shape height).le

end Splay.Accounting
