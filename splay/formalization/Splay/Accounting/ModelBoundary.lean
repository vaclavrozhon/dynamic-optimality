import Splay.Accounting.Bridge
import Splay.ModelBoundary

namespace Splay.Accounting

/--
A comparison profile exporting no cost and no height.

This is intentionally not claimed to arise from a normal-form trace.  It is
the smallest witness showing that the lawless `CostModel` and
`ComparisonProfile` structures do not imply the accounting hypothesis.
-/
def zeroComparisonProfile : ComparisonProfile where
  cost := fun _ => 0
  maxHeight := fun _ => 0

/--
The request-count model with the zero comparison profile has no family of
accounting certificates.

For any proposed uniform constants, choose a request list one longer than the
bound delivered by `Certificate.cost_bound`.  The model assigns that list its
length as splay cost, while the comparison profile keeps both numerical inputs
of the certificate fixed at zero.
-/
theorem unboundedAbstractModel_not_accountingHypothesis :
    ¬ Hypothesis Splay.unboundedAbstractModel zeroComparisonProfile := by
  rintro ⟨constants, certificates⟩
  let bound :=
    constants.coreConstant *
      (1 + 0) * gapBound 0 * gapLog 0 ^ 2
  let request : Fin 1 := ⟨0, by omega⟩
  let accesses : List (Fin 1) :=
    List.replicate (bound + 1) request
  obtain ⟨certificate⟩ :=
    certificates 1 (by omega) () accesses
  have impossible := certificate.cost_bound
  simp only [Splay.unboundedAbstractModel, zeroComparisonProfile,
    accesses, List.length_replicate] at impossible
  change bound + 1 ≤ bound at impossible
  omega

/--
Consequently there is no theorem deriving `Accounting.Hypothesis` for every
pair of inhabitants of the two abstract, lawless numerical structures.
-/
theorem not_every_model_profile_satisfies_accountingHypothesis :
    ¬ ∀ (model : CostModel) (comparison : ComparisonProfile),
      Hypothesis model comparison := by
  intro universal
  exact unboundedAbstractModel_not_accountingHypothesis
    (universal Splay.unboundedAbstractModel zeroComparisonProfile)

end Splay.Accounting
