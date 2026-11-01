import MultiSplay.InitializedClassicalExecution
import MultiSplay.ComparatorConcreteService
import MultiSplay.ComparatorCompetitiveReduction
import MultiSplay.InitializedGenericBound

/-!
# Classical MultiSplay in the common BST/OPT model

The concrete maintained comparator executes the actual classical event word.
Its construction discharges every service and representation premise before
applying the persistent forest Splay comparison. The algorithm is the fixed
online strategy of `InitializedOnline`, with actual original-key rotations
and one charged initialization from any supplied initial BST.
-/

namespace MultiSplay.Online

open DynamicOptimality

/-- An actual inexpensive comparator for every classical request history.
This theorem has no comparator, simulation, or invariant hypothesis. -/
theorem comparator_estimate : ComparatorEstimate (100000000 * 2137120) :=
  ComparatorForest.comparator_estimate_of_services 100000000 (fun n =>
    ComparatorForest.service_of_pairService (balancedReference n) (balancedHierarchy n)
      100000000
      (ComparatorForest.concrete_pair_service (balancedReference n) (balancedHierarchy n)))

/-- The exact-height composed bound, including the empty universe. -/
theorem composed_bound :
    ∃ constant : Nat, 0 < constant ∧
      ∀ {n : Nat} (before : BST 0 n) (requests : List (Fin n)),
        cost before requests ≤ constant * (OPT requests+n) *
          (comparisonFactor (balancedReference n).height *
            Splay.Analysis.egTargetFactor (balancedReference n).height) :=
  cost_bound_of_comparator_estimate comparator_estimate

/-- `O(L₃(n) * g(2 L₁(n)))` competitiveness, where `g` is the strongest
currently proved Splay factor. Constants are uniform in the universe,
initial tree and request word. -/
theorem competitive : Competitive cost shiftedEGFactor :=
  competitive_of_comparator_estimate comparator_estimate

/-- The explicit expanded factor, with the same actual online algorithm. -/
theorem competitive_expanded : Competitive cost competitiveEGFactor := by
  obtain ⟨constant,positive,bound⟩ := composed_bound
  refine ⟨20*constant,by omega,?_⟩
  intro n _ before requests
  calc
    cost before requests ≤ constant*(OPT requests+n)*
        (comparisonFactor (balancedReference n).height *
          Splay.Analysis.egTargetFactor (balancedReference n).height) := bound before requests
    _ ≤ constant*(OPT requests+n)*(20*competitiveEGFactor n) :=
      Nat.mul_le_mul_left _ (balancedReference_composedEGFactor_le n)
    _ = _ := by ring

/-- Generalization to every factor supported by valid persistent Splay
interface coefficients. No cheap-comparator assumption remains. -/
theorem competitive_generic (factor : Nat → Nat) (valid : AdmissibleForestFactor factor) :
    Competitive cost (fun n => comparisonFactor (balancedReference n).height *
      factor (balancedReference n).height) :=
  competitive_of_factor comparator_estimate factor valid

/-- A monotone admissible factor gives the shifted logarithmic form. This
interface concerns split/join histories, not only ordinary query sequences. -/
theorem competitive_generic_shifted (factor : Nat → Nat)
    (valid : AdmissibleForestFactor factor) (monotone : Monotone factor) :
    Competitive cost (fun n => Splay.Analysis.iteratedLog 3 n *
      factor (2 * Splay.Analysis.iteratedLog 1 n)) :=
  competitive_shifted_of_factor comparator_estimate factor valid monotone

end MultiSplay.Online
