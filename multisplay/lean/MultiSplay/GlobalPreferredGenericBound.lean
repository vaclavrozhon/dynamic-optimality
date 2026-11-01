import MultiSplay.GlobalPreferredInventoryHistory
import MultiSplay.ClassicalSwitchAccountingCoefficients

/-! # Generic valid interface factors for the actual classical strategy

The hypothesis concerns the proved split/join interface coefficients at the
normalizer's actual capacity-dependent value cap. Ordinary query-only Splay
competitiveness is not sufficient for this interface. No additional trace,
placement, or physical simulation hypothesis is introduced here.
-/

namespace MultiSplay

/-- A function dominates one valid common-forest interface bound uniformly
in capacity. The coefficient function and domination constant are fixed
before the reference, universe, and request history are supplied. -/
def AdmissibleForestFactor (factor : Nat → Nat) : Prop :=
  ∃ (coefficients : Splay.Interface.ActivityCoefficients) (scale : Nat),
    Splay.Interface.CoefficientBound Splay.Accounting.articleShape coefficients ∧
      ∀ capacity, Splay.Analysis.coefficientFactor coefficients (Unlocated.normalizedValueCap capacity) ≤
        scale * factor capacity

theorem AdmissibleForestFactor.positive {factor : Nat → Nat}
    (valid : AdmissibleForestFactor factor) (capacity : Nat) : 0 < factor capacity := by
  obtain ⟨coefficients,scale,_,bound⟩ := valid
  have positive := Splay.Analysis.coefficientFactor_pos coefficients (Unlocated.normalizedValueCap capacity)
  have paid := bound capacity
  by_contra nonpositive
  have zero : factor capacity = 0 := by omega
  simp only [zero,Nat.mul_zero] at paid
  omega

end MultiSplay

namespace MultiSplay.Global.Preferred.Online

open DynamicOptimality (RawTree BST)
open EndpointEncoding ClassicalSwitch CommonForest

/-- A single comparison constant works for every valid interface coefficient
function, reference, and literal chronological switch word. -/
theorem initial_run_comparator_bound_of_coefficients :
    ∃ constant : Nat, 0 < constant ∧
      ∀ coefficients : Splay.Interface.ActivityCoefficients,
      Splay.Interface.CoefficientBound Splay.Accounting.articleShape coefficients →
      ∀ {n : Nat} (reference : BST 0 n) (preference : EndpointEncoding.State)
        (requests : List (Fin n))
        {sources targets : List (RawTree Nat)} {budget : Nat},
        domains sources = domains (forest preference reference.toRaw) →
        Program sources
          (historyWord reference.toRaw preference
            (requests.map fun key => nodeAddress reference key.val)) targets budget →
        ((strategy reference).run (initial reference preference) requests).2 ≤
          constant * (n + budget) *
            Splay.Analysis.coefficientFactor coefficients (Unlocated.normalizedValueCap reference.height) +
              requests.length := by
  obtain ⟨constant,positive,bound⟩ := Accounting.finite_history_splay_bound_linear_of_coefficients
  refine ⟨2*constant,Nat.mul_pos (by omega) positive,?_⟩
  intro coefficients valid n reference preference requests sources targets budget same comparator
  obtain ⟨next,inventory,trace⟩ := initial_run_trace reference preference requests
  have paid := bound coefficients valid reference preference requests rfl same trace comparator
  calc
    ((strategy reference).run (initial reference preference) requests).2 ≤
        2 * runWork (initial reference preference) requests + requests.length := run_cost_le _ _
    _ ≤ 2 * (constant * (n+budget) *
        Splay.Analysis.coefficientFactor coefficients (Unlocated.normalizedValueCap reference.height)) +
          requests.length := Nat.add_le_add_right (Nat.mul_le_mul_left 2 paid) _
    _ = _ := by ring

/-- Domination changes only the numerical factor. The comparator still has
the exact event word and the initial domains of the fixed physical run. -/
theorem initial_run_comparator_bound_of_factor (factor : Nat → Nat)
    (valid : AdmissibleForestFactor factor) :
    ∃ constant : Nat, 0 < constant ∧
      ∀ {n : Nat} (reference : BST 0 n) (preference : EndpointEncoding.State)
        (requests : List (Fin n))
        {sources targets : List (RawTree Nat)} {budget : Nat},
        domains sources = domains (forest preference reference.toRaw) →
        Program sources
          (historyWord reference.toRaw preference
            (requests.map fun key => nodeAddress reference key.val)) targets budget →
        ((strategy reference).run (initial reference preference) requests).2 ≤
          constant * (n + budget) * factor reference.height + requests.length := by
  obtain ⟨coefficients,scale,coefficientBound,domination⟩ := valid
  obtain ⟨constant,positive,bound⟩ := initial_run_comparator_bound_of_coefficients
  refine ⟨constant*(scale+1),Nat.mul_pos positive (by omega),?_⟩
  intro n reference preference requests sources targets budget same comparator
  have paid := bound coefficients coefficientBound reference preference requests same comparator
  have factorBound := (domination reference.height).trans
    (Nat.mul_le_mul_right (factor reference.height) (Nat.le_succ scale))
  calc
    ((strategy reference).run (initial reference preference) requests).2 ≤
        constant*(n+budget)*
          Splay.Analysis.coefficientFactor coefficients (Unlocated.normalizedValueCap reference.height) +
            requests.length := paid
    _ ≤ constant*(n+budget)*((scale+1)*factor reference.height)+requests.length :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ factorBound) _
    _ = _ := by ring

end MultiSplay.Global.Preferred.Online
