import Splay.Interface.InitialColumnIncidenceAssembly
import Splay.Interface.Potential

/-!
# One initialization charge for an evolving forest

The interface universe may include inactive pivots that will be reinserted by
future joins. Their neutral value is one. `excess` counts only value above one,
so reserving such elements does not charge a new initialization potential.
The theorem uses the existing activity bound; it does not change its factors.
-/

namespace MultiSplay.InterfaceForest

open Splay.Interface

def excess {n : Nat} (state : State n) : Nat :=
  ∑ element : Element n, (state.value element - 1)

theorem excess_add_card {n : Nat} {params : Parameters} {state : State n}
    (valid : state.Valid params) : excess state + (2 * n + 1) = state.totalValue := by
  have pointwise : ∀ element : Element n, state.value element - 1 + 1 = state.value element := by
    intro element
    have bound := (valid.2.1 element).1
    omega
  have sum := Finset.sum_congr rfl (fun element (_ : element ∈ Finset.univ) => pointwise element)
  simpa [excess, State.totalValue, Finset.sum_add_distrib] using sum

theorem trace_final_valid {n : Nat} {params : Parameters} {a b : State n}
    {operations : List (Operation n)} (trace : Trace params a operations b) : b.Valid params := by
  induction trace with
  | nil valid => exact valid
  | cons head tail ih => exact ih

/-- Exact telescoping over the entire history, with dormant elements charged
zero. Neither splits nor joins restart this balance. -/
theorem excess_balance {n : Nat} {params : Parameters} {initial final : State n}
    {operations : List (Operation n)} (valid : initial.Valid params)
    (trace : Trace params initial operations final) :
    excess final + totalDecreases operations = excess initial + totalIncreases operations := by
  have balance := trace.totalValue_balance
  have first := excess_add_card valid
  have last := excess_add_card (trace_final_valid trace)
  omega

theorem valueChanges_le_excess {n : Nat} {params : Parameters} {initial final : State n}
    {operations : List (Operation n)} (valid : initial.Valid params)
    (trace : Trace params initial operations final) :
    totalValueChanges operations ≤ 2 * totalIncreases operations + excess initial := by
  have balance := excess_balance valid trace
  rw [totalValueChanges_eq]
  omega

theorem neutral_excess {n : Nat} (state : State n) (neutral : ∀ element, state.value element = 1) :
    excess state = 0 := by simp [excess, neutral]

/-- Constants are chosen for the interface shape before the value bound and
the universe size. This is the proved original splay black box, with its initial
value term expressed as excess rather than the size of a reserved universe. -/
theorem activity_le_excess (shape : Shape) :
    ∃ insertConstant valueConstant : Nat,
      0 < insertConstant ∧ 0 < valueConstant ∧
      ∀ (params : Parameters), params.toShape = shape →
      ∀ {n : Nat} {initial final : State n} {operations : List (Operation n)},
        initial.Initial params → Trace params initial operations final →
        totalActivity operations ≤
          insertConstant * params.valueBound * totalInserts operations +
          valueConstant * Nat.clog 2 params.valueBound *
            (2 * totalIncreases operations + excess initial) := by
  obtain ⟨insertConstant, valueConstant, hi, hv, bound⟩ := Splay.Interface.activityBound shape
  refine ⟨insertConstant, valueConstant, hi, hv, ?_⟩
  intro params same n initial final operations initialized trace
  exact (bound params same initialized trace).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (valueChanges_le_excess initialized.1 trace)) _)

end MultiSplay.InterfaceForest
