import VirtualMonotoneNormalization
import Splay.Interface.OperationCounts

/-! Arbitrary finite bounded relabeling on unchanged blocks. The exact
upward bill is the sum of positive coordinate differences; decreasing
coordinates create no charged variation. This is a literal interface
trace and preserves all structural operation counts. -/

namespace Splay.Research.VirtualFiniteRelabel

open Splay.Interface Splay.Research.VirtualNumericInsertion
open Splay.Research.VirtualMonotoneNormalization (updateState updateState_blocks updateState_values)

noncomputable def events {n : ℕ} (before : State n) (target : Element n → ℕ) :
    List (Element n) → List (Operation n)
  | [] => []
  | element::elements =>
      (if target element ≤ before.value element then
        List.replicate (before.value element-target element) (.valueChange element .decrease)
      else List.replicate (target element-before.value element) (.valueChange element .increase)) ++
      events (setValue before element (target element)) target elements

theorem trace {n : ℕ} {params : Parameters} (before : State n) (target : Element n → ℕ)
    (elements : List (Element n)) (valid : before.Valid params)
    (positive : ∀ element, 1 ≤ target element) (bounded : ∀ element, target element ≤ params.valueBound) :
    Trace params before (events before target elements) (updateState before target elements) := by
  induction elements generalizing before with
  | nil => exact .nil valid
  | cons element elements ih =>
      let next := setValue before element (target element)
      have nextValid : next.Valid params := setValue_valid before element (target element) valid
        (positive element) (bounded element)
      have tail := ih next nextValid
      by_cases lower : target element ≤ before.value element
      · have first := decreases_trace before element (before.value element-target element) valid
          (by have := positive element; omega)
        have arithmetic : before.value element-(before.value element-target element) = target element := by omega
        rw [arithmetic] at first
        simpa only [events, lower, ↓reduceIte, updateState] using trace_append first tail
      · have first := increases_trace before element (target element-before.value element) valid
          (by have := bounded element; omega)
        have arithmetic : before.value element+(target element-before.value element) = target element := by omega
        rw [arithmetic] at first
        simpa only [events, lower, ↓reduceIte, updateState] using trace_append first tail

theorem increases {n : ℕ} (before : State n) (target : Element n → ℕ)
    (elements : List (Element n)) (distinct : elements.Nodup) :
    totalIncreases (events before target elements) =
      (elements.map fun element => target element-before.value element).sum := by
  induction elements generalizing before with
  | nil => rfl
  | cons element elements ih =>
      obtain ⟨fresh, tailDistinct⟩ := List.nodup_cons.mp distinct
      let next := setValue before element (target element)
      have tail := ih next tailDistinct
      have sameCosts : (elements.map fun queried => target queried-next.value queried) =
          (elements.map fun queried => target queried-before.value queried) := by
        apply List.map_congr_left
        intro queried member
        have different : queried ≠ element := by intro equal; subst queried; exact fresh member
        simp [next, setValue, different]
      rw [sameCosts] at tail
      change totalIncreases ((if target element ≤ before.value element then _ else _) ++ events next target elements) = _
      rw [totalIncreases_append, tail]
      by_cases lower : target element ≤ before.value element
      · simp [lower, Nat.sub_eq_zero_of_le lower, totalIncreases, Operation.increaseCount]
      · simp [lower, totalIncreases, Operation.increaseCount]

theorem counters {n : ℕ} (before : State n) (target : Element n → ℕ) (elements : List (Element n)) :
    totalActivity (events before target elements) = 0 ∧ totalBlockGrowth (events before target elements) = 0 ∧
      totalInserts (events before target elements) = 0 := by
  induction elements generalizing before with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons element elements ih =>
      have tail := ih (setValue before element (target element))
      simp only [events, totalActivity_append, totalBlockGrowth_append, totalInserts_append,
        tail.1, tail.2.1, tail.2.2, Nat.add_zero]
      split <;> simp [totalActivity, totalBlockGrowth, totalInserts,
        Operation.activity, Operation.blockGrowth, Operation.insertCount]

private theorem state_eq {n : ℕ} {left right : State n}
    (blocks : left.blocks = right.blocks) (values : left.value = right.value) : left = right := by
  cases left
  cases right
  simp_all

/-- All coordinates finish at the exact requested labels. The finite sum
includes unused coordinates, which can be given default label one. -/
theorem realize {n : ℕ} {params : Parameters} (before : State n) (target : Element n → ℕ)
    (valid : before.Valid params) (positive : ∀ element, 1 ≤ target element)
    (bounded : ∀ element, target element ≤ params.valueBound) :
    Trace params before (events before target (List.finRange (2*n+1))) (State.mk before.blocks target) ∧
      totalIncreases (events before target (List.finRange (2*n+1))) =
        ((List.finRange (2*n+1)).map fun element => target element-before.value element).sum ∧
      totalActivity (events before target (List.finRange (2*n+1))) = 0 ∧
      totalBlockGrowth (events before target (List.finRange (2*n+1))) = 0 ∧
      totalInserts (events before target (List.finRange (2*n+1))) = 0 := by
  have run := trace before target (List.finRange (2*n+1)) valid positive bounded
  have endpoint : updateState before target (List.finRange (2*n+1)) = State.mk before.blocks target := by
    apply state_eq (left := updateState before target (List.finRange (2*n+1)))
      (right := State.mk before.blocks target) (updateState_blocks before target _)
    funext element
    simpa only [List.mem_finRange, ↓reduceIte] using updateState_values before target
      (List.finRange (2*n+1)) element
  rw [endpoint] at run
  exact ⟨run, increases before target _ (List.nodup_finRange _), counters before target _⟩

end Splay.Research.VirtualFiniteRelabel

#print axioms Splay.Research.VirtualFiniteRelabel.realize
