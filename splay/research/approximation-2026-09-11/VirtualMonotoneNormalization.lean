import VirtualNumericInsertion
import Mathlib.Data.List.FinRange

/-! Finite abstract monotone normalization. Every numerical coordinate is
lowered to a specified positive target. The literal trace has zero value
increases, zero block growth, and exactly preserves all block payloads. -/

namespace Splay.Research.VirtualMonotoneNormalization

open Splay.Interface Splay.Research.VirtualNumericInsertion

def updateState {n : ℕ} (before : State n) (target : Element n → ℕ) :
    List (Element n) → State n
  | [] => before
  | element::elements => updateState (setValue before element (target element)) target elements

def events {n : ℕ} (before : State n) (target : Element n → ℕ) :
    List (Element n) → List (Operation n)
  | [] => []
  | element::elements =>
      List.replicate (before.value element-target element) (.valueChange element .decrease) ++
        events (setValue before element (target element)) target elements

theorem updateState_blocks {n : ℕ} (before : State n) (target : Element n → ℕ)
    (elements : List (Element n)) : (updateState before target elements).blocks = before.blocks := by
  induction elements generalizing before with
  | nil => rfl
  | cons element elements ih => exact ih _

theorem updateState_values {n : ℕ} (before : State n) (target : Element n → ℕ)
    (elements : List (Element n)) (queried : Element n) :
    (updateState before target elements).value queried =
      if queried ∈ elements then target queried else before.value queried := by
  induction elements generalizing before with
  | nil => simp [updateState]
  | cons element elements ih =>
      simp only [updateState, ih, List.mem_cons]
      by_cases later : queried ∈ elements
      · simp [later]
      · by_cases same : queried = element <;> simp [later, same, setValue]

theorem events_increases {n : ℕ} (before : State n) (target : Element n → ℕ)
    (elements : List (Element n)) : totalIncreases (events before target elements) = 0 := by
  induction elements generalizing before with
  | nil => simp [events, totalIncreases]
  | cons element elements ih =>
      have tail := ih (setValue before element (target element))
      simp only [totalIncreases] at tail
      simp [events, totalIncreases, Operation.increaseCount, tail]

theorem events_growth {n : ℕ} (before : State n) (target : Element n → ℕ)
    (elements : List (Element n)) : totalBlockGrowth (events before target elements) = 0 := by
  induction elements generalizing before with
  | nil => simp [events, totalBlockGrowth]
  | cons element elements ih =>
      have tail := ih (setValue before element (target element))
      simp only [totalBlockGrowth] at tail
      simp [events, totalBlockGrowth, Operation.blockGrowth, tail]

theorem trace {n : ℕ} {params : Parameters} (before : State n) (target : Element n → ℕ)
    (elements : List (Element n)) (valid : before.Valid params)
    (positive : ∀ element, 1 ≤ target element)
    (lower : ∀ element, target element ≤ before.value element) :
    Trace params before (events before target elements) (updateState before target elements) := by
  induction elements generalizing before with
  | nil => exact .nil valid
  | cons element elements ih =>
      let next := setValue before element (target element)
      have nextValid : next.Valid params := setValue_valid before element (target element) valid
        (positive element) ((lower element).trans (valid.2.1 element).2)
      have nextLower : ∀ queried, target queried ≤ next.value queried := by
        intro queried
        by_cases same : queried = element
        · simp [next, setValue, same]
        · simpa [next, setValue, same] using lower queried
      have head := decreases_trace before element (before.value element-target element) valid
        (by have := positive element; have := lower element; omega)
      have arithmetic : before.value element-(before.value element-target element) = target element := by
        have := lower element
        omega
      rw [arithmetic] at head
      exact trace_append head (ih next nextValid nextLower)

private theorem state_eq {n : ℕ} {left right : State n}
    (blocks : left.blocks = right.blocks) (values : left.value = right.value) : left = right := by
  cases left
  cases right
  simp_all

/-- Normalize every coordinate, including currently unused elements, to
exactly `target`. Physical-span baseline increases can use this with no
additional charged numerical variation. -/
theorem full_trace {n : ℕ} {params : Parameters} (before : State n) (target : Element n → ℕ)
    (valid : before.Valid params) (positive : ∀ element, 1 ≤ target element)
    (lower : ∀ element, target element ≤ before.value element) :
    Trace params before (events before target (List.finRange (2*n+1)))
      (State.mk before.blocks target) := by
  have run := trace before target (List.finRange (2*n+1)) valid positive lower
  have endpoint : updateState before target (List.finRange (2*n+1)) = State.mk before.blocks target := by
    apply state_eq (left := updateState before target (List.finRange (2*n+1)))
      (right := State.mk before.blocks target) (updateState_blocks before target _)
    funext element
    simpa only [List.mem_finRange, ↓reduceIte] using updateState_values before target
      (List.finRange (2*n+1)) element
  rw [endpoint] at run
  exact run

end Splay.Research.VirtualMonotoneNormalization

#print axioms Splay.Research.VirtualMonotoneNormalization.full_trace
#print axioms Splay.Research.VirtualMonotoneNormalization.events_increases
#print axioms Splay.Research.VirtualMonotoneNormalization.events_growth
