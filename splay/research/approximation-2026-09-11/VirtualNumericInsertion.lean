import VirtualInterfaceAdmin
import Splay.Interface.Potential
import Mathlib.Tactic

/-! Numeric implementation of active singleton birth in the abstract
interface. The creator stays fixed; the newborn starts and ends at 1.
The one-unit cap room and creator/newborn distinction are explicit. -/

namespace Splay.Research.VirtualNumericInsertion

open Splay.Interface Splay.Research.VirtualInterfaceAdmin

def setValue {n : ℕ} (state : State n) (element : Element n) (target : ℕ) : State n :=
  ⟨state.blocks, Function.update state.value element target⟩

@[simp] theorem setValue_self {n : ℕ} (state : State n) (element : Element n) :
    setValue state element (state.value element) = state := by
  simp [setValue]

@[simp] theorem setValue_twice {n : ℕ} (state : State n) (element : Element n) (x y : ℕ) :
    setValue (setValue state element x) element y = setValue state element y := by
  simp [setValue]

theorem setValue_valid {n : ℕ} {params : Parameters} (state : State n)
    (element : Element n) (target : ℕ) (valid : state.Valid params)
    (positive : 1 ≤ target) (bounded : target ≤ params.valueBound) :
    (setValue state element target).Valid params := by
  refine ⟨valid.1, ?_, valid.2.2⟩
  intro queried
  by_cases same : queried = element
  · subst queried
    simpa [setValue] using And.intro positive bounded
  · simpa [setValue, same] using valid.2.1 queried

theorem trace_append {n : ℕ} {params : Parameters} {before middle after : State n}
    {first second : List (Operation n)} (one : Trace params before first middle)
    (two : Trace params middle second after) :
    Trace params before (first ++ second) after := by
  induction one with
  | nil valid => exact two
  | cons step tail ih => exact .cons step (ih two)

theorem increases_trace {n : ℕ} {params : Parameters} (state : State n)
    (element : Element n) (count : ℕ) (valid : state.Valid params)
    (bounded : state.value element + count ≤ params.valueBound) :
    Trace params state (List.replicate count (.valueChange element .increase))
      (setValue state element (state.value element + count)) := by
  induction count generalizing state with
  | zero => simpa using Trace.nil valid
  | succ count ih =>
      let next := setValue state element (state.value element+1)
      have nextValid : next.Valid params := setValue_valid state element _ valid (by omega) (by omega)
      have nextValue : next.value element = state.value element+1 := by simp [next, setValue]
      have step : Step params state (.valueChange element .increase) next :=
        ⟨valid, .increase (by omega) rfl rfl, nextValid⟩
      have rest := ih next nextValid (by rw [nextValue]; omega)
      have joined := Trace.cons step rest
      simpa [List.replicate_succ, next, setValue, Nat.add_assoc, Nat.add_comm] using joined

theorem decreases_trace {n : ℕ} {params : Parameters} (state : State n)
    (element : Element n) (count : ℕ) (valid : state.Valid params)
    (positive : count+1 ≤ state.value element) :
    Trace params state (List.replicate count (.valueChange element .decrease))
      (setValue state element (state.value element - count)) := by
  induction count generalizing state with
  | zero => simpa using Trace.nil valid
  | succ count ih =>
      let next := setValue state element (state.value element-1)
      have nextValid : next.Valid params := setValue_valid state element _ valid (by omega)
        ((Nat.sub_le _ _).trans (valid.2.1 element).2)
      have nextValue : next.value element = state.value element-1 := by simp [next, setValue]
      have step : Step params state (.valueChange element .decrease) next :=
        ⟨valid, .decrease (by omega) rfl rfl, nextValid⟩
      have rest := ih next nextValid (by rw [nextValue]; omega)
      have joined := Trace.cons step rest
      have arithmetic : state.value element-1-count = state.value element-(count+1) := by omega
      simpa [List.replicate_succ, next, setValue, arithmetic] using joined

def singletonEvents {n : ℕ} (before : State n) (creator element : Element n) : List (Operation n) :=
  List.replicate (before.value creator) (.valueChange element .increase) ++
    [.create creator, .insert before.blocks.length element, .convert before.blocks.length] ++
    List.replicate (before.value creator) (.valueChange element .decrease)

theorem singleton_trace {n : ℕ} {params : Parameters} (before : State n)
    (creator element : Element n) (valid : before.Valid params)
    (fresh : element ∉ before.allElements) (different : creator ≠ element)
    (room : before.growingCount creator < params.growingLimit)
    (unit : before.value element = 1)
    (capRoom : before.value creator+1 ≤ params.valueBound) :
    Trace params before (singletonEvents before creator element)
      (appendBlock before (freshBlock creator .shrinking [element])) := by
  let raised := setValue before element (before.value creator+1)
  have raising : Trace params before
      (List.replicate (before.value creator) (.valueChange element .increase)) raised := by
    simpa [unit, raised, Nat.add_comm] using
      increases_trace before element (before.value creator) valid (by omega)
  have raisedValid := setValue_valid before element (before.value creator+1) valid (by omega) capRoom
  have insertion := append_singleton_trace raised creator element raisedValid fresh room
    (by simp [raised, setValue, different])
  let inserted := appendBlock raised (freshBlock creator .shrinking [element])
  have insertedValid := append_shrinking_valid raised creator [element] raisedValid (by
    refine List.nodup_append.mpr ⟨valid.1, by simp, ?_⟩
    intro old member selected singleton equal
    have selectedEq : selected = element := by simpa using singleton
    exact fresh ((equal.trans selectedEq) ▸ member))
  have lowering := decreases_trace inserted element (before.value creator) insertedValid
    (by simp [inserted, appendBlock, raised, setValue])
  have joined := trace_append (trace_append raising insertion) lowering
  have endpoint : setValue inserted element (inserted.value element-before.value creator) =
      appendBlock before (freshBlock creator .shrinking [element]) := by
    simp [inserted, appendBlock, raised, setValue, ← unit]
  rw [endpoint] at joined
  exact joined

theorem singleton_increases {n : ℕ} (before : State n) (creator element : Element n) :
    totalIncreases (singletonEvents before creator element) = before.value creator := by
  simp [singletonEvents, totalIncreases, Operation.increaseCount]

theorem singleton_growth {n : ℕ} (before : State n) (creator element : Element n) :
    totalBlockGrowth (singletonEvents before creator element) = 1 := by
  simp [singletonEvents, totalBlockGrowth, Operation.blockGrowth]

end Splay.Research.VirtualNumericInsertion

#print axioms Splay.Research.VirtualNumericInsertion.singleton_trace
#print axioms Splay.Research.VirtualNumericInsertion.singleton_increases
#print axioms Splay.Research.VirtualNumericInsertion.singleton_growth
