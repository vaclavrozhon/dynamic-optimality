import BlockDepartures

/-!
# Weighted charges over a shrinking block's lifetime

A charged record leaves its source instance permanently. A complete phase
leaves at most one old member. The first phase can use a geometric bound
on the sum of its charges; all subsequent phases together cost at most
one label range. Administrative deletions between phases are allowed.
-/

namespace Greedy.WeightedDepartures

open GreedyForest.Execution
open scoped BigOperators

variable {Record : Type*} [DecidableEq Record]

def total : List (DepartureStep Record × ℤ) → ℤ
  | [] => 0
  | (_, charge) :: rest => charge + total rest

def Bounded (range allowance : ℤ) (steps : List (DepartureStep Record × ℤ)) : Prop :=
  ∀ step ∈ steps, 0 ≤ step.2 ∧ step.2 ≤ range * (step.1.charged.card : ℤ) ∧
    step.2 ≤ allowance

theorem initial_bound (range allowance : ℤ) (rangeNonneg : 0 ≤ range)
    (before : Finset Record) (steps : List (DepartureStep Record × ℤ))
    (transitions : DepartureTransitions before (steps.map Prod.fst))
    (bounded : Bounded range allowance steps) :
    total steps ≤ range * (before.card : ℤ) := by
  induction steps generalizing before with
  | nil => simp only [total]; positivity
  | cons step rest ih =>
      obtain ⟨after, charged, disjoint, _, tailValid⟩ := transitions
      have size := departure_step_card before step.1 after charged disjoint
      have sizeInt : (step.1.charged.card : ℤ) + step.1.after.card ≤ before.card := by
        exact_mod_cast size
      have tail := ih step.1.after tailValid (fun s hs => bounded s (by simp [hs]))
      have head := (bounded step (by simp)).2.1
      have multiply := mul_le_mul_of_nonneg_left sizeInt rangeNonneg
      simp only [total]
      nlinarith

theorem lifetime_bound (range allowance : ℤ) (rangeNonneg : 0 ≤ range)
    (allowanceNonneg : 0 ≤ allowance) (before : Finset Record)
    (steps : List (DepartureStep Record × ℤ))
    (transitions : DepartureTransitions before (steps.map Prod.fst))
    (bounded : Bounded range allowance steps) :
    total steps ≤ allowance + range := by
  induction steps generalizing before with
  | nil => simp only [total]; omega
  | cons step rest ih =>
      obtain ⟨_, _, _, collapse, tailValid⟩ := transitions
      have head := bounded step (by simp)
      have tailBounded : Bounded range allowance rest := fun s hs => bounded s (by simp [hs])
      by_cases empty : step.1.charged.card = 0
      · have upper : step.2 ≤ 0 := by simpa [empty] using head.2.1
        have zero : step.2 = 0 := upper.antisymm head.1
        simpa only [total, zero, zero_add] using ih step.1.after tailValid tailBounded
      · have small : (step.1.after.card : ℤ) ≤ 1 := by
          exact_mod_cast collapse (Nat.pos_of_ne_zero empty)
        have tail := initial_bound range allowance rangeNonneg step.1.after rest tailValid tailBounded
        have multiply := mul_le_mul_of_nonneg_left small rangeNonneg
        simp only [total]
        nlinarith

omit [DecidableEq Record] in
theorem total_ofFn {stages : ℕ} (step : Fin stages → DepartureStep Record)
    (charge : Fin stages → ℤ) :
    total (List.ofFn (fun p => (step p, charge p))) = ∑ p, charge p := by
  have listTotal : ∀ steps : List (DepartureStep Record × ℤ),
      total steps = (steps.map Prod.snd).sum := by
    intro steps
    induction steps with
    | nil => rfl
    | cons step rest ih => simp [total, ih]
  rw [listTotal]
  simp [List.map_ofFn, List.sum_ofFn]

/-- The charged sets are literal images of events under their losing
record. Injectivity and permanent deletion are supplied by the existing
departure history, while the phase allowance may use a weighted cut bound. -/
theorem event_bound {Event : Type*} {stages : ℕ}
    {events : Fin stages → Finset Event} {record : Event → Record}
    (history : EventDepartureHistory Record Event stages events record)
    (charge : Event → ℤ) (range allowance : ℤ)
    (rangeNonneg : 0 ≤ range) (allowanceNonneg : 0 ≤ allowance)
    (each : ∀ p e, e ∈ events p → 0 ≤ charge e ∧ charge e ≤ range)
    (phase : ∀ p, (∑ e ∈ events p, charge e) ≤ allowance) :
    (∑ p, ∑ e ∈ events p, charge e) ≤ allowance + range := by
  classical
  let step := fun p => DepartureStep.mk (history.after p) ((events p).image record)
  let mass := fun p => ∑ e ∈ events p, charge e
  have bounded : Bounded range allowance (List.ofFn (fun p => (step p, mass p))) := by
    intro item member
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp member
    refine ⟨Finset.sum_nonneg (fun e he => (each p e he).1), ?_, phase p⟩
    have size : (step p).charged.card = (events p).card :=
      Finset.card_image_of_injOn (history.injective p)
    rw [size]
    calc
      mass p ≤ ∑ _e ∈ events p, range := Finset.sum_le_sum fun e he => (each p e he).2
      _ = range * ((events p).card : ℤ) := by simp [mul_comm]
  have transitions : DepartureTransitions history.initial
      ((List.ofFn (fun p => (step p, mass p))).map Prod.fst) := by
    simpa only [List.map_ofFn, Function.comp_def, step] using history.transitions
  have bound := lifetime_bound range allowance rangeNonneg allowanceNonneg history.initial
    (List.ofFn (fun p => (step p, mass p))) transitions bounded
  rwa [total_ofFn] at bound

end Greedy.WeightedDepartures
