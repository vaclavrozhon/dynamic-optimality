import Splay.Accounting.RibStackDigits

namespace Splay.Accounting.OfflineNormalForm.RibStack.Digits

def Uniform (digit : Digit) (digits : List Digit) : Prop := ∀ d ∈ digits, d = digit

@[simp] theorem uniform_nil (digit : Digit) : Uniform digit [] := by simp [Uniform]

@[simp] theorem uniform_cons (digit first : Digit) (tail : List Digit) :
    Uniform digit (first :: tail) ↔ first = digit ∧ Uniform digit tail := by simp [Uniform]

/-- A stopped carry leaves the literal remaining class list and its cost unchanged. -/
theorem push_locality (initial suffix : List Digit) (level : ℕ) (stops : ¬ Uniform .three initial) :
    push (initial ++ suffix) = push initial ++ suffix ∧
      pushCost level (initial ++ suffix) = pushCost level initial ∧
      (push initial).length = initial.length := by
  induction initial generalizing level with
  | nil => exact False.elim (stops (uniform_nil _))
  | cons digit tail ih =>
      cases digit with
      | one => simp [push, pushCost]
      | two => simp [push, pushCost]
      | three =>
          have tailStops : ¬ Uniform .three tail := by simpa using stops
          obtain ⟨same, cost, length⟩ := ih (level + 1) tailStops
          simp [push, pushCost, same, cost, length]

/-- The corresponding locality statement for borrowing. -/
theorem pop_locality (initial suffix : List Digit) (level : ℕ) (stops : ¬ Uniform .one initial) :
    pop (initial ++ suffix) = pop initial ++ suffix ∧
      popCost level (initial ++ suffix) = popCost level initial ∧
      (pop initial).length = initial.length := by
  induction initial generalizing level with
  | nil => exact False.elim (stops (uniform_nil _))
  | cons digit tail ih =>
      cases digit with
      | two => simp [pop, popCost]
      | three => simp [pop, popCost]
      | one =>
          have tailStops : ¬ Uniform .one tail := by simpa using stops
          obtain ⟨same, cost, length⟩ := ih (level + 1) tailStops
          cases tail with
          | nil => exact False.elim (tailStops (uniform_nil _))
          | cons digit tail =>
              simp only [List.cons_append] at same cost
              simp [pop, popCost, same, cost, length]

theorem push_length_le (digits : List Digit) : (push digits).length ≤ digits.length + 1 := by
  induction digits with
  | nil => simp [push]
  | cons digit tail ih => cases digit <;> simp [push]; omega

theorem pop_length_le (digits : List Digit) : (pop digits).length ≤ digits.length := by
  induction digits with
  | nil => simp [pop]
  | cons digit tail ih =>
      cases digit with
      | two => simp [pop]
      | three => simp [pop]
      | one => cases tail <;> simp [pop] at *; omega

theorem pushCost_pos (level : ℕ) (digits : List Digit) : 0 < pushCost level digits := by
  cases digits with
  | nil => simp [pushCost]
  | cons digit tail => cases digit <;> simp [pushCost]

theorem popCost_pos (level : ℕ) (digits : List Digit) (nonempty : digits ≠ []) :
    0 < popCost level digits := by
  cases digits with
  | nil => contradiction
  | cons digit tail => cases digit <;> cases tail <;> simp [popCost]

/-- If the update reaches the last chunk, its existing counter charge pays
for rebuilding the entire folded class spine. -/
theorem length_le_pushCost_of_uniform (initial : List Digit) (last : Digit) (level : ℕ)
    (all : Uniform .three initial) : initial.length + 1 ≤ pushCost level (initial ++ [last]) := by
  induction initial generalizing level with
  | nil => have bound := pushCost_pos level [last]; simpa using Nat.succ_le_of_lt bound
  | cons digit tail ih =>
      obtain ⟨rfl, rest⟩ := (uniform_cons _ _ _).mp all
      have bound := ih (level + 1) rest
      simp only [List.cons_append, pushCost, List.length_cons]
      omega

theorem length_le_popCost_of_uniform (initial : List Digit) (last : Digit) (level : ℕ)
    (all : Uniform .one initial) : initial.length + 1 ≤ popCost level (initial ++ [last]) := by
  induction initial generalizing level with
  | nil => have bound := popCost_pos level [last] (by simp); simpa using Nat.succ_le_of_lt bound
  | cons digit tail ih =>
      obtain ⟨rfl, rest⟩ := (uniform_cons _ _ _).mp all
      have bound := ih (level + 1) rest
      cases tail with
      | nil => simp [popCost]; omega
      | cons digit tail =>
          simp only [List.cons_append, popCost, List.length_cons] at *
          omega

end Splay.Accounting.OfflineNormalForm.RibStack.Digits
