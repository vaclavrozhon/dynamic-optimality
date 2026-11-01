import Mathlib.Tactic

/-!
# Weighted amortization of the ribless stack's class counter

There are one, two, or three trees of each nonempty class. A carry or borrow
resets all preceding classes to two trees. Class `i` work may cost `i + 1`,
so the potential weights a non-two digit by `4 * (i + 1)`.

The resulting bound covers arbitrary interleavings of pushes and pops. It
does not assume a frequency bound proved only for monotone update sequences.
-/

namespace Splay.Accounting.OfflineNormalForm.RibStack.Digits

inductive Digit
  | one | two | three
  deriving DecidableEq, Repr

def Digit.value : Digit → ℕ
  | .one => 1
  | .two => 2
  | .three => 3

def value : List Digit → ℕ
  | [] => 0
  | digit :: tail => digit.value + 2 * value tail

def push : List Digit → List Digit
  | [] => [.one]
  | .one :: tail => .two :: tail
  | .two :: tail => .three :: tail
  | .three :: tail => .two :: push tail

def pop : List Digit → List Digit
  | [] => []
  | [.one] => []
  | .one :: digit :: tail => .two :: pop (digit :: tail)
  | .two :: tail => .one :: tail
  | .three :: tail => .two :: tail

def pushCost (level : ℕ) : List Digit → ℕ
  | .three :: tail => level + 1 + pushCost (level + 1) tail
  | _ => level + 1

def popCost (level : ℕ) : List Digit → ℕ
  | [] => 0
  | .one :: digit :: tail => level + 1 + popCost (level + 1) (digit :: tail)
  | _ => level + 1

def potential (level : ℕ) : List Digit → ℕ
  | [] => 0
  | digit :: tail => (if digit = .two then 0 else 4 * (level + 1)) + potential (level + 1) tail

def allowance (level : ℕ) : ℕ := if level = 0 then 7 else 5 * (level + 1)

theorem terminal_le_allowance (level : ℕ) : 5 * (level + 1) ≤ allowance level := by
  cases level <;> simp [allowance]

theorem carry_le_allowance (level : ℕ) :
    level + 1 + allowance (level + 1) ≤ 4 * (level + 1) + allowance level := by
  cases level <;> simp [allowance]
  omega

@[simp] theorem value_push (digits : List Digit) : value (push digits) = value digits + 1 := by
  induction digits with
  | nil => rfl
  | cons digit tail ih =>
      cases digit <;> simp [push, value, Digit.value, ih] <;> omega

theorem value_pop (digits : List Digit) (nonempty : digits ≠ []) :
    value (pop digits) + 1 = value digits := by
  induction digits with
  | nil => exact False.elim (nonempty rfl)
  | cons digit tail ih =>
      cases digit with
      | one =>
          cases tail with
          | nil => rfl
          | cons digit tail =>
              have rest := ih (by simp)
              simp only [pop, value, Digit.value] at *
              omega
      | two => simp [pop, value, Digit.value]; omega
      | three => simp [pop, value, Digit.value]; omega

theorem push_amortized (level : ℕ) (digits : List Digit) :
    pushCost level digits + potential level (push digits) ≤
      potential level digits + allowance level := by
  induction digits generalizing level with
  | nil =>
      have := terminal_le_allowance level
      simp only [pushCost, push, potential, reduceCtorEq, if_false, Nat.add_zero, Nat.zero_add]
      omega
  | cons digit tail ih =>
      have terminal := terminal_le_allowance level
      have carry := carry_le_allowance level
      have rest := ih (level + 1)
      cases digit <;> simp only [pushCost, push, potential, reduceCtorEq, if_false, if_true] at * <;> omega

theorem pop_amortized (level : ℕ) (digits : List Digit) :
    popCost level digits + potential level (pop digits) ≤
      potential level digits + allowance level := by
  induction digits generalizing level with
  | nil => simp [popCost, pop, potential]
  | cons digit tail ih =>
      have terminal := terminal_le_allowance level
      have carry := carry_le_allowance level
      have rest := ih (level + 1)
      cases digit with
      | one =>
          cases tail with
          | nil => simp [popCost, pop, potential]; omega
          | cons digit tail =>
              simp only [popCost, pop, potential, reduceCtorEq, if_false, if_true] at *
              omega
      | two => simp [popCost, pop, potential]; omega
      | three => simp [popCost, pop, potential]; omega

theorem potential_le_value (level : ℕ) (digits : List Digit) :
    potential level digits ≤ 4 * (level + 1) * value digits := by
  induction digits generalizing level with
  | nil => simp [potential, value]
  | cons digit tail ih =>
      have rest := ih (level + 1)
      have scaled : 4 * (level + 1 + 1) * value tail ≤ 8 * (level + 1) * value tail :=
        Nat.mul_le_mul_right _ (by omega)
      cases digit <;> simp [potential, value, Digit.value] at * <;> nlinarith

/-- Every represented class consumes exponentially many stack elements. -/
theorem pow_length_le_value (digits : List Digit) : 2 ^ digits.length ≤ value digits + 1 := by
  induction digits with
  | nil => simp [value]
  | cons digit tail ih =>
      cases digit <;> simp [value, Digit.value, pow_succ] <;> omega

theorem pushCost_le_quadratic (level : ℕ) (digits : List Digit) :
    pushCost level digits ≤ (digits.length + 1) * (level + digits.length + 1) := by
  induction digits generalizing level with
  | nil => simp [pushCost]
  | cons digit tail ih =>
      have rest := ih (level + 1)
      cases digit <;> simp only [pushCost, List.length_cons] <;> nlinarith

theorem popCost_le_quadratic (level : ℕ) (digits : List Digit) :
    popCost level digits ≤ (digits.length + 1) * (level + digits.length + 1) := by
  induction digits generalizing level with
  | nil => simp [popCost]
  | cons digit tail ih =>
      have rest := ih (level + 1)
      cases digit with
      | one =>
          cases tail with
          | nil => simp [popCost]; omega
          | cons digit tail =>
              simp only [popCost, List.length_cons] at *
              nlinarith
      | two => simp only [popCost, List.length_cons]; nlinarith
      | three => simp only [popCost, List.length_cons]; nlinarith

theorem length_le_clog (digits : List Digit) : digits.length ≤ Nat.clog 2 (value digits + 1) := by
  have monotone := Nat.clog_mono_right 2 (pow_length_le_value digits)
  simpa only [Nat.clog_pow 2 digits.length (by decide)] using monotone

theorem pushCost_le_logSquared (digits : List Digit) :
    pushCost 0 digits ≤ (Nat.clog 2 (value digits + 1) + 1) ^ 2 := by
  have cost := pushCost_le_quadratic 0 digits
  have levels := length_le_clog digits
  calc
    pushCost 0 digits ≤ (digits.length + 1) * (digits.length + 1) := by simpa using cost
    _ ≤ (Nat.clog 2 (value digits + 1) + 1) * (Nat.clog 2 (value digits + 1) + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    _ = _ := by ring

theorem popCost_le_logSquared (digits : List Digit) :
    popCost 0 digits ≤ (Nat.clog 2 (value digits + 1) + 1) ^ 2 := by
  have cost := popCost_le_quadratic 0 digits
  have levels := length_le_clog digits
  calc
    popCost 0 digits ≤ (digits.length + 1) * (digits.length + 1) := by simpa using cost
    _ ≤ (Nat.clog 2 (value digits + 1) + 1) * (Nat.clog 2 (value digits + 1) + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    _ = _ := by ring

inductive Operation
  | push | pop
  deriving DecidableEq, Repr

def Operation.apply : Operation → List Digit → List Digit
  | .push => Digits.push
  | .pop => Digits.pop

def Operation.cost : Operation → List Digit → ℕ
  | .push => pushCost 0
  | .pop => popCost 0

def run : List Operation → List Digit → List Digit
  | [], digits => digits
  | operation :: tail, digits => run tail (operation.apply digits)

def runCost : List Operation → List Digit → ℕ
  | [], _ => 0
  | operation :: tail, digits => operation.cost digits + runCost tail (operation.apply digits)

theorem run_amortized (operations : List Operation) (digits : List Digit) :
    runCost operations digits + potential 0 (run operations digits) ≤
      7 * operations.length + potential 0 digits := by
  induction operations generalizing digits with
  | nil => simp [run, runCost]
  | cons operation tail ih =>
      have rest := ih (operation.apply digits)
      have localBound : operation.cost digits + potential 0 (operation.apply digits) ≤
          potential 0 digits + 7 := by
        cases operation with
        | push => exact push_amortized 0 digits
        | pop => exact pop_amortized 0 digits
      simp only [run, runCost, List.length_cons]
      omega

/-- Actual class work is linear in the operation count, with a linear
initialization allowance for a nonempty initial stack. -/
theorem runCost_le (operations : List Operation) (digits : List Digit) :
    runCost operations digits ≤ 7 * operations.length + 4 * value digits := by
  have amortized := run_amortized operations digits
  have initial := potential_le_value 0 digits
  omega

end Splay.Accounting.OfflineNormalForm.RibStack.Digits
