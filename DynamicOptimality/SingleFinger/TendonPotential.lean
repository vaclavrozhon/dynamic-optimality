import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-! Potential for joining tendons after pointer reassignment.

For tendon lengths `lengths`, `pairPotential lengths` is the sum, over
unordered pairs of tendons, of the smaller length. Joining lengths `a` and
`b` releases at least `min a b` units. Thus transferring the smaller tendon
can be paid for even when both endpoint deques were balanced before a copy.
Growing a tendon by one increases the potential by at most the number of
other tendons. This arithmetic lemma does not assert a simulator or a
constant-time catenation operation.
-/

namespace DynamicOptimality.SingleFinger.TendonPotential

def minSum (length : Nat) : List Nat → Nat
  | [] => 0
  | other::rest => min length other + minSum length rest

def pairPotential : List Nat → Nat
  | [] => 0
  | length::rest => minSum length rest + pairPotential rest

theorem minSum_perm (length : Nat) {first last : List Nat} (same : first.Perm last) :
    minSum length first = minSum length last := by
  induction same with
  | nil => rfl
  | cons entry same ih => simp only [minSum,ih]
  | swap a b rest => simp only [minSum]; omega
  | trans first last ihfirst ihlast => exact ihfirst.trans ihlast

theorem pairPotential_perm {first last : List Nat} (same : first.Perm last) :
    pairPotential first = pairPotential last := by
  induction same with
  | nil => rfl
  | cons entry same ih => simp only [pairPotential,minSum_perm entry same,ih]
  | swap a b rest => simp only [pairPotential,minSum,Nat.min_comm]; omega
  | trans first last ihfirst ihlast => exact ihfirst.trans ihlast

theorem minSum_subadditive (a b : Nat) (rest : List Nat) :
    minSum (a+b) rest ≤ minSum a rest + minSum b rest := by
  induction rest with
  | nil => simp [minSum]
  | cons other rest ih =>
    have : min (a+b) other ≤ min a other + min b other := by omega
    simp only [minSum]
    omega

/-- Copy-induced joining releases the cost of transferring the smaller
logical tendon, independently of all the other tendon lengths. -/
theorem merge_releases (a b : Nat) (rest : List Nat) :
    pairPotential ((a+b)::rest) + min a b ≤ pairPotential (a::b::rest) := by
  have bound := minSum_subadditive a b rest
  simp only [pairPotential,minSum]
  omega

theorem minSum_increment (a : Nat) (rest : List Nat) :
    minSum (a+1) rest ≤ minSum a rest + rest.length := by
  induction rest with
  | nil => simp [minSum]
  | cons other rest ih =>
    have : min (a+1) other ≤ min a other + 1 := by omega
    simp only [minSum,List.length_cons]
    omega

theorem grow_one (a : Nat) (rest : List Nat) :
    pairPotential ((a+1)::rest) ≤ pairPotential (a::rest) + rest.length := by
  have := minSum_increment a rest
  simp only [pairPotential]
  omega

/-- Removing a marked separator joins its two adjacent tendons and adds
that separator itself to the joined path. This extra vertex costs only one
unit per remaining tendon in the pair potential. -/
theorem merge_separator (a b : Nat) (rest : List Nat) :
    pairPotential ((a+b+1)::rest) + min a b ≤
      pairPotential (a::b::rest) + rest.length := by
  have joined := merge_releases a b rest
  have inserted := grow_one (a+b) rest
  omega

theorem minSum_mono {a b : Nat} (less : a ≤ b) (rest : List Nat) :
    minSum a rest ≤ minSum b rest := by
  induction rest with
  | nil => exact le_rfl
  | cons other rest ih =>
    have : min a other ≤ min b other := by omega
    simp only [minSum]
    omega

theorem shrink_one (a : Nat) (rest : List Nat) :
    pairPotential (a::rest) ≤ pairPotential ((a+1)::rest) := by
  have := minSum_mono (a := a) (b := a+1) (by omega) rest
  simp only [pairPotential]
  omega

theorem remove (a : Nat) (rest : List Nat) :
    pairPotential rest ≤ pairPotential (a::rest) := by simp [pairPotential]

theorem minSum_bound (a : Nat) (rest : List Nat) : minSum a rest ≤ a*rest.length := by
  induction rest with
  | nil => simp [minSum]
  | cons other rest ih =>
    have : min a other ≤ a := Nat.min_le_left _ _
    simp only [minSum,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem insert_short {a bound : Nat} (short : a ≤ bound) (rest : List Nat) :
    pairPotential (a::rest) ≤ pairPotential rest + bound*rest.length := by
  have := (minSum_bound a rest).trans (Nat.mul_le_mul_right rest.length short)
  simp only [pairPotential]
  omega

@[simp] theorem minSum_zero (rest : List Nat) : minSum 0 rest = 0 := by
  induction rest <;> simp [minSum, *]

@[simp] theorem insert_zero (rest : List Nat) : pairPotential (0::rest) = pairPotential rest := by
  simp [pairPotential]

/-- All initial fingers coincide, so an empty collection of tendon queues
has zero potential; no initial reconstruction allowance is hidden here. -/
@[simp] theorem initial_zero : pairPotential [] = 0 := rfl

end DynamicOptimality.SingleFinger.TendonPotential
