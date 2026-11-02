import Std.Data.DTreeMap.Internal.Operations
import Std.Data.DTreeMap.Internal.Queries
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith

/-!
# Reusing the standard library's verified balanced auxiliary trees

Lean's `DTreeMap.Internal.Impl` stores subtree sizes and uses size balance
with ratio three. We reuse that concrete invariant and its proved
maintenance operations. The additional bounds below concern the actual
tree height and the number of visited records in the actual search.
They do not yet assert a BST simulation of split or join.
-/

namespace ChaCha.Paper20261030.Auxiliary

open Std.DTreeMap.Internal
open Std.DTreeMap.Internal.Impl

variable {α : Type*} {β : α → Type*}

def height : Impl α β → Nat
  | .leaf => 0
  | .inner _ _ _ l r => max (height l) (height r) + 1

theorem child_weight_bound {sz : Nat} {k : α} {v : β k} {l r : Impl α β}
    (h : (Impl.inner sz k v l r).Balanced) :
    4 * (l.size + 1) ≤ 3 * (sz + 1) ∧ 4 * (r.size + 1) ≤ 3 * (sz + 1) := by
  obtain ⟨hl,hr,hroot,hsize⟩ := balanced_inner_iff.mp h
  simp only [BalancedAtRoot,delta] at hroot
  omega

theorem cube_weight (a b : Nat) (h : 4 * a ≤ 3 * b) : 2 * a ^ 3 ≤ b ^ 3 := by
  have hc : (4 * a) ^ 3 ≤ (3 * b) ^ 3 := Nat.pow_le_pow_left h 3
  nlinarith [Nat.zero_le (b ^ 3)]

/-- A cubic size bound suffices for a constant-factor binary logarithm. -/
theorem balanced_height_power {t : Impl α β} (h : t.Balanced) :
    2 ^ height t ≤ (t.size + 1) ^ 3 := by
  induction h with
  | leaf => simp [height,Impl.size]
  | @inner sz k v l r hl hr hroot hsize ihl ihr =>
    have hw := child_weight_bound (k := k) (v := v) (Balanced.inner hl hr hroot hsize)
    have hcl := cube_weight (l.size + 1) (sz + 1) hw.1
    have hcr := cube_weight (r.size + 1) (sz + 1) hw.2
    rcases le_total (height l) (height r) with hh | hh
    · simp only [height,max_eq_right hh,Impl.size]
      rw [pow_succ]
      omega
    · simp only [height,max_eq_left hh,Impl.size]
      rw [pow_succ]
      omega

/-- The proved invariant gives logarithmic height for the actual library
tree, with no supplied height or complexity hypothesis. -/
theorem balanced_height_log {t : Impl α β} (h : t.Balanced) :
    height t ≤ 3 * Nat.clog 2 (t.size + 1) := by
  have hp := balanced_height_power h
  have hw := Nat.le_pow_clog (by decide : 1 < 2) (t.size + 1)
  have hc : (t.size + 1) ^ 3 ≤ (2 ^ Nat.clog 2 (t.size + 1)) ^ 3 := Nat.pow_le_pow_left hw 3
  rw [← pow_mul,Nat.mul_comm (Nat.clog 2 (t.size + 1)) 3] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hp.trans hc)

/-- The number of inspected records in the standard search, including the
matching record and excluding an empty child. -/
def searchVisits [Ord α] (x : α) : Impl α β → Nat
  | .leaf => 0
  | .inner _ k _ l r =>
      match compare x k with
      | .lt => searchVisits x l + 1
      | .eq => 1
      | .gt => searchVisits x r + 1

def searchResult [Ord α] (x : α) : Impl α β → Bool
  | .leaf => false
  | .inner _ k _ l r =>
      match compare x k with
      | .lt => searchResult x l
      | .eq => true
      | .gt => searchResult x r

theorem searchResult_eq_contains [Ord α] (x : α) (t : Impl α β) :
    searchResult x t = t.contains x := by
  induction t with
  | leaf => rfl
  | inner sz k v l r ihl ihr =>
    simp only [searchResult,Impl.contains,ihl,ihr]
    cases compare x k <;> rfl

theorem searchVisits_height [Ord α] (x : α) (t : Impl α β) : searchVisits x t ≤ height t := by
  induction t with
  | leaf => rfl
  | inner sz k v l r ihl ihr =>
    simp only [searchVisits,height]
    split <;> omega

theorem searchVisits_log [Ord α] (x : α) {t : Impl α β} (h : t.Balanced) :
    searchVisits x t ≤ 3 * Nat.clog 2 (t.size + 1) :=
  (searchVisits_height x t).trans (balanced_height_log h)

end ChaCha.Paper20261030.Auxiliary
