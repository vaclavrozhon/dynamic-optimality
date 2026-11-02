import ChaCha.Paper20261030.AuxiliarySplit
import ChaCha.Paper20261030.WeightedJoin

/-!
# Logarithmic pointer cost of splitting the actual balanced tree

The two output subtree sizes provide the accounting terms. On each return
from recursion, only one output grows. The size-sensitive join bound
charges that growth, up to one unit for rounding the logarithm. This
telescopes across the search path and gives a logarithmic total cost.
-/

namespace ChaCha.Paper20261030.Auxiliary

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ChaCha.MTR ChaCha.MTR.Pointer

variable {α : Type*} {β : α → Type*}

theorem split_join_order (a b c : Nat) (hb : BalancedAtRoot a b) (hc : c + 1 ≤ a) :
    c ≤ delta * b := by
  simp only [BalancedAtRoot,delta] at *
  omega

theorem log_rounding (a : Nat) : Nat.clog 2 a ≤ Nat.log 2 a + 1 :=
  Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) a))

theorem rank_telescope (a b : Nat) (hab : a ≤ b) :
    42 * Nat.clog 2 a + (42 * Nat.clog 2 b - 42 * Nat.log 2 a) ≤
      42 * Nat.clog 2 b + 42 := by
  have hg := log_rounding a
  have hm := (Nat.log_le_clog 2 a).trans (Nat.clog_monotone 2 hab)
  omega

theorem splitAt_pointer_rank [Ord α] [LawfulEqOrd α] (x : α) (t : Impl α β)
    (ht : t.Balanced) (hf : searchResult x t = true) :
    Rearranges (erase t) (erase (splitAt x t ht hf).impl)
      (42 * (Nat.clog 2 ((splitAt x t ht hf).left.size + 1) +
        Nat.clog 2 ((splitAt x t ht hf).right.size + 1)) + 50 * height t) := by
  induction t with
  | leaf => simp [searchResult] at hf
  | inner sz k v l r ihl ihr =>
    cases hc : compare x k with
    | eq =>
      rw [splitAt_root_tree x ht hf hc]
      exact rearranges_refl _ _
    | lt =>
      have fl : searchResult x l = true := by simpa [searchResult,hc] using hf
      let s := splitAt x l ht.left fl
      let d := link k v s.right r s.right_balanced ht.right
      have ss : s.left.size + 1 + s.right.size = l.size := splitAt_size x l ht.left fl
      have ho := split_join_order l.size r.size s.right.size ht.at_root (by omega)
      have hlne : erase l ≠ .empty := by cases l <;> simp_all [erase,searchResult]
      have first := (ihl ht.left fl).left (k := k) (r := erase r) hlne
      have turn := singleR_pointer k v x s.value s.left s.right r
      have join := (link_right_rank_budget k v s.right r s.right_balanced ht.right ho).right
        (l := erase s.left) (k := x) (by simp [erase,bin])
      have all := (first.trans turn).trans join
      have hout : splitAt x (.inner sz k v l r) ht hf =
          ⟨s.value,s.left,d.impl,s.left_balanced,d.balanced_impl⟩ := by
        rw [splitAt]
        split <;> rename_i hb <;> simp [hc] at hb
        rfl
      rw [hout]
      apply all.mono
      have hj : d.impl.size + 1 = s.right.size + r.size + 2 := by have := d.size_impl; omega
      have hcst := rank_telescope (s.right.size + 1) (s.right.size + r.size + 2) (by omega)
      have hmul := Nat.mul_le_mul_left 50 (Nat.le_max_left (height l) (height r))
      change _ ≤ 42 * (Nat.clog 2 (s.left.size + 1) + Nat.clog 2 (d.impl.size + 1)) +
        50 * height (.inner sz k v l r)
      simp only [hj,height,Nat.mul_add,Nat.mul_one]
      dsimp only [s] at hcst ⊢
      omega
    | gt =>
      have fr : searchResult x r = true := by simpa [searchResult,hc] using hf
      let s := splitAt x r ht.right fr
      let d := link k v l s.left ht.left s.left_balanced
      have ss : s.left.size + 1 + s.right.size = r.size := splitAt_size x r ht.right fr
      have ho := split_join_order r.size l.size s.left.size ht.at_root.symm (by omega)
      have hrne : erase r ≠ .empty := by cases r <;> simp_all [erase,searchResult]
      have first := (ihr ht.right fr).right (l := erase l) (k := k) hrne
      have turn := singleL_pointer k v l x s.value s.left s.right
      have join := (link_left_rank_budget k v l s.left ht.left s.left_balanced ho).left
        (r := erase s.right) (k := x) (by simp [erase,bin])
      have all := (first.trans turn).trans join
      have hout : splitAt x (.inner sz k v l r) ht hf =
          ⟨s.value,d.impl,s.right,d.balanced_impl,s.right_balanced⟩ := by
        rw [splitAt]
        split <;> rename_i hb <;> simp [hc] at hb
        rfl
      rw [hout]
      apply all.mono
      have hj : d.impl.size + 1 = l.size + s.left.size + 2 := by have := d.size_impl; omega
      have hcst := rank_telescope (s.left.size + 1) (l.size + s.left.size + 2) (by omega)
      have hmul := Nat.mul_le_mul_left 50 (Nat.le_max_right (height l) (height r))
      change _ ≤ 42 * (Nat.clog 2 (d.impl.size + 1) + Nat.clog 2 (s.right.size + 1)) +
        50 * height (.inner sz k v l r)
      simp only [hj,height,Nat.mul_add,Nat.mul_one]
      dsimp only [s] at hcst ⊢
      omega

/-- Successful split exposes the requested key at the root, with balanced
outputs, using only logarithmically many actual moves and rotations. -/
theorem splitAt_pointer_log [Ord α] [LawfulEqOrd α] (x : α) (t : Impl α β)
    (ht : t.Balanced) (hf : searchResult x t = true) :
    Rearranges (erase t) (erase (splitAt x t ht hf).impl)
      (234 * Nat.clog 2 (t.size + 1)) := by
  apply (splitAt_pointer_rank x t ht hf).mono
  have hs := splitAt_size x t ht hf
  have hh := balanced_height_log ht
  have hl := Nat.clog_monotone 2
    (show (splitAt x t ht hf).left.size + 1 ≤ t.size + 1 by omega)
  have hr := Nat.clog_monotone 2
    (show (splitAt x t ht hf).right.size + 1 ≤ t.size + 1 by omega)
  omega

end ChaCha.Paper20261030.Auxiliary
