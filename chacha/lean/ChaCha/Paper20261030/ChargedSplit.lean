import ChaCha.Paper20261030.ChargedWeightedJoin
import ChaCha.Paper20261030.ChargedRearrangements
import ChaCha.Paper20261030.SharpSplit

/-!
# Logarithmic splitting with charged record operations

The pivot is found by comparisons with records observed on the search
path. Recursive joins include all cached-size updates and bounded local
observations. The size-sensitive join estimate telescopes on the two
outputs, retaining a logarithmic bound after accounting for these costs.
-/

namespace ChaCha.Paper20261030.Auxiliary.Metadata

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ChaCha.MTR

variable {α : Type*} {β : α → Type*}

theorem link_charged_right_rank_budget (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) (horder : l.size ≤ delta * r.size) :
    ObservedRearranges (bin k v l r) (link k v l r hl hr).impl
      (990 * Nat.clog 2 (l.size + r.size + 2) + 76 - 990 * Nat.log 2 (l.size + 1)) := by
  intro ancestors
  obtain ⟨reads,cost,trace,hcost⟩ := link_charged_right_rank (l.size + 1 + r.size)
    k v l r hl hr horder ancestors
  exact ⟨reads,cost,trace,by omega⟩

theorem link_charged_left_rank_budget (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) (horder : r.size ≤ delta * l.size) :
    ObservedRearranges (bin k v l r) (link k v l r hl hr).impl
      (990 * Nat.clog 2 (l.size + r.size + 2) + 76 - 990 * Nat.log 2 (r.size + 1)) := by
  intro ancestors
  obtain ⟨reads,cost,trace,hcost⟩ := link_charged_left_rank (l.size + 1 + r.size)
    k v l r hl hr horder ancestors
  exact ⟨reads,cost,trace,by omega⟩

theorem charged_rank_telescope (a b : Nat) (hab : a ≤ b) :
    990 * Nat.clog 2 a + (990 * Nat.clog 2 b + 76 - 990 * Nat.log 2 a) ≤
      990 * Nat.clog 2 b + 1066 := by
  have hg := log_rounding a
  have hm := (Nat.log_le_clog 2 a).trans (Nat.clog_monotone 2 hab)
  omega

theorem splitAt_charged_rank [Ord α] [LawfulEqOrd α] (x : α) (t : Impl α β)
    (ht : t.Balanced) (hf : searchResult x t = true) :
    ObservedRearranges t (splitAt x t ht hf).impl
      (990 * (Nat.clog 2 ((splitAt x t ht hf).left.size + 1) +
        Nat.clog 2 ((splitAt x t ht hf).right.size + 1)) + 1250 * height t) := by
  induction t with
  | leaf => simp [searchResult] at hf
  | inner sz k v l r ihl ihr =>
    have hbin : bin k v l r = .inner sz k v l r := by
      have hs := ht.eq
      simp only [bin,hs]
    have inspected : ObservedRearranges (.inner sz k v l r) (.inner sz k v l r) 75 := by
      intro ancestors
      obtain ⟨cost,trace,hcost⟩ := snapshot_charged (.inner sz k v l r) ancestors
      exact ⟨_,cost,trace,hcost⟩
    cases hc : compare x k with
    | eq =>
      have heq : (splitAt x (.inner sz k v l r) ht hf).impl = .inner sz k v l r := by
        have hx := compare_eq_iff_eq.mp hc
        subst x
        rw [splitAt]
        split <;> rename_i hb <;> simp at hb
        simpa only [SplitResult.impl,cast_eq] using hbin
      rw [heq]
      exact inspected.mono (by simp only [height]; omega)
    | lt =>
      have fl : searchResult x l = true := by simpa [searchResult,hc] using hf
      let s := splitAt x l ht.left fl
      let d := link k v s.right r s.right_balanced ht.right
      have ss : s.left.size + 1 + s.right.size = l.size := splitAt_size x l ht.left fl
      have ho := split_join_order l.size r.size s.right.size ht.at_root (by omega)
      have hlne : l ≠ .leaf := by cases l <;> simp_all [searchResult]
      have hsz : l.size = s.impl.size := by
        change l.size = s.left.size + 1 + s.right.size
        omega
      have first := (ihl ht.left fl).bin_left (k := k) (v := v) (r := r) hlne hsz
      have turn := singleR_observed k v x s.value s.left s.right r
      have hjoin : (bin k v s.right r).size = d.impl.size := by
        have hd := d.size_impl
        change s.right.size + 1 + r.size = d.impl.size
        omega
      have join := (link_charged_right_rank_budget k v s.right r s.right_balanced ht.right ho).bin_right
        (l := s.left) (k := x) (v := s.value) (by simp [bin]) hjoin
      have body := (first.trans turn).trans join
      rw [hbin] at body
      have all := inspected.trans body
      have hout : splitAt x (.inner sz k v l r) ht hf =
          ⟨s.value,s.left,d.impl,s.left_balanced,d.balanced_impl⟩ := by
        rw [splitAt]
        split <;> rename_i hb <;> simp [hc] at hb
        rfl
      rw [hout]
      apply all.mono
      have hj : d.impl.size + 1 = s.right.size + r.size + 2 := by have := d.size_impl; omega
      have hcst := charged_rank_telescope (s.right.size + 1) (s.right.size + r.size + 2) (by omega)
      have hmul := Nat.mul_le_mul_left 1250 (Nat.le_max_left (height l) (height r))
      change _ ≤ 990 * (Nat.clog 2 (s.left.size + 1) + Nat.clog 2 (d.impl.size + 1)) +
        1250 * height (.inner sz k v l r)
      simp only [hj,height,Nat.mul_add,Nat.mul_one]
      dsimp only [s] at hcst ⊢
      omega
    | gt =>
      have fr : searchResult x r = true := by simpa [searchResult,hc] using hf
      let s := splitAt x r ht.right fr
      let d := link k v l s.left ht.left s.left_balanced
      have ss : s.left.size + 1 + s.right.size = r.size := splitAt_size x r ht.right fr
      have ho := split_join_order r.size l.size s.left.size ht.at_root.symm (by omega)
      have hrne : r ≠ .leaf := by cases r <;> simp_all [searchResult]
      have hsz : r.size = s.impl.size := by
        change r.size = s.left.size + 1 + s.right.size
        omega
      have first := (ihr ht.right fr).bin_right (l := l) (k := k) (v := v) hrne hsz
      have turn := singleL_observed k v l x s.value s.left s.right
      have hjoin : (bin k v l s.left).size = d.impl.size := by
        have hd := d.size_impl
        change l.size + 1 + s.left.size = d.impl.size
        omega
      have join := (link_charged_left_rank_budget k v l s.left ht.left s.left_balanced ho).bin_left
        (r := s.right) (k := x) (v := s.value) (by simp [bin]) hjoin
      have body := (first.trans turn).trans join
      rw [hbin] at body
      have all := inspected.trans body
      have hout : splitAt x (.inner sz k v l r) ht hf =
          ⟨s.value,d.impl,s.right,d.balanced_impl,s.right_balanced⟩ := by
        rw [splitAt]
        split <;> rename_i hb <;> simp [hc] at hb
        rfl
      rw [hout]
      apply all.mono
      have hj : d.impl.size + 1 = l.size + s.left.size + 2 := by have := d.size_impl; omega
      have hcst := charged_rank_telescope (s.left.size + 1) (l.size + s.left.size + 2) (by omega)
      have hmul := Nat.mul_le_mul_left 1250 (Nat.le_max_right (height l) (height r))
      change _ ≤ 990 * (Nat.clog 2 (d.impl.size + 1) + Nat.clog 2 (s.right.size + 1)) +
        1250 * height (.inner sz k v l r)
      simp only [hj,height,Nat.mul_add,Nat.mul_one]
      dsimp only [s] at hcst ⊢
      omega

/-- Successful split exposes the requested key at the root, with balanced
outputs, with logarithmically many moves, rotations, record reads, and cache writes. -/
theorem splitAt_charged_log [Ord α] [LawfulEqOrd α] (x : α) (t : Impl α β)
    (ht : t.Balanced) (hf : searchResult x t = true) :
    ObservedRearranges t (splitAt x t ht hf).impl
      (5730 * Nat.clog 2 (t.size + 1)) := by
  apply (splitAt_charged_rank x t ht hf).mono
  have hs := splitAt_size x t ht hf
  have hh := balanced_height_log ht
  have hl := Nat.clog_monotone 2
    (show (splitAt x t ht hf).left.size + 1 ≤ t.size + 1 by omega)
  have hr := Nat.clog_monotone 2
    (show (splitAt x t ht hf).right.size + 1 ≤ t.size + 1 by omega)
  omega

end ChaCha.Paper20261030.Auxiliary.Metadata
