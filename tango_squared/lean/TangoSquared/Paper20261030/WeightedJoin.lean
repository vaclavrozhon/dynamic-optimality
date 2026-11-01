import TangoSquared.Paper20261030.JoinWeights

/-!
# Size-sensitive pointer cost of joining balanced trees

When the left input is at most three times the right input, all recursive
descent takes place in the right input. The bound retains the left weight
so that successive joins during splitting can telescope.
-/

namespace TangoSquared.Paper20261030.Auxiliary

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open TangoSquared.MTR TangoSquared.MTR.Pointer

variable {α : Type*} {β : α → Type*}

theorem link_right_weighted (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) (horder : l.size ≤ delta * r.size) :
    ∃ steps, Rearranges (erase (bin k v l r)) (erase (link k v l r hl hr).impl) (7 * steps) ∧
      2 ^ steps * (l.size + 1) ^ 6 ≤ (l.size + r.size + 2) ^ 6 := by
  cases l with
  | leaf =>
    refine ⟨height r,?_,?_⟩
    · simpa only [link] using insertMin_pointer k v r hr
    · have hh := balanced_height_power hr
      have hm : (r.size + 1) ^ 3 ≤ (r.size + 2) ^ 6 :=
        (Nat.pow_le_pow_left (by omega : r.size + 1 ≤ r.size + 2) 3).trans
          (Nat.pow_le_pow_right (by omega : 0 < r.size + 2) (by decide : 3 ≤ 6))
      simpa only [Impl.size_leaf,Nat.zero_add,one_pow,Nat.mul_one] using hh.trans hm
  | inner sl lk lv ll lr =>
    cases r with
    | leaf =>
      have hp := hl.one_le
      simp only [Impl.size_leaf,Impl.size_inner,Nat.mul_zero] at horder
      omega
    | inner sr rk rv rl rr =>
      by_cases hright : delta * sl < sr
      · have hd := join_weight_decay sl rl.size rr.size sr hl.one_le hr.eq hr.at_root hright
        obtain ⟨steps,route,hpower⟩ := link_right_weighted k v (.inner sl lk lv ll lr) rl hl hr.left hd.1
        let d := link k v (.inner sl lk lv ll lr) rl hl hr.left
        have hp : BalanceLErasePrecond d.impl.size rr.size := by
          rw [d.size_impl]
          exact join_balance_precond _ _ _ _ hl.one_le hr.eq hr.at_root hright
        have hout : (link k v (.inner sl lk lv ll lr) (.inner sr rk rv rl rr) hl hr).impl =
            balanceLErase rk rv d.impl rr d.balanced_impl hr.right hp := by
          rw [link,dif_pos hright]
        refine ⟨steps + 1,?_,?_⟩
        · intro ancestors
          obtain ⟨cost,trace,hcost⟩ := route (.left rk (erase rr) :: ancestors)
          obtain ⟨bc,bt,hbc⟩ := balanceLErase_pointer rk rv d.impl rr d.balanced_impl hr.right hp ancestors
          have up := Trace.step (Step.upLeft (erase d.impl) (erase rr) rk ancestors) (Trace.nil _)
          have tail := trace_append trace (trace_append up bt)
          have full := Trace.step
            (Step.rotateLeft (erase (.inner sl lk lv ll lr)) (erase rl) (erase rr) k rk ancestors)
            (Trace.step (Step.left (erase (.inner sl lk lv ll lr)) (erase rl) (erase rr) k rk ancestors) tail)
          refine ⟨cost + bc + 3,?_,by omega⟩
          rw [hout]
          simpa only [erase,bin,List.nil_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
            Nat.zero_add,Nat.reduceAdd] using full
        · have hc := sixth_weight _ _ hd.2
          simp only [Impl.size_inner] at hpower ⊢
          calc
            2 ^ (steps + 1) * (sl + 1) ^ 6 = 2 * (2 ^ steps * (sl + 1) ^ 6) := by
              simp [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
            _ ≤ 2 * (sl + rl.size + 2) ^ 6 := Nat.mul_le_mul_left 2 hpower
            _ ≤ (sl + sr + 2) ^ 6 := hc
      · have hleft : ¬ delta * sr < sl := by
          simp only [Impl.size_inner] at horder
          omega
        refine ⟨0,?_,?_⟩
        · rw [link,dif_neg hright,dif_neg hleft]
          exact rearranges_refl _ _
        · simp only [pow_zero,one_mul]
          exact Nat.pow_le_pow_left (by omega) 6
termination_by sizeOf l + sizeOf r

theorem link_right_rank (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) (horder : l.size ≤ delta * r.size)
    (ancestors : List (Frame α)) :
    ∃ cost, Trace ⟨erase (bin k v l r),ancestors⟩ []
        ⟨erase (link k v l r hl hr).impl,ancestors⟩ cost ∧
      cost + 42 * Nat.log 2 (l.size + 1) ≤ 42 * Nat.clog 2 (l.size + r.size + 2) := by
  obtain ⟨steps,route,hpower⟩ := link_right_weighted k v l r hl hr horder
  obtain ⟨cost,trace,hcost⟩ := route ancestors
  refine ⟨cost,trace,?_⟩
  have hh := weight_steps_log (by omega : l.size + 1 ≠ 0) hpower
  omega

theorem link_left_weighted (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) (horder : r.size ≤ delta * l.size) :
    ∃ steps, Rearranges (erase (bin k v l r)) (erase (link k v l r hl hr).impl) (7 * steps) ∧
      2 ^ steps * (r.size + 1) ^ 6 ≤ (l.size + r.size + 2) ^ 6 := by
  cases r with
  | leaf =>
    refine ⟨height l,?_,?_⟩
    · cases l with
      | leaf =>
        simpa only [link,insertMin,erase,bin,height,Nat.mul_zero] using
          rearranges_refl (MTR.Tree.node .empty k .empty) 0
      | inner sz k' v' l' r' => simpa only [link] using insertMax_pointer k v (.inner sz k' v' l' r') hl
    · have hh := balanced_height_power hl
      have hm : (l.size + 1) ^ 3 ≤ (l.size + 2) ^ 6 :=
        (Nat.pow_le_pow_left (by omega : l.size + 1 ≤ l.size + 2) 3).trans
          (Nat.pow_le_pow_right (by omega : 0 < l.size + 2) (by decide : 3 ≤ 6))
      simpa only [Impl.size_leaf,Nat.add_zero,Nat.zero_add,one_pow,Nat.mul_one] using hh.trans hm
  | inner sr rk rv rl rr =>
    cases l with
    | leaf =>
      have hp := hr.one_le
      simp only [Impl.size_leaf,Impl.size_inner,Nat.mul_zero] at horder
      omega
    | inner sl lk lv ll lr =>
      have hright : ¬ delta * sl < sr := by
        simp only [Impl.size_inner] at horder
        omega
      by_cases hleft : delta * sr < sl
      · have hs : sl = lr.size + 1 + ll.size := by have := hl.eq; omega
        have hd := join_weight_decay sr lr.size ll.size sl hr.one_le hs hl.at_root.symm hleft
        obtain ⟨steps,route,hpower⟩ := link_left_weighted k v lr (.inner sr rk rv rl rr) hl.right hr hd.1
        let d := link k v lr (.inner sr rk rv rl rr) hl.right hr
        have hp : BalanceLErasePrecond d.impl.size ll.size := by
          rw [d.size_impl]
          have hb := join_balance_precond _ _ _ _ hr.one_le hs hl.at_root.symm hleft
          simpa [Impl.size_inner,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb
        have hout : (link k v (.inner sl lk lv ll lr) (.inner sr rk rv rl rr) hl hr).impl =
            balanceRErase lk lv ll d.impl hl.left d.balanced_impl hp := by
          rw [link,dif_neg hright,dif_pos hleft]
        refine ⟨steps + 1,?_,?_⟩
        · intro ancestors
          obtain ⟨cost,trace,hcost⟩ := route (.right (erase ll) lk :: ancestors)
          obtain ⟨bc,bt,hbc⟩ := balanceRErase_pointer lk lv ll d.impl hl.left d.balanced_impl hp ancestors
          have up := Trace.step (Step.upRight (erase ll) (erase d.impl) lk ancestors) (Trace.nil _)
          have tail := trace_append trace (trace_append up bt)
          have full := Trace.step
            (Step.rotateRight (erase ll) (erase lr) (erase (.inner sr rk rv rl rr)) lk k ancestors)
            (Trace.step (Step.right (erase ll) (erase lr) (erase (.inner sr rk rv rl rr)) lk k ancestors) tail)
          refine ⟨cost + bc + 3,?_,by omega⟩
          rw [hout]
          simpa only [erase,bin,List.nil_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
            Nat.zero_add,Nat.reduceAdd] using full
        · have hc := sixth_weight _ _ hd.2
          simp only [Impl.size_inner] at hpower ⊢
          calc
            2 ^ (steps + 1) * (sr + 1) ^ 6 = 2 * (2 ^ steps * (sr + 1) ^ 6) := by
              simp [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
            _ ≤ 2 * (lr.size + sr + 2) ^ 6 := Nat.mul_le_mul_left 2 hpower
            _ ≤ (sl + sr + 2) ^ 6 := by simpa [Nat.add_comm] using hc
      · refine ⟨0,?_,?_⟩
        · rw [link,dif_neg hright,dif_neg hleft]
          exact rearranges_refl _ _
        · simp only [pow_zero,one_mul]
          exact Nat.pow_le_pow_left (by omega) 6
termination_by sizeOf l + sizeOf r

theorem link_left_rank (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) (horder : r.size ≤ delta * l.size)
    (ancestors : List (Frame α)) :
    ∃ cost, Trace ⟨erase (bin k v l r),ancestors⟩ []
        ⟨erase (link k v l r hl hr).impl,ancestors⟩ cost ∧
      cost + 42 * Nat.log 2 (r.size + 1) ≤ 42 * Nat.clog 2 (l.size + r.size + 2) := by
  obtain ⟨steps,route,hpower⟩ := link_left_weighted k v l r hl hr horder
  obtain ⟨cost,trace,hcost⟩ := route ancestors
  refine ⟨cost,trace,?_⟩
  have hh := weight_steps_log (by omega : r.size + 1 ≠ 0) hpower
  omega

theorem link_right_rank_budget (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) (horder : l.size ≤ delta * r.size) :
    Rearranges (erase (bin k v l r)) (erase (link k v l r hl hr).impl)
      (42 * Nat.clog 2 (l.size + r.size + 2) - 42 * Nat.log 2 (l.size + 1)) := by
  intro ancestors
  obtain ⟨cost,trace,hcost⟩ := link_right_rank k v l r hl hr horder ancestors
  exact ⟨cost,trace,by omega⟩

theorem link_left_rank_budget (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) (horder : r.size ≤ delta * l.size) :
    Rearranges (erase (bin k v l r)) (erase (link k v l r hl hr).impl)
      (42 * Nat.clog 2 (l.size + r.size + 2) - 42 * Nat.log 2 (r.size + 1)) := by
  intro ancestors
  obtain ⟨cost,trace,hcost⟩ := link_left_rank k v l r hl hr horder ancestors
  exact ⟨cost,trace,by omega⟩

end TangoSquared.Paper20261030.Auxiliary
