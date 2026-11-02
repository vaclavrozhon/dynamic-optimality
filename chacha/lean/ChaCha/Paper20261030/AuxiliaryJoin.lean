import ChaCha.Paper20261030.AuxiliaryInsertion

/-!
# Joining two actual balanced trees around their separator

The input is the ordinary tree with the separator at its root and the two
balanced trees as children. Every recursive library join is implemented
by one rotation, a child excursion, and the verified local rebalance.
The resulting pointer cost is logarithmic in the sizes of the inputs.
-/

namespace ChaCha.Paper20261030.Auxiliary

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ChaCha.MTR ChaCha.MTR.Pointer

variable {α : Type*} {β : α → Type*}

theorem join_balance_precond (a b c s : Nat) (ha : 1 ≤ a)
    (hs : s = b + 1 + c) (hb : BalancedAtRoot b c) (hbig : delta * a < s) :
    BalanceLErasePrecond (a + 1 + b) c := by
  simp only [BalanceLErasePrecond,BalancedAtRoot,delta] at *
  omega

theorem link_pointer (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) :
    Rearranges (erase (bin k v l r)) (erase (link k v l r hl hr).impl)
      (7 * (height l + height r)) := by
  cases l with
  | leaf =>
    simpa only [link,height,Nat.zero_add] using insertMin_pointer k v r hr
  | inner sl lk lv ll lr =>
    cases r with
    | leaf =>
      simpa only [link,height,Nat.add_zero] using insertMax_pointer k v (.inner sl lk lv ll lr) hl
    | inner sr rk rv rl rr =>
      by_cases hright : delta * sl < sr
      · let d := link k v (.inner sl lk lv ll lr) rl hl hr.left
        have hp : BalanceLErasePrecond d.impl.size rr.size := by
          rw [d.size_impl]
          exact join_balance_precond _ _ _ _ hl.one_le hr.eq hr.at_root hright
        have hout : (link k v (.inner sl lk lv ll lr) (.inner sr rk rv rl rr) hl hr).impl =
            balanceLErase rk rv d.impl rr d.balanced_impl hr.right hp := by
          rw [link,dif_pos hright]
        intro ancestors
        obtain ⟨cost,trace,hcost⟩ := link_pointer k v (.inner sl lk lv ll lr) rl hl hr.left
          (.left rk (erase rr) :: ancestors)
        obtain ⟨bc,bt,hbc⟩ := balanceLErase_pointer rk rv d.impl rr d.balanced_impl hr.right hp ancestors
        have up := Trace.step (Step.upLeft (erase d.impl) (erase rr) rk ancestors) (Trace.nil _)
        have tail := trace_append trace (trace_append up bt)
        have full := Trace.step
          (Step.rotateLeft (erase (.inner sl lk lv ll lr)) (erase rl) (erase rr) k rk ancestors)
          (Trace.step (Step.left (erase (.inner sl lk lv ll lr)) (erase rl) (erase rr) k rk ancestors) tail)
        refine ⟨cost + bc + 3,?_,?_⟩
        · rw [hout]
          simpa only [erase,bin,List.nil_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
            Nat.zero_add,Nat.reduceAdd] using full
        · simp only [height] at hcost ⊢
          omega
      · by_cases hleft : delta * sr < sl
        · let d := link k v lr (.inner sr rk rv rl rr) hl.right hr
          have hp : BalanceLErasePrecond d.impl.size ll.size := by
            rw [d.size_impl]
            have hs : sl = lr.size + 1 + ll.size := by have := hl.eq; omega
            have hb := join_balance_precond _ _ _ _ hr.one_le hs hl.at_root.symm hleft
            simpa [Impl.size_inner,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb
          have hout : (link k v (.inner sl lk lv ll lr) (.inner sr rk rv rl rr) hl hr).impl =
              balanceRErase lk lv ll d.impl hl.left d.balanced_impl hp := by
            rw [link,dif_neg hright,dif_pos hleft]
          intro ancestors
          obtain ⟨cost,trace,hcost⟩ := link_pointer k v lr (.inner sr rk rv rl rr) hl.right hr
            (.right (erase ll) lk :: ancestors)
          obtain ⟨bc,bt,hbc⟩ := balanceRErase_pointer lk lv ll d.impl hl.left d.balanced_impl hp ancestors
          have up := Trace.step (Step.upRight (erase ll) (erase d.impl) lk ancestors) (Trace.nil _)
          have tail := trace_append trace (trace_append up bt)
          have full := Trace.step
            (Step.rotateRight (erase ll) (erase lr) (erase (.inner sr rk rv rl rr)) lk k ancestors)
            (Trace.step (Step.right (erase ll) (erase lr) (erase (.inner sr rk rv rl rr)) lk k ancestors) tail)
          refine ⟨cost + bc + 3,?_,?_⟩
          · rw [hout]
            simpa only [erase,bin,List.nil_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
              Nat.zero_add,Nat.reduceAdd] using full
          · simp only [height] at hcost ⊢
            omega
        · rw [link,dif_neg hright,dif_neg hleft]
          exact rearranges_refl _ _
termination_by sizeOf l + sizeOf r

theorem link_pointer_log (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) :
    Rearranges (erase (bin k v l r)) (erase (link k v l r hl hr).impl)
      (21 * (Nat.clog 2 (l.size + 1) + Nat.clog 2 (r.size + 1))) := by
  intro ancestors
  obtain ⟨cost,trace,hcost⟩ := link_pointer k v l r hl hr ancestors
  refine ⟨cost,trace,?_⟩
  have hleft := balanced_height_log hl
  have hright := balanced_height_log hr
  omega

end ChaCha.Paper20261030.Auxiliary
