import TangoSquared.Paper20261030.ChargedJoin
import TangoSquared.Paper20261030.JoinWeights

/-!
# Size-sensitive join cost including record reads and writes

When the left input is at most three times the right input, all recursive
descent takes place in the right input. The bound retains the left weight
so that successive joins during splitting can telescope.
-/

namespace TangoSquared.Paper20261030.Auxiliary.Metadata

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open TangoSquared.MTR

variable {α : Type*} {β : α → Type*}

theorem link_charged_right_weighted (old : Nat) (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) (horder : l.size ≤ delta * r.size) :
    ∃ steps, ObservedRearranges (.inner old k v l r) (link k v l r hl hr).impl (165 * steps + 76) ∧
      2 ^ steps * (l.size + 1) ^ 6 ≤ (l.size + r.size + 2) ^ 6 := by
  cases l with
  | leaf =>
    refine ⟨height r,?_,?_⟩
    · simpa only [link] using insertMin_charged old k v r hr
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
        obtain ⟨steps,route,hpower⟩ := link_charged_right_weighted old k v (.inner sl lk lv ll lr) rl hl hr.left hd.1
        let d := link k v (.inner sl lk lv ll lr) rl hl hr.left
        have hp : BalanceLErasePrecond d.impl.size rr.size := by
          rw [d.size_impl]
          exact join_balance_precond _ _ _ _ hl.one_le hr.eq hr.at_root hright
        have hout : (link k v (.inner sl lk lv ll lr) (.inner sr rk rv rl rr) hl hr).impl =
            balanceLErase rk rv d.impl rr d.balanced_impl hr.right hp := by
          rw [link,dif_pos hright]
        refine ⟨steps + 1,?_,?_⟩
        · intro ancestors
          obtain ⟨rc,reads,hrc⟩ := snapshot_charged
            (.inner old k v (.inner sl lk lv ll lr) (.inner sr rk rv rl rr)) ancestors
          obtain ⟨word,cost,trace,hcost⟩ := route
            (.left (sr,⟨rk,rv⟩) (recordTree rr) :: ancestors)
          obtain ⟨bc,bt,hbc⟩ := balanceLErase_existing_charged sr rk rv d.impl rr
            d.balanced_impl hr.right hp ancestors
          have up : Trace ⟨recordTree d.impl,.left (sr,⟨rk,rv⟩) (recordTree rr) :: ancestors⟩ []
              ⟨recordTree (.inner sr rk rv d.impl rr),ancestors⟩ 1 :=
            .step (.nav (.upLeft (recordTree d.impl) (recordTree rr) (sr,⟨rk,rv⟩) ancestors)) (.nil _)
          have tail := trace.append (up.append bt)
          have full := Trace.step
            (Step.nav (.rotateLeft (recordTree (.inner sl lk lv ll lr)) (recordTree rl) (recordTree rr)
              (old,⟨k,v⟩) (sr,⟨rk,rv⟩) ancestors))
            (Trace.step (Step.nav (.left (recordTree (.inner sl lk lv ll lr)) (recordTree rl) (recordTree rr)
              (old,⟨k,v⟩) (sr,⟨rk,rv⟩) ancestors)) tail)
          rw [hout]
          refine ⟨_,_,reads.append full,?_⟩
          omega
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
          exact refresh_charged old k v _ _
        · simp only [pow_zero,one_mul]
          exact Nat.pow_le_pow_left (by omega) 6
termination_by sizeOf l + sizeOf r

theorem link_charged_right_rank (old : Nat) (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) (horder : l.size ≤ delta * r.size)
    (ancestors : List (Pointer.Frame (NodeRecord α β))) :
    ∃ reads cost, Trace ⟨recordTree (.inner old k v l r),ancestors⟩ reads
        ⟨recordTree (link k v l r hl hr).impl,ancestors⟩ cost ∧
      cost + 990 * Nat.log 2 (l.size + 1) ≤ 990 * Nat.clog 2 (l.size + r.size + 2) + 76 := by
  obtain ⟨steps,route,hpower⟩ := link_charged_right_weighted old k v l r hl hr horder
  obtain ⟨reads,cost,trace,hcost⟩ := route ancestors
  refine ⟨reads,cost,trace,?_⟩
  have hh := weight_steps_log (by omega : l.size + 1 ≠ 0) hpower
  omega

theorem link_charged_left_weighted (old : Nat) (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) (horder : r.size ≤ delta * l.size) :
    ∃ steps, ObservedRearranges (.inner old k v l r) (link k v l r hl hr).impl (165 * steps + 76) ∧
      2 ^ steps * (r.size + 1) ^ 6 ≤ (l.size + r.size + 2) ^ 6 := by
  cases r with
  | leaf =>
    refine ⟨height l,?_,?_⟩
    · cases l with
      | leaf =>
        simpa only [link,insertMin,height,bin,Impl.size_leaf,Nat.mul_zero,Nat.zero_add,Nat.add_zero] using
          refresh_charged old k v .leaf .leaf
      | inner sz k' v' l' r' => simpa only [link] using insertMax_charged old k v (.inner sz k' v' l' r') hl
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
        obtain ⟨steps,route,hpower⟩ := link_charged_left_weighted old k v lr (.inner sr rk rv rl rr) hl.right hr hd.1
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
          obtain ⟨rc,reads,hrc⟩ := snapshot_charged
            (.inner old k v (.inner sl lk lv ll lr) (.inner sr rk rv rl rr)) ancestors
          obtain ⟨word,cost,trace,hcost⟩ := route
            (.right (recordTree ll) (sl,⟨lk,lv⟩) :: ancestors)
          obtain ⟨bc,bt,hbc⟩ := balanceRErase_existing_charged sl lk lv ll d.impl
            hl.left d.balanced_impl hp ancestors
          have up : Trace ⟨recordTree d.impl,.right (recordTree ll) (sl,⟨lk,lv⟩) :: ancestors⟩ []
              ⟨recordTree (.inner sl lk lv ll d.impl),ancestors⟩ 1 :=
            .step (.nav (.upRight (recordTree ll) (recordTree d.impl) (sl,⟨lk,lv⟩) ancestors)) (.nil _)
          have tail := trace.append (up.append bt)
          have full := Trace.step
            (Step.nav (.rotateRight (recordTree ll) (recordTree lr) (recordTree (.inner sr rk rv rl rr))
              (sl,⟨lk,lv⟩) (old,⟨k,v⟩) ancestors))
            (Trace.step (Step.nav (.right (recordTree ll) (recordTree lr) (recordTree (.inner sr rk rv rl rr))
              (sl,⟨lk,lv⟩) (old,⟨k,v⟩) ancestors)) tail)
          rw [hout]
          refine ⟨_,_,reads.append full,?_⟩
          omega
        · have hc := sixth_weight _ _ hd.2
          simp only [Impl.size_inner] at hpower ⊢
          calc
            2 ^ (steps + 1) * (sr + 1) ^ 6 = 2 * (2 ^ steps * (sr + 1) ^ 6) := by
              simp [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
            _ ≤ 2 * (lr.size + sr + 2) ^ 6 := Nat.mul_le_mul_left 2 hpower
            _ ≤ (sl + sr + 2) ^ 6 := by simpa [Nat.add_comm] using hc
      · refine ⟨0,?_,?_⟩
        · rw [link,dif_neg hright,dif_neg hleft]
          exact refresh_charged old k v _ _
        · simp only [pow_zero,one_mul]
          exact Nat.pow_le_pow_left (by omega) 6
termination_by sizeOf l + sizeOf r

theorem link_charged_left_rank (old : Nat) (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) (horder : r.size ≤ delta * l.size)
    (ancestors : List (Pointer.Frame (NodeRecord α β))) :
    ∃ reads cost, Trace ⟨recordTree (.inner old k v l r),ancestors⟩ reads
        ⟨recordTree (link k v l r hl hr).impl,ancestors⟩ cost ∧
      cost + 990 * Nat.log 2 (r.size + 1) ≤ 990 * Nat.clog 2 (l.size + r.size + 2) + 76 := by
  obtain ⟨steps,route,hpower⟩ := link_charged_left_weighted old k v l r hl hr horder
  obtain ⟨reads,cost,trace,hcost⟩ := route ancestors
  refine ⟨reads,cost,trace,?_⟩
  have hh := weight_steps_log (by omega : r.size + 1 ≠ 0) hpower
  omega

end TangoSquared.Paper20261030.Auxiliary.Metadata
