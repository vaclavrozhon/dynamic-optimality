import TangoSquared.Paper20261030.ChargedInsertion
import TangoSquared.Paper20261030.AuxiliaryJoin

/-!
# Recursive join with charged reads and cached-size updates

This is the actual standard-library join on two balanced trees separated
by an existing pivot. Each recursive level reads a four-level snapshot,
makes one rotation and a child excursion, and uses the charged balancing
kernel on return. No subtree sizes are repaired for free.
-/

namespace TangoSquared.Paper20261030.Auxiliary.Metadata

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open TangoSquared.MTR

variable {α : Type*} {β : α → Type*}

inductive JoinPlan where
  | insertMinimum | insertMaximum | descendLeft | descendRight | keep
  deriving DecidableEq, Repr

/-- The recursive branch depends only on the observed child roots. -/
def joinPlan : Snapshot α β → JoinPlan
  | .node _ _ _ .empty _ => .insertMinimum
  | .node _ _ _ _ .empty => .insertMaximum
  | .node _ _ _ (.node sl _ _ _ _) (.node sr _ _ _ _) =>
    if delta * sl < sr then .descendRight
    else if delta * sr < sl then .descendLeft else .keep
  | _ => .keep

theorem joinPlan_inner (old sl sr : Nat) (k lk rk : α)
    (v : β k) (lv : β lk) (rv : β rk) (ll lr rl rr : Impl α β) :
    joinPlan (capture 4 (.inner old k v (.inner sl lk lv ll lr) (.inner sr rk rv rl rr))) =
      if delta * sl < sr then .descendRight
      else if delta * sr < sl then .descendLeft else .keep := rfl

theorem link_charged (old : Nat) (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) :
    ObservedRearranges (.inner old k v l r) (link k v l r hl hr).impl
      (165 * (height l + height r) + 76) := by
  cases l with
  | leaf =>
    simpa only [link,height,Nat.zero_add] using insertMin_charged old k v r hr
  | inner sl lk lv ll lr =>
    cases r with
    | leaf =>
      simpa only [link,height,Nat.add_zero] using insertMax_charged old k v (.inner sl lk lv ll lr) hl
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
        obtain ⟨rc,reads,hrc⟩ := snapshot_charged
          (.inner old k v (.inner sl lk lv ll lr) (.inner sr rk rv rl rr)) ancestors
        obtain ⟨word,cost,trace,hcost⟩ := link_charged old k v (.inner sl lk lv ll lr) rl hl hr.left
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
        simp only [height] at hcost ⊢
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
          obtain ⟨rc,reads,hrc⟩ := snapshot_charged
            (.inner old k v (.inner sl lk lv ll lr) (.inner sr rk rv rl rr)) ancestors
          obtain ⟨word,cost,trace,hcost⟩ := link_charged old k v lr (.inner sr rk rv rl rr) hl.right hr
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
          simp only [height] at hcost ⊢
          omega
        · rw [link,dif_neg hright,dif_neg hleft]
          intro ancestors
          obtain ⟨word,cost,trace,hcost⟩ := refresh_charged old k v
            (.inner sl lk lv ll lr) (.inner sr rk rv rl rr) ancestors
          exact ⟨word,cost,trace,by omega⟩
termination_by sizeOf l + sizeOf r

theorem link_charged_log (old : Nat) (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) :
    ObservedRearranges (.inner old k v l r) (link k v l r hl hr).impl
      (495 * (Nat.clog 2 (l.size + 1) + Nat.clog 2 (r.size + 1)) + 76) := by
  intro ancestors
  obtain ⟨word,cost,trace,bound⟩ := link_charged old k v l r hl hr ancestors
  have hleft := balanced_height_log hl
  have hright := balanced_height_log hr
  exact ⟨word,cost,trace,by omega⟩

end TangoSquared.Paper20261030.Auxiliary.Metadata
