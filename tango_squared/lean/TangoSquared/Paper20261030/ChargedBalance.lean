import TangoSquared.Paper20261030.MetadataPointer

/-!
# Local balancing with charged reads, rotations, and cache writes

The size update is made at its actual record. Each single rotation and its
two cache writes cost five operations. Each double rotation and its three
cache writes cost eleven. A preceding four-level tour reads the records
used to select the rotation and calculate the new sizes.
-/

namespace TangoSquared.Paper20261030.Auxiliary.Metadata

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open TangoSquared.MTR

variable {α : Type*} {β : α → Type*}

def Repairs (before after : Impl α β) (budget : Nat) : Prop :=
  ∀ ancestors : List (Pointer.Frame (NodeRecord α β)), ∃ cost,
    Trace ⟨recordTree before,ancestors⟩ [] ⟨recordTree after,ancestors⟩ cost ∧ cost ≤ budget

theorem repairs_refl (t : Impl α β) (budget : Nat) : Repairs t t budget :=
  fun _ => ⟨0,.nil _,Nat.zero_le _⟩

theorem write_left (a b c : MTR.Tree (NodeRecord α β)) (entry : Sigma β)
    (parent : NodeRecord α β) (old fresh : Nat) (ancestors) :
    Trace ⟨.node (.node a (old,entry) b) parent c,ancestors⟩ []
      ⟨.node (.node a (fresh,entry) b) parent c,ancestors⟩ 3 :=
  .step (.nav (.left a b c (old,entry) parent ancestors))
    (.step (.write a b old fresh entry (.left parent c :: ancestors))
      (.step (.nav (.upLeft (.node a (fresh,entry) b) c parent ancestors)) (.nil _)))

theorem write_right (a b c : MTR.Tree (NodeRecord α β)) (entry : Sigma β)
    (parent : NodeRecord α β) (old fresh : Nat) (ancestors) :
    Trace ⟨.node a parent (.node b (old,entry) c),ancestors⟩ []
      ⟨.node a parent (.node b (fresh,entry) c),ancestors⟩ 3 :=
  .step (.nav (.right a b c parent (old,entry) ancestors))
    (.step (.write b c old fresh entry (.right a parent :: ancestors))
      (.step (.nav (.upRight a (.node b (fresh,entry) c) parent ancestors)) (.nil _)))

theorem singleL_repairs (k : α) (v : β k) (l : Impl α β)
    (rs : Nat) (rk : α) (rv : β rk) (rl rr : Impl α β) :
    Repairs (bin k v l (.inner rs rk rv rl rr)) (singleL k v l rk rv rl rr) 11 := by
  intro ancestors
  let old := l.size + 1 + rs
  let fresh := l.size + 1 + rl.size
  have wc := write_left (recordTree l) (recordTree rl) (recordTree rr)
    ⟨k,v⟩ (rs,⟨rk,rv⟩) old fresh ancestors
  have wr := Trace.step (Step.write (.node (recordTree l) (fresh,⟨k,v⟩) (recordTree rl)) (recordTree rr) rs (fresh + 1 + rr.size) ⟨rk,rv⟩ ancestors) (Trace.nil _)
  refine ⟨5,?_,by decide⟩
  exact .step (.nav (.rotateLeft (recordTree l) (recordTree rl) (recordTree rr)
    (old,⟨k,v⟩) (rs,⟨rk,rv⟩) ancestors)) (wc.append wr)

theorem singleR_repairs (k : α) (v : β k) (ls : Nat) (lk : α) (lv : β lk)
    (ll lr r : Impl α β) :
    Repairs (bin k v (.inner ls lk lv ll lr) r) (singleR k v lk lv ll lr r) 11 := by
  intro ancestors
  let old := ls + 1 + r.size
  let fresh := lr.size + 1 + r.size
  have wc := write_right (recordTree ll) (recordTree lr) (recordTree r)
    ⟨k,v⟩ (ls,⟨lk,lv⟩) old fresh ancestors
  have wr := Trace.step (Step.write (recordTree ll) (.node (recordTree lr) (fresh,⟨k,v⟩) (recordTree r)) ls (ll.size + 1 + fresh) ⟨lk,lv⟩ ancestors) (Trace.nil _)
  refine ⟨5,?_,by decide⟩
  exact .step (.nav (.rotateRight (recordTree ll) (recordTree lr) (recordTree r)
    (ls,⟨lk,lv⟩) (old,⟨k,v⟩) ancestors)) (wc.append wr)

theorem doubleL_repairs (k : α) (v : β k) (l : Impl α β)
    (rs : Nat) (rk : α) (rv : β rk) (ms : Nat) (mk : α) (mv : β mk)
    (ml mr rr : Impl α β) :
    Repairs (bin k v l (.inner rs rk rv (.inner ms mk mv ml mr) rr))
      (doubleL k v l rk rv mk mv ml mr rr) 11 := by
  intro ancestors
  let kr : NodeRecord α β := (l.size + 1 + rs,⟨k,v⟩)
  let rr' : NodeRecord α β := (rs,⟨rk,rv⟩)
  let mm : NodeRecord α β := (ms,⟨mk,mv⟩)
  let fl := l.size + 1 + ml.size
  let fr := mr.size + 1 + rr.size
  have wl := write_left (recordTree l) (recordTree ml)
    (.node (recordTree mr) rr' (recordTree rr)) ⟨k,v⟩ mm kr.1 fl ancestors
  have wr := write_right (.node (recordTree l) (fl,⟨k,v⟩) (recordTree ml))
    (recordTree mr) (recordTree rr) ⟨rk,rv⟩ mm rs fr ancestors
  have wm := Trace.step (Step.write (.node (recordTree l) (fl,⟨k,v⟩) (recordTree ml)) (.node (recordTree mr) (fr,⟨rk,rv⟩) (recordTree rr)) ms (fl + 1 + fr) ⟨mk,mv⟩ ancestors) (Trace.nil _)
  have tail := wl.append (wr.append wm)
  refine ⟨11,?_,le_rfl⟩
  exact .step (.nav (.right (recordTree l) (.node (recordTree ml) mm (recordTree mr)) (recordTree rr) kr rr' ancestors))
    (.step (.nav (.rotateRight (recordTree ml) (recordTree mr) (recordTree rr) mm rr' (.right (recordTree l) kr :: ancestors)))
      (.step (.nav (.upRight (recordTree l) (.node (recordTree ml) mm (.node (recordTree mr) rr' (recordTree rr))) kr ancestors))
        (.step (.nav (.rotateLeft (recordTree l) (recordTree ml) (.node (recordTree mr) rr' (recordTree rr)) kr mm ancestors)) tail)))

theorem doubleR_repairs (k : α) (v : β k) (ls : Nat) (lk : α) (lv : β lk)
    (ll : Impl α β) (ms : Nat) (mk : α) (mv : β mk) (ml mr r : Impl α β) :
    Repairs (bin k v (.inner ls lk lv ll (.inner ms mk mv ml mr)) r)
      (doubleR k v lk lv ll mk mv ml mr r) 11 := by
  intro ancestors
  let kr : NodeRecord α β := (ls + 1 + r.size,⟨k,v⟩)
  let lr' : NodeRecord α β := (ls,⟨lk,lv⟩)
  let mm : NodeRecord α β := (ms,⟨mk,mv⟩)
  let fl := ll.size + 1 + ml.size
  let fr := mr.size + 1 + r.size
  have wl := write_left (recordTree ll) (recordTree ml)
    (.node (recordTree mr) kr (recordTree r)) ⟨lk,lv⟩ mm ls fl ancestors
  have wr := write_right (.node (recordTree ll) (fl,⟨lk,lv⟩) (recordTree ml))
    (recordTree mr) (recordTree r) ⟨k,v⟩ mm kr.1 fr ancestors
  have wm := Trace.step (Step.write (.node (recordTree ll) (fl,⟨lk,lv⟩) (recordTree ml)) (.node (recordTree mr) (fr,⟨k,v⟩) (recordTree r)) ms (fl + 1 + fr) ⟨mk,mv⟩ ancestors) (Trace.nil _)
  have tail := wl.append (wr.append wm)
  refine ⟨11,?_,le_rfl⟩
  exact .step (.nav (.left (recordTree ll) (.node (recordTree ml) mm (recordTree mr)) (recordTree r) lr' kr ancestors))
    (.step (.nav (.rotateLeft (recordTree ll) (recordTree ml) (recordTree mr) lr' mm (.left kr (recordTree r) :: ancestors)))
      (.step (.nav (.upLeft (.node (.node (recordTree ll) lr' (recordTree ml)) mm (recordTree mr)) (recordTree r) kr ancestors))
        (.step (.nav (.rotateRight (.node (recordTree ll) lr' (recordTree ml)) (recordTree mr) (recordTree r) mm kr ancestors)) tail)))

theorem applyPlan_repairs (plan : BalancePlan) (k : α) (v : β k) (l r : Impl α β) :
    Repairs (bin k v l r) (applyPlan plan k v l r) 11 := by
  cases plan with
  | keep => exact repairs_refl _ _
  | singleLeft =>
    cases r with
    | leaf => exact repairs_refl _ _
    | inner => exact singleL_repairs _ _ _ _ _ _ _ _
  | singleRight =>
    cases l with
    | leaf => exact repairs_refl _ _
    | inner => exact singleR_repairs _ _ _ _ _ _ _ _
  | doubleLeft =>
    cases r with
    | leaf => exact repairs_refl _ _
    | inner sz rk rv rl rr =>
      cases rl with
      | leaf => exact repairs_refl _ _
      | inner => exact doubleL_repairs _ _ _ _ _ _ _ _ _ _ _ _
  | doubleRight =>
    cases l with
    | leaf => exact repairs_refl _ _
    | inner sz lk lv ll lr =>
      cases lr with
      | leaf => exact repairs_refl _ _
      | inner => exact doubleR_repairs _ _ _ _ _ _ _ _ _ _ _ _

theorem balance_charged (k : α) (v : β k) (l r : Impl α β) (ancestors) :
    ∃ cost, Trace ⟨recordTree (bin k v l r),ancestors⟩
      (capture 4 (bin k v l r)).records ⟨recordTree (balanceₘ k v l r),ancestors⟩ cost ∧
      cost ≤ 86 := by
  obtain ⟨rc, reads, hrc, output⟩ := balance_snapshot_tour k v l r ancestors
  obtain ⟨wc, writes, hwc⟩ := applyPlan_repairs (balancePlan (capture 4 (bin k v l r))) k v l r ancestors
  rw [output] at writes
  refine ⟨rc + wc,?_,by omega⟩
  simpa only [List.append_nil] using (Trace.ofPointer reads).append writes

/-- A recursive caller may have just changed the children while the pivot
still has its old cached size. Charge the pivot update as well. -/
theorem balance_existing_charged (old : Nat) (k : α) (v : β k)
    (l r : Impl α β) (ancestors) :
    ∃ cost, Trace ⟨recordTree (.inner old k v l r),ancestors⟩
      (capture 4 (.inner old k v l r)).records
      ⟨recordTree (balanceₘ k v l r),ancestors⟩ cost ∧ cost ≤ 87 := by
  obtain ⟨rc,reads,hrc⟩ := four_level_tour (recordTree (.inner old k v l r)) ancestors
  have cache : Trace ⟨recordTree (.inner old k v l r),ancestors⟩ []
      ⟨recordTree (bin k v l r),ancestors⟩ 1 :=
    .step (.write (recordTree l) (recordTree r) old (l.size + 1 + r.size) ⟨k,v⟩ ancestors) (.nil _)
  obtain ⟨wc,writes,hwc⟩ := applyPlan_repairs
    (balancePlan (capture 4 (bin k v l r))) k v l r ancestors
  have output : applyPlan (balancePlan (capture 4 (bin k v l r))) k v l r = balanceₘ k v l r := by
    rw [balancePlan_depth 1,balancePlan_correct]
  rw [output] at writes
  refine ⟨rc + (1 + wc),?_,by omega⟩
  simpa only [capture_records,List.nil_append,List.append_nil] using
    (Trace.ofPointer reads).append (cache.append writes)

theorem balanceLErase_existing_charged (old : Nat) (k : α) (v : β k)
    (l r : Impl α β) (hl : l.Balanced) (hr : r.Balanced)
    (hp : BalanceLErasePrecond l.size r.size) (ancestors) :
    ∃ cost, Trace ⟨recordTree (.inner old k v l r),ancestors⟩
      (capture 4 (.inner old k v l r)).records
      ⟨recordTree (balanceLErase k v l r hl hr hp),ancestors⟩ cost ∧ cost ≤ 87 := by
  rw [balanceLErase_eq_balanceL!,balanceL!_eq_balance! hl hr hp,
    balance!_eq_balanceₘ hl hr (Or.inl hp)]
  exact balance_existing_charged old k v l r ancestors

theorem balanceRErase_existing_charged (old : Nat) (k : α) (v : β k)
    (l r : Impl α β) (hl : l.Balanced) (hr : r.Balanced)
    (hp : BalanceLErasePrecond r.size l.size) (ancestors) :
    ∃ cost, Trace ⟨recordTree (.inner old k v l r),ancestors⟩
      (capture 4 (.inner old k v l r)).records
      ⟨recordTree (balanceRErase k v l r hl hr hp),ancestors⟩ cost ∧ cost ≤ 87 := by
  rw [balanceRErase_eq_balanceR!,balanceR!_eq_balance! hl hr hp,
    balance!_eq_balanceₘ hl hr (Or.inr hp)]
  exact balance_existing_charged old k v l r ancestors

end TangoSquared.Paper20261030.Auxiliary.Metadata
