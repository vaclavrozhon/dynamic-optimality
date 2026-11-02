import ChaCha.Paper20261030.AuxiliaryPointer

/-!
# Pointer implementation of the standard library's local balancing

A single rotation costs one pointer operation. A double rotation costs
four: enter the child, rotate it, return, and rotate the root. The library's
actual balance operations agree with this model under their proved
preconditions, so their structural changes have the same constant cost.
-/

namespace ChaCha.Paper20261030.Auxiliary

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ChaCha.MTR ChaCha.MTR.Pointer

variable {α : Type*} {β : α → Type*}

/-- A subtree rearrangement implemented from its root, in every ancestor
context. The final cursor is at the new subtree root. -/
def Rearranges (before after : MTR.Tree α) (budget : Nat) : Prop :=
  ∀ ancestors : List (Frame α), ∃ cost,
    Trace ⟨before,ancestors⟩ [] ⟨after,ancestors⟩ cost ∧ cost ≤ budget

theorem rearranges_refl (t : MTR.Tree α) (budget : Nat) : Rearranges t t budget :=
  fun _ => ⟨0,Trace.nil _,Nat.zero_le _⟩

theorem Rearranges.mono {a b : MTR.Tree α} {c d : Nat}
    (h : Rearranges a b c) (hle : c ≤ d) : Rearranges a b d := by
  intro ancestors
  obtain ⟨cost,trace,hcost⟩ := h ancestors
  exact ⟨cost,trace,hcost.trans hle⟩

theorem Rearranges.trans {a b c : MTR.Tree α} {m n : Nat}
    (h : Rearranges a b m) (g : Rearranges b c n) : Rearranges a c (m + n) := by
  intro ancestors
  obtain ⟨hc,ht,hb⟩ := h ancestors
  obtain ⟨gc,gt,gb⟩ := g ancestors
  exact ⟨hc + gc,by simpa using trace_append ht gt,Nat.add_le_add hb gb⟩

theorem Rearranges.left {a b r : MTR.Tree α} {k : α} {n : Nat}
    (h : Rearranges a b n) (ha : a ≠ .empty) :
    Rearranges (.node a k r) (.node b k r) (n + 2) := by
  cases a with
  | empty => exact False.elim (ha rfl)
  | node al ak ar =>
    intro ancestors
    obtain ⟨cost,trace,hcost⟩ := h (.left k r :: ancestors)
    have up := Trace.step (Step.upLeft b r k ancestors) (Trace.nil _)
    have full := Trace.step (Step.left al ar r ak k ancestors) (trace_append trace up)
    exact ⟨cost + 2,by simpa using full,by omega⟩

theorem Rearranges.right {l a b : MTR.Tree α} {k : α} {n : Nat}
    (h : Rearranges a b n) (ha : a ≠ .empty) :
    Rearranges (.node l k a) (.node l k b) (n + 2) := by
  cases a with
  | empty => exact False.elim (ha rfl)
  | node al ak ar =>
    intro ancestors
    obtain ⟨cost,trace,hcost⟩ := h (.right l k :: ancestors)
    have up := Trace.step (Step.upRight l b k ancestors) (Trace.nil _)
    have full := Trace.step (Step.right l al ar k ak ancestors) (trace_append trace up)
    exact ⟨cost + 2,by simpa using full,by omega⟩

theorem singleL_pointer (k : α) (v : β k) (l : Impl α β)
    (rk : α) (rv : β rk) (rl rr : Impl α β) :
    Rearranges (erase (bin k v l (bin rk rv rl rr)))
      (erase (singleL k v l rk rv rl rr)) 4 := by
  intro ancestors
  exact ⟨1,Trace.step (Step.rotateLeft (erase l) (erase rl) (erase rr) k rk ancestors)
    (Trace.nil _), by decide⟩

theorem singleR_pointer (k : α) (v : β k) (lk : α) (lv : β lk)
    (ll lr r : Impl α β) :
    Rearranges (erase (bin k v (bin lk lv ll lr) r))
      (erase (singleR k v lk lv ll lr r)) 4 := by
  intro ancestors
  exact ⟨1,Trace.step (Step.rotateRight (erase ll) (erase lr) (erase r) lk k ancestors)
    (Trace.nil _), by decide⟩

theorem doubleL_pointer (k : α) (v : β k) (l : Impl α β) (rk : α) (rv : β rk)
    (rlk : α) (rlv : β rlk) (rll rlr rr : Impl α β) :
    Rearranges (erase (bin k v l (bin rk rv (bin rlk rlv rll rlr) rr)))
      (erase (doubleL k v l rk rv rlk rlv rll rlr rr)) 4 := by
  intro ancestors
  refine ⟨4,?_,le_rfl⟩
  exact Trace.step (Step.right (erase l) (.node (erase rll) rlk (erase rlr)) (erase rr) k rk ancestors)
    (Trace.step (Step.rotateRight (erase rll) (erase rlr) (erase rr) rlk rk (.right (erase l) k :: ancestors))
      (Trace.step (Step.upRight (erase l) (.node (erase rll) rlk (.node (erase rlr) rk (erase rr))) k ancestors)
        (Trace.step (Step.rotateLeft (erase l) (erase rll) (.node (erase rlr) rk (erase rr)) k rlk ancestors)
          (Trace.nil _))))

theorem doubleR_pointer (k : α) (v : β k) (lk : α) (lv : β lk)
    (ll : Impl α β) (lrk : α) (lrv : β lrk) (lrl lrr r : Impl α β) :
    Rearranges (erase (bin k v (bin lk lv ll (bin lrk lrv lrl lrr)) r))
      (erase (doubleR k v lk lv ll lrk lrv lrl lrr r)) 4 := by
  intro ancestors
  refine ⟨4,?_,le_rfl⟩
  exact Trace.step (Step.left (erase ll) (.node (erase lrl) lrk (erase lrr)) (erase r) lk k ancestors)
    (Trace.step (Step.rotateLeft (erase ll) (erase lrl) (erase lrr) lk lrk (.left k (erase r) :: ancestors))
      (Trace.step (Step.upLeft (.node (.node (erase ll) lk (erase lrl)) lrk (erase lrr)) (erase r) k ancestors)
        (Trace.step (Step.rotateRight (.node (erase ll) lk (erase lrl)) (erase lrr) (erase r) lrk k ancestors)
          (Trace.nil _))))

theorem rotateL_pointer (k : α) (v : β k) (l : Impl α β)
    (rk : α) (rv : β rk) (rl rr : Impl α β) :
    Rearranges (erase (bin k v l (bin rk rv rl rr)))
      (erase (rotateL k v l rk rv rl rr)) 4 := by
  unfold rotateL
  split
  · exact singleL_pointer _ _ _ _ _ _ _
  · cases rl with
    | leaf => exact singleL_pointer _ _ _ _ _ _ _
    | inner sz rlk rlv rll rlr => exact doubleL_pointer _ _ _ _ _ _ _ _ _ _

theorem rotateR_pointer (k : α) (v : β k) (lk : α) (lv : β lk)
    (ll lr r : Impl α β) :
    Rearranges (erase (bin k v (bin lk lv ll lr) r))
      (erase (rotateR k v lk lv ll lr r)) 4 := by
  unfold rotateR
  split
  · exact singleR_pointer _ _ _ _ _ _ _
  · cases lr with
    | leaf => exact singleR_pointer _ _ _ _ _ _ _
    | inner sz lrk lrv lrl lrr => exact doubleR_pointer _ _ _ _ _ _ _ _ _ _

theorem balanceModel_pointer (k : α) (v : β k) (l r : Impl α β) :
    Rearranges (erase (bin k v l r)) (erase (balanceₘ k v l r)) 4 := by
  unfold balanceₘ
  split
  · exact rearranges_refl _ _
  · split
    · cases r with
      | leaf =>
        have hz : (Impl.leaf : Impl α β).size = 0 := rfl
        omega
      | inner sz rk rv rl rr => exact rotateL_pointer _ _ _ _ _ _ _
    · split
      · cases l with
        | leaf =>
          have hz : (Impl.leaf : Impl α β).size = 0 := rfl
          omega
        | inner sz lk lv ll lr => exact rotateR_pointer _ _ _ _ _ _ _
      · exact rearranges_refl _ _

theorem balanceLErase_pointer (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) (hp : BalanceLErasePrecond l.size r.size) :
    Rearranges (erase (bin k v l r)) (erase (balanceLErase k v l r hl hr hp)) 4 := by
  rw [balanceLErase_eq_balanceL!,balanceL!_eq_balance! hl hr hp,
    balance!_eq_balanceₘ hl hr (Or.inl hp)]
  exact balanceModel_pointer _ _ _ _

theorem balanceRErase_pointer (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) (hp : BalanceLErasePrecond r.size l.size) :
    Rearranges (erase (bin k v l r)) (erase (balanceRErase k v l r hl hr hp)) 4 := by
  rw [balanceRErase_eq_balanceR!,balanceR!_eq_balance! hl hr hp,
    balance!_eq_balanceₘ hl hr (Or.inr hp)]
  exact balanceModel_pointer _ _ _ _

theorem balanceL_pointer (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) (hp : BalanceLPrecond l.size r.size) :
    Rearranges (erase (bin k v l r)) (erase (balanceL k v l r hl hr hp)) 4 := by
  rw [balanceL_eq_balanceLErase]
  exact balanceLErase_pointer _ _ _ _ _ _ _

theorem balanceR_pointer (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) (hp : BalanceLPrecond r.size l.size) :
    Rearranges (erase (bin k v l r)) (erase (balanceR k v l r hl hr hp)) 4 := by
  rw [balanceR_eq_balanceRErase]
  exact balanceRErase_pointer _ _ _ _ _ _ _

end ChaCha.Paper20261030.Auxiliary
