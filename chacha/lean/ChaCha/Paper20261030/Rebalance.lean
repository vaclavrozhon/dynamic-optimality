import ChaCha.Paper20261030.ChargedJoin
import ChaCha.Paper20261030.ChargedRearrangements
import Std.Data.DTreeMap.Internal.WF.Lemmas

/-!
# Charged initialization from an arbitrary auxiliary shape

Rebalance the two children and join them with their existing pivot. This
preserves every key and payload, reads the reached records, and repairs
all cached sizes. The input need not already be a right spine and its
size caches need not be correct. For `k` actual records, the cost is at
most `(990 clog 2 (k+1) + 81) k`.
-/

namespace ChaCha.Paper20261030.Auxiliary.Metadata

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl

variable {α : Type*} {β : α → Type*}

def actualSize : Impl α β → Nat
  | .leaf => 0
  | .inner _ _ _ l r => actualSize l + 1 + actualSize r

def rebalance : (t : Impl α β) → Impl.Tree α β (actualSize t)
  | .leaf => ⟨.leaf,.leaf,rfl⟩
  | .inner _ k v l r =>
    let left := rebalance l
    let right := rebalance r
    let joined := link k v left.impl right.impl left.balanced_impl right.balanced_impl
    ⟨joined.impl,joined.balanced_impl,by
      rw [joined.size_impl,left.size_impl,right.size_impl]
      rfl⟩

theorem rebalance_word [Ord α] (t : Impl α β) : (rebalance t).impl.toListModel = t.toListModel := by
  induction t with
  | leaf => rfl
  | inner sz k v l r ihl ihr => simp only [rebalance,toListModel_link,ihl,ihr,toListModel_inner]

theorem actualSize_length (t : Impl α β) : actualSize t = t.toListModel.length := by
  induction t <;> simp_all [actualSize,toListModel,List.length_append,List.length_cons,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem rebalance_ordered [Ord α] (t : Impl α β) (h : t.Ordered) : (rebalance t).impl.Ordered := by
  simpa only [Impl.Ordered,rebalance_word] using h

theorem rebalance_charged (t : Impl α β) :
    ObservedRearranges t (rebalance t).impl
      ((990 * Nat.clog 2 (actualSize t + 1) + 81) * actualSize t) := by
  induction t with
  | leaf => exact fun _ => ⟨[],0,.nil _,le_rfl⟩
  | inner sz k v l r ihl ihr =>
    have read : ObservedRearranges (.inner sz k v l r) (.inner sz k v l r) 1 :=
      fun rest => ⟨_,1,.read rfl (.nil _),le_rfl⟩
    have left : ObservedRearranges (.inner sz k v l r) (.inner sz k v (rebalance l).impl r)
        ((990 * Nat.clog 2 (actualSize l + 1) + 81) * actualSize l + 2) := by
      cases l with
      | leaf => exact fun _ => ⟨[],0,.nil _,Nat.zero_le _⟩
      | inner => exact ihl.left (by simp)
    have right : ObservedRearranges (.inner sz k v (rebalance l).impl r)
        (.inner sz k v (rebalance l).impl (rebalance r).impl)
        ((990 * Nat.clog 2 (actualSize r + 1) + 81) * actualSize r + 2) := by
      cases r with
      | leaf => exact fun _ => ⟨[],0,.nil _,Nat.zero_le _⟩
      | inner => exact ihr.right (by simp)
    have joined := link_charged_log sz k v (rebalance l).impl (rebalance r).impl
      (rebalance l).balanced_impl (rebalance r).balanced_impl
    have full := ((read.trans left).trans right).trans joined
    apply full.mono
    rw [(rebalance l).size_impl,(rebalance r).size_impl]
    have hl := Nat.clog_monotone 2
      (show actualSize l + 1 ≤ actualSize (.inner sz k v l r) + 1 by simp [actualSize]; omega)
    have hr := Nat.clog_monotone 2
      (show actualSize r + 1 ≤ actualSize (.inner sz k v l r) + 1 by simp only [actualSize]; omega)
    have hml := Nat.mul_le_mul_right (actualSize l)
      (show 990 * Nat.clog 2 (actualSize l + 1) + 81 ≤
        990 * Nat.clog 2 (actualSize (.inner sz k v l r) + 1) + 81 by omega)
    have hmr := Nat.mul_le_mul_right (actualSize r)
      (show 990 * Nat.clog 2 (actualSize r + 1) + 81 ≤
        990 * Nat.clog 2 (actualSize (.inner sz k v l r) + 1) + 81 by omega)
    simp only [actualSize] at hl hr hml hmr ⊢
    simp only [Nat.mul_add,Nat.mul_one] at hml hmr ⊢
    omega

end ChaCha.Paper20261030.Auxiliary.Metadata
