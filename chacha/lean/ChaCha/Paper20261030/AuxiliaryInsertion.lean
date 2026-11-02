import ChaCha.Paper20261030.AuxiliaryRotations

/-!
# Joining a boundary key to a balanced auxiliary tree

The key is already present at the root of the input ordinary tree. The
library operation `insertMin` or `insertMax` is thus realized entirely by
rotations and adjacent moves, with no creation or deletion of physical
keys. The result is exactly the library's balanced tree.
-/

namespace ChaCha.Paper20261030.Auxiliary

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ChaCha.MTR ChaCha.MTR.Pointer

variable {α : Type*} {β : α → Type*}

theorem insertMin_pointer (k : α) (v : β k) (t : Impl α β) (ht : t.Balanced) :
    Rearranges (erase (bin k v .leaf t)) (erase (insertMin k v t ht).impl)
      (7 * height t) := by
  induction t with
  | leaf => exact rearranges_refl _ _
  | inner sz rk rv l r ihl ihr =>
    let d := insertMin k v l ht.left
    have hp : BalanceLPrecond d.impl.size r.size := by
      right
      rw [d.size_impl]
      exact ⟨by omega,by simpa using ht.at_root⟩
    have hout : (insertMin k v (.inner sz rk rv l r) ht).impl =
        balanceL rk rv d.impl r d.balanced_impl ht.right hp := by
      rw [insertMin]
    intro ancestors
    obtain ⟨cost,trace,hcost⟩ := ihl ht.left (.left rk (erase r) :: ancestors)
    obtain ⟨bc,bt,hbc⟩ := balanceL_pointer rk rv d.impl r d.balanced_impl ht.right hp ancestors
    have up := Trace.step (Step.upLeft (erase d.impl) (erase r) rk ancestors) (Trace.nil _)
    have tail := trace_append trace (trace_append up bt)
    have full := Trace.step
      (Step.rotateLeft .empty (erase l) (erase r) k rk ancestors)
      (Trace.step (Step.left .empty (erase l) (erase r) k rk ancestors) tail)
    refine ⟨cost + bc + 3,?_,?_⟩
    · rw [hout]
      simpa only [erase,bin,List.nil_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
        Nat.zero_add,Nat.reduceAdd]
        using full
    · simp only [height]
      omega

theorem insertMax_pointer (k : α) (v : β k) (t : Impl α β) (ht : t.Balanced) :
    Rearranges (erase (bin k v t .leaf)) (erase (insertMax k v t ht).impl)
      (7 * height t) := by
  induction t with
  | leaf => exact rearranges_refl _ _
  | inner sz lk lv l r ihl ihr =>
    let d := insertMax k v r ht.right
    have hp : BalanceLPrecond d.impl.size l.size := by
      right
      rw [d.size_impl]
      exact ⟨by omega,by simpa using ht.at_root.symm⟩
    have hout : (insertMax k v (.inner sz lk lv l r) ht).impl =
        balanceR lk lv l d.impl ht.left d.balanced_impl hp := by
      rw [insertMax]
    intro ancestors
    obtain ⟨cost,trace,hcost⟩ := ihr ht.right (.right (erase l) lk :: ancestors)
    obtain ⟨bc,bt,hbc⟩ := balanceR_pointer lk lv l d.impl ht.left d.balanced_impl hp ancestors
    have up := Trace.step (Step.upRight (erase l) (erase d.impl) lk ancestors) (Trace.nil _)
    have tail := trace_append trace (trace_append up bt)
    have full := Trace.step
      (Step.rotateRight (erase l) (erase r) .empty lk k ancestors)
      (Trace.step (Step.right (erase l) (erase r) .empty lk k ancestors) tail)
    refine ⟨cost + bc + 3,?_,?_⟩
    · rw [hout]
      simpa only [erase,bin,List.nil_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
        Nat.zero_add,Nat.reduceAdd]
        using full
    · simp only [height]
      omega

theorem insertMin_pointer_log (k : α) (v : β k) (t : Impl α β) (ht : t.Balanced) :
    Rearranges (erase (bin k v .leaf t)) (erase (insertMin k v t ht).impl)
      (21 * Nat.clog 2 (t.size + 1)) := by
  intro ancestors
  obtain ⟨cost,trace,hcost⟩ := insertMin_pointer k v t ht ancestors
  refine ⟨cost,trace,?_⟩
  have hh := balanced_height_log ht
  omega

theorem insertMax_pointer_log (k : α) (v : β k) (t : Impl α β) (ht : t.Balanced) :
    Rearranges (erase (bin k v t .leaf)) (erase (insertMax k v t ht).impl)
      (21 * Nat.clog 2 (t.size + 1)) := by
  intro ancestors
  obtain ⟨cost,trace,hcost⟩ := insertMax_pointer k v t ht ancestors
  refine ⟨cost,trace,?_⟩
  have hh := balanced_height_log ht
  omega

end ChaCha.Paper20261030.Auxiliary
