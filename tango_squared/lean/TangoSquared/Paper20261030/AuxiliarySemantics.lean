import TangoSquared.Paper20261030.SharpSplit
import Std.Data.DTreeMap.Internal.WF.Lemmas

/-!
# Preservation of auxiliary keys, order, and payloads

Pointer traces establish physical rearrangement. The list model also
records the value stored with each key, so its preservation checks that
splitting retains the application metadata as well as the routing keys.
-/

namespace TangoSquared.Paper20261030.Auxiliary

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open TangoSquared.MTR

variable {α : Type*} {β : α → Type*}

theorem erase_inorder (t : Impl α β) :
    MTR.Tree.inorder (erase t) = t.toListModel.map Sigma.fst := by
  induction t with
  | leaf => rfl
  | inner sz k v l r ihl ihr =>
    simp [erase,MTR.Tree.inorder,Impl.toListModel,ihl,ihr]

theorem splitAt_toList [Ord α] [LawfulEqOrd α] (x : α) (t : Impl α β)
    (ht : t.Balanced) (hf : searchResult x t = true) :
    (splitAt x t ht hf).impl.toListModel = t.toListModel := by
  induction t with
  | leaf => simp [searchResult] at hf
  | inner sz k v l r ihl ihr =>
    cases hc : compare x k with
    | eq =>
      have hx := compare_eq_iff_eq.mp hc
      rw [splitAt]
      split <;> rename_i hb <;> simp [hc] at hb
      subst k
      rfl
    | lt =>
      have fl : searchResult x l = true := by simpa [searchResult,hc] using hf
      have il := congrArg (fun word => word ++ ⟨k,v⟩ :: r.toListModel) (ihl ht.left fl)
      rw [splitAt]
      split <;> rename_i hb <;> simp [hc] at hb
      simpa only [SplitResult.impl,bin,toListModel_inner,toListModel_link,
        List.append_assoc,List.cons_append] using il
    | gt =>
      have fr : searchResult x r = true := by simpa [searchResult,hc] using hf
      have ir := congrArg (fun word => l.toListModel ++ ⟨k,v⟩ :: word) (ihr ht.right fr)
      rw [splitAt]
      split <;> rename_i hb <;> simp [hc] at hb
      simpa only [SplitResult.impl,bin,toListModel_inner,toListModel_link,
        List.append_assoc,List.cons_append] using ir

theorem splitAt_inorder [Ord α] [LawfulEqOrd α] (x : α) (t : Impl α β)
    (ht : t.Balanced) (hf : searchResult x t = true) :
    MTR.Tree.inorder (erase (splitAt x t ht hf).impl) = MTR.Tree.inorder (erase t) := by
  rw [erase_inorder,erase_inorder,splitAt_toList]

theorem splitAt_ordered [Ord α] [LawfulEqOrd α] (x : α) (t : Impl α β)
    (ht : t.Balanced) (hf : searchResult x t = true) (ho : t.Ordered) :
    (splitAt x t ht hf).impl.Ordered := by
  simpa only [Impl.Ordered,splitAt_toList] using ho

/-- The exposed root can serve the request after the charged split. The
whole operation is an access in the existing ordinary BST pointer model. -/
theorem splitAt_access [Ord α] [LawfulEqOrd α] (x : α) (t : Impl α β)
    (ht : t.Balanced) (hf : searchResult x t = true) :
    ∃ cost, Pointer.Access x (erase t) (erase (splitAt x t ht hf).impl) cost ∧
      cost ≤ 234 * Nat.clog 2 (t.size + 1) + 1 := by
  obtain ⟨cost,trace,hcost⟩ := splitAt_pointer_log x t ht hf []
  let final := Pointer.Cursor.atRoot (erase (splitAt x t ht hf).impl)
  have service : Pointer.Trace final [x] final 1 :=
    Pointer.Trace.serve (by rfl) (Pointer.Trace.nil _)
  refine ⟨cost + 1,⟨final,rfl,?_⟩,by omega⟩
  simpa [Pointer.Cursor.atRoot] using trace_append trace service

end TangoSquared.Paper20261030.Auxiliary
