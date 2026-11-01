import TangoSquared.Paper20261030.AuxiliarySemantics
import TangoSquared.Paper20261030.LeafEncoding

/-!
# Transferring auxiliary rearrangements to record-leaf routing trees

This composes the checked pointer traces with the concrete leaf encoding.
The resulting trees contain precisely the original auxiliary record keys
as leaves. These are routing costs; local metadata observations and their
placement are handled separately from this conversion.
-/

namespace TangoSquared.Paper20261030.Auxiliary

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl

variable {α : Type*} {β : α → Type*}

def leafTree (t : Impl α β) := LeafEncoding.encode (erase t)

theorem rearranges_leaf {a b : MTR.Tree α} {budget : Nat}
    (h : Rearranges a b budget) (ha : a ≠ .empty) :
    LeafPointer.Rearranges (LeafEncoding.encode a) (LeafEncoding.encode b) (5 * budget) := by
  intro ancestors
  obtain ⟨cost,trace,hcost⟩ := h []
  obtain ⟨leafCost,lt,hl⟩ := LeafEncoding.encode_trace trace ha
  refine ⟨leafCost,?_,by omega⟩
  simpa [LeafEncoding.cursor,LeafEncoding.frames,LeafPointer.Cursor.extend] using lt.extend ancestors

theorem link_leaf_cost (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced) :
    LeafPointer.Rearranges (leafTree (bin k v l r)) (leafTree (link k v l r hl hr).impl)
      (105 * (Nat.clog 2 (l.size + 1) + Nat.clog 2 (r.size + 1))) := by
  simpa only [leafTree,← Nat.mul_assoc,Nat.reduceMul] using
    rearranges_leaf (link_pointer_log k v l r hl hr) (by simp [erase,bin])

theorem split_leaf_cost [Ord α] [LawfulEqOrd α] (x : α) (t : Impl α β)
    (ht : t.Balanced) (hf : searchResult x t = true) :
    LeafPointer.Rearranges (leafTree t) (leafTree (splitAt x t ht hf).impl)
      (1170 * Nat.clog 2 (t.size + 1)) := by
  have hn : erase t ≠ .empty := by cases t <;> simp_all [searchResult,erase]
  simpa only [leafTree,← Nat.mul_assoc,Nat.reduceMul] using rearranges_leaf (splitAt_pointer_log x t ht hf) hn

theorem leafTree_leaves (t : Impl α β) :
    (leafTree t).leaves = t.toListModel.map Sigma.fst := by
  rw [leafTree,LeafEncoding.encode_leaves,erase_inorder]

theorem split_leaf_word [Ord α] [LawfulEqOrd α] (x : α) (t : Impl α β)
    (ht : t.Balanced) (hf : searchResult x t = true) :
    (leafTree (splitAt x t ht hf).impl).leaves = (leafTree t).leaves := by
  rw [leafTree_leaves,leafTree_leaves,splitAt_toList]

end TangoSquared.Paper20261030.Auxiliary
