import TangoSquared.Paper20261030.ComponentEquivalence

/-!
# Exact inorder lists of auxiliary gap subtrees

A core with `k` separator records has `k+1` actual ports. Recording them
as a list makes interval replacement explicit: splitting partitions the
port list, joining concatenates the two lists, and adding an extreme
separator adds exactly its sibling port. No equality of balancing shapes
is needed.
-/

namespace TangoSquared.Paper20261030.AuxiliaryComponent

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata

variable {α κ : Type*} {β : κ → Type*}

def portWord (c : AuxiliaryComponent α κ β) : List (Source α (NodeRecord κ β)) :=
  (List.range (c.core.size + 1)).map c.ports

theorem portWord_length (c : AuxiliaryComponent α κ β) : c.portWord.length = c.core.size + 1 := by
  simp only [portWord,List.length_map,List.length_range]

theorem Equivalent.portWord {a b : AuxiliaryComponent α κ β} (h : Equivalent a b) :
    a.portWord = b.portWord := by
  unfold AuxiliaryComponent.portWord
  rw [← h.size]
  apply List.map_inj_left.mpr
  intro i hi
  apply h.ports i
  have := List.mem_range.mp hi
  omega

theorem equivalent_of_words {a b : AuxiliaryComponent α κ β}
    (hw : a.core.toListModel = b.core.toListModel) (hp : a.portWord = b.portWord) : Equivalent a b := by
  have hs : a.core.size = b.core.size := by
    rw [size_eq_length _ a.balanced,size_eq_length _ b.balanced,hw]
  refine ⟨hw,?_⟩
  intro i hi
  have hm : i ∈ List.range (a.core.size + 1) := List.mem_range.mpr (by omega)
  have he : (List.range (a.core.size + 1)).map a.ports =
      (List.range (a.core.size + 1)).map b.ports := by
    simpa only [portWord,← hs] using hp
  exact List.map_inj_left.mp he i hm

theorem join_portWord (key : κ) (value : β key) (l r : AuxiliaryComponent α κ β) :
    (join key value l r).portWord = l.portWord ++ r.portWord := by
  unfold portWord
  rw [join_size,show l.core.size + 1 + r.core.size + 1 = (l.core.size + 1) + (r.core.size + 1) by omega,
    List.range_add,List.map_append,List.map_map]
  congr 1
  · apply List.map_inj_left.mpr
    intro i hi
    have hb : i ≤ l.core.size := by have := List.mem_range.mp hi; omega
    simp only [join,if_pos hb]
  · apply List.map_inj_left.mpr
    intro i hi
    have hb : ¬ l.core.size + 1 + i ≤ l.core.size := by omega
    simp only [Function.comp_apply,join,if_neg hb,Nat.add_sub_cancel_left]

theorem append_portWord (c : AuxiliaryComponent α κ β) (key : κ) (value : β key)
    (sibling : Source α (NodeRecord κ β)) :
    (append c key value sibling).portWord = c.portWord ++ [sibling] := by
  unfold portWord
  rw [append_size,List.range_succ,List.map_append,List.map_singleton]
  have hlast : (append c key value sibling).ports (c.core.size + 1) = sibling := by
    simp only [append,show ¬ c.core.size + 1 ≤ c.core.size by omega,if_false]
  rw [hlast]
  congr 1
  apply List.map_inj_left.mpr
  intro i hi
  have hb : i ≤ c.core.size := by have := List.mem_range.mp hi; omega
  simp only [append,if_pos hb]

theorem prepend_portWord (key : κ) (value : β key) (sibling : Source α (NodeRecord κ β))
    (c : AuxiliaryComponent α κ β) :
    (prepend key value sibling c).portWord = sibling :: c.portWord := by
  unfold portWord
  rw [prepend_size,List.range_succ_eq_map,List.map_cons,List.map_map]
  have hzero : (prepend key value sibling c).ports 0 = sibling := by simp only [prepend,if_true]
  rw [hzero]
  congr 1

theorem cut_portWord [Ord κ] [LawfulEqOrd κ] (c : AuxiliaryComponent α κ β) (key : κ)
    (found : searchResult key c.core = true) :
    c.portWord = (cutLeft c key found).portWord ++ (cutRight c key found).portWord := by
  have hs := splitAt_size key c.core c.balanced found
  unfold portWord
  rw [← hs,show (splitAt key c.core c.balanced found).left.size + 1 +
      (splitAt key c.core c.balanced found).right.size + 1 =
      ((splitAt key c.core c.balanced found).left.size + 1) +
      ((splitAt key c.core c.balanced found).right.size + 1) by omega,
    List.range_add,List.map_append,List.map_map]
  rfl

end TangoSquared.Paper20261030.AuxiliaryComponent
