import ChaCha.Paper20261030.SecondaryDecomposition
import ChaCha.Paper20261030.PreferredDescendant

/-!
# The physical port window of a secondary preferred descendant

All its preferred ancestors have separator keys outside its reference
interval. Their represented sibling components are independent of any
preference changes inside that interval. The context obtained here can
therefore be reused after an interior repair, with the identical outside
records and physical hanging subtrees.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem descendant_context {p : DepthSplit → Bool} {a b x y : Nat}
    {reference : DepthTree a b} {subtree : DepthTree x y}
    (below : SeparatorPath.Descendant p reference subtree)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    ∃ (sub : AuxiliaryComponent Nat Nat (Tagged Payload))
      (frames : List (ContextFrame (α := Nat) followsRight)),
      Represents followsRight (source subtree p) sub ∧ Equivalent c (PreferredContext.wrap sub frames) ∧
      (∀ e ∈ PreferredContext.before frames, e.1 < x) ∧
      (∀ e ∈ PreferredContext.after frames, y ≤ e.1) ∧
      ∀ q : DepthSplit → Bool, (∀ s, s ∉ subtree.nodes → q s = p s) →
        PreferredContext.plug (source subtree q) frames = source reference q := by
  induction below generalizing c with
  | refl reference => exact ⟨c,[],represented,.refl _,by simp [PreferredContext.before],
      by simp [PreferredContext.after],fun _ _ => rfl⟩
  | @left a b cut x y ha hb l r subtree bit below ih =>
    obtain ⟨lc,rc,hl,hr,same⟩ := represented.left_view bit
    obtain ⟨sub,frames,hs,he,hbefore,hafter,hplug⟩ := ih lc hl
    let record : Cached := (0,⟨cut,((⟨a,cut,b⟩,p ⟨a,cut,b⟩),false)⟩)
    let frame : ContextFrame (α := Nat) followsRight := .left record (source r p) rc rfl bit hr
    have bounds := below.bounds
    refine ⟨sub,frames ++ [frame],hs,?_,?_,?_,?_⟩
    · rw [PreferredContext.wrap_append]
      exact same.trans (frame.equivalent he)
    · simpa only [PreferredContext.before_append,PreferredContext.before,ContextFrame.before,
        frame,List.nil_append,List.append_nil] using hbefore
    · intro e hm
      simp only [PreferredContext.after_append,PreferredContext.after,ContextFrame.after,
        frame,List.append_nil,List.mem_append,List.mem_singleton] at hm
      rcases hm with hm | hm
      · exact hafter e hm
      · subst e
        exact bounds.2
    · intro q hq
      have rootOutside : (⟨a,cut,b⟩ : DepthSplit) ∉ subtree.nodes := by
        intro hm
        have h := subtree.node_bounds hm
        simp only at h
        omega
      have rootSame := hq _ rootOutside
      have siblingSame : source r q = source r p := by
        apply source_congr
        intro s hm
        apply hq s
        intro hsub
        have h₁ := r.node_bounds hm
        have h₂ := subtree.node_bounds hsub
        omega
      rw [PreferredContext.plug_append]
      change Source.fork record (PreferredContext.plug (source subtree q) frames) (source r p) = _
      rw [hplug q hq]
      simp only [source,rootSame,siblingSame,record]
  | @right a b cut x y ha hb l r subtree bit below ih =>
    obtain ⟨lc,rc,hl,hr,same⟩ := represented.right_view bit
    obtain ⟨sub,frames,hs,he,hbefore,hafter,hplug⟩ := ih rc hr
    let record : Cached := (0,⟨cut,((⟨a,cut,b⟩,p ⟨a,cut,b⟩),false)⟩)
    let frame : ContextFrame (α := Nat) followsRight := .right record (source l p) lc rfl bit hl
    have bounds := below.bounds
    refine ⟨sub,frames ++ [frame],hs,?_,?_,?_,?_⟩
    · rw [PreferredContext.wrap_append]
      exact same.trans (frame.equivalent he)
    · intro e hm
      simp only [PreferredContext.before_append,PreferredContext.before,ContextFrame.before,
        frame,List.nil_append,List.singleton_append,List.mem_cons] at hm
      rcases hm with hm | hm
      · subst e
        change cut < x
        omega
      · exact hbefore e hm
    · simpa only [PreferredContext.after_append,PreferredContext.after,ContextFrame.after,
        frame,List.nil_append,List.append_nil] using hafter
    · intro q hq
      have rootOutside : (⟨a,cut,b⟩ : DepthSplit) ∉ subtree.nodes := by
        intro hm
        have h := subtree.node_bounds hm
        simp only at h
        omega
      have rootSame := hq _ rootOutside
      have siblingSame : source l q = source l p := by
        apply source_congr
        intro s hm
        apply hq s
        intro hsub
        have h₁ := l.node_bounds hm
        have h₂ := subtree.node_bounds hsub
        omega
      rw [PreferredContext.plug_append]
      change Source.fork record (source l p) (PreferredContext.plug (source subtree q) frames) = _
      rw [hplug q hq]
      simp only [source,rootSame,siblingSame,record]

end ChaCha.Paper20261030.SecondaryDecomposition
