import ChaCha.Paper20261030.NeighborSemantics
import ChaCha.Paper20261030.SecondaryContext

/-!
# A preferred-path departure is one of the two observed neighbors

For an exit to the right of a left-preferring split, the split is the
greatest path separator below the requested depth. For the opposite exit,
it is the least path separator at least that depth. Preferred ancestors
lie outside the split interval, and the old preferred continuation lies
entirely on the other side of its separator. Both claims concern exact
records, including their split identities and preference bits.
-/

namespace ChaCha.Paper20261030.SeparatorPath

theorem right_exit_neighbor {a b x y cut : Nat} {p : DepthSplit → Bool}
    {reference : DepthTree a b} (hx : x ≤ cut) (hy : cut < y)
    (l : DepthTree x cut) (r : DepthTree (cut + 1) y)
    (below : Descendant p reference (.node cut hx hy l r))
    (bit : p ⟨x,cut,y⟩ = false) (d : Nat) (hd : cut < d) (hdhi : d ≤ y) :
    ((word reference p).filter (fun e => decide (e.1 < d))).getLast? =
      some ⟨cut,(⟨x,cut,y⟩,false)⟩ := by
  obtain ⟨before,after,hw,hbefore,hafter,hchange⟩ := below.word_context
  have hb : before.filter (fun e => decide (e.1 < d)) = before := by
    apply List.filter_eq_self.mpr
    intro e he
    have := hbefore e he
    exact decide_eq_true (by omega)
  have hl : (word l p).filter (fun e => decide (e.1 < d)) = word l p := by
    apply List.filter_eq_self.mpr
    intro e he
    have := (key_bounds l p he).2
    exact decide_eq_true (by omega)
  have ha : after.filter (fun e => decide (e.1 < d)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he hf
    have := hafter e he
    have := of_decide_eq_true hf
    omega
  rw [hw]
  simp [word,bit,List.filter_append,hb,hl,ha,hd,List.getLast?_append]

theorem left_exit_neighbor {a b x y cut : Nat} {p : DepthSplit → Bool}
    {reference : DepthTree a b} (hx : x ≤ cut) (hy : cut < y)
    (l : DepthTree x cut) (r : DepthTree (cut + 1) y)
    (below : Descendant p reference (.node cut hx hy l r))
    (bit : p ⟨x,cut,y⟩ = true) (d : Nat) (hdlo : x ≤ d) (hd : d ≤ cut) :
    ((word reference p).filter (fun e => decide (d ≤ e.1))).head? =
      some ⟨cut,(⟨x,cut,y⟩,true)⟩ := by
  obtain ⟨before,after,hw,hbefore,hafter,hchange⟩ := below.word_context
  have hb : before.filter (fun e => decide (d ≤ e.1)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he hf
    have := hbefore e he
    have := of_decide_eq_true hf
    omega
  have hr : (word r p).filter (fun e => decide (d ≤ e.1)) = word r p := by
    apply List.filter_eq_self.mpr
    intro e he
    have := (key_bounds r p he).1
    exact decide_eq_true (by omega)
  have ha : after.filter (fun e => decide (d ≤ e.1)) = after := by
    apply List.filter_eq_self.mpr
    intro e he
    have := hafter e he
    exact decide_eq_true (by omega)
  rw [hw]
  simp [word,bit,List.filter_append,hb,hr,ha,hd,List.head?_append]

end ChaCha.Paper20261030.SeparatorPath

namespace ChaCha.Paper20261030.SecondaryDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem represented_neighbors {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    (neighbors d c.core).1 =
        (((SeparatorPath.word reference p).filter (fun e => decide (e.1 < d))).getLast?).map markEntry ∧
      (neighbors d c.core).2 =
        (((SeparatorPath.word reference p).filter (fun e => decide (d ≤ e.1))).head?).map markEntry := by
  obtain ⟨hl,hr⟩ := neighbors_correct d c.core (represented_ordered reference p c represented)
  rw [hl,hr,represented_word reference p c represented]
  simp only [List.filter_map,List.getLast?_map,List.head?_map]
  exact ⟨rfl,rfl⟩

theorem observed_right_exit {a b x y cut : Nat} (hx : x ≤ cut) (hy : cut < y)
    (l : DepthTree x cut) (r : DepthTree (cut + 1) y) (reference : DepthTree a b)
    (p : DepthSplit → Bool) (below : SeparatorPath.Descendant p reference (.node cut hx hy l r))
    (bit : p ⟨x,cut,y⟩ = false) (d : Nat) (hd : cut < d) (hdhi : d ≤ y)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    (neighbors d c.core).1 = some ⟨cut,((⟨x,cut,y⟩,false),false)⟩ := by
  rw [(represented_neighbors reference p d c represented).1,
    SeparatorPath.right_exit_neighbor hx hy l r below bit d hd hdhi]
  rfl

theorem observed_left_exit {a b x y cut : Nat} (hx : x ≤ cut) (hy : cut < y)
    (l : DepthTree x cut) (r : DepthTree (cut + 1) y) (reference : DepthTree a b)
    (p : DepthSplit → Bool) (below : SeparatorPath.Descendant p reference (.node cut hx hy l r))
    (bit : p ⟨x,cut,y⟩ = true) (d : Nat) (hdlo : x ≤ d) (hd : d ≤ cut)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    (neighbors d c.core).2 = some ⟨cut,((⟨x,cut,y⟩,true),false)⟩ := by
  rw [(represented_neighbors reference p d c represented).2,
    SeparatorPath.left_exit_neighbor hx hy l r below bit d hdlo hd]
  rfl

end ChaCha.Paper20261030.SecondaryDecomposition
