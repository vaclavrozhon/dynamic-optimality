import ChaCha.Paper20261030.SecondaryInteriorRepair
import ChaCha.Paper20261030.DepthPreferences
import ChaCha.Paper20261030.DepartureTest

/-!
# An abstract secondary head step identifies one preferred reference split

The already counted `PrefRouter.HeadStep` changes the first wrong edge.
This file identifies its exact static depth-reference split and proves
that updating that one persistent bit gives the decoded target tree.
-/

namespace ChaCha.Paper20261030.SeparatorPath

theorem Descendant.node_mem {p : DepthSplit → Bool} {a b x y : Nat}
    {reference : DepthTree a b} {subtree : DepthTree x y}
    (below : Descendant p reference subtree) {s : DepthSplit} (hs : s ∈ subtree.nodes) :
    s ∈ reference.nodes := by
  induction below with
  | refl => exact hs
  | left ha hb l r subtree bit below ih => simp [DepthTree.nodes,ih hs]
  | right ha hb l r subtree bit below ih => simp [DepthTree.nodes,ih hs]

end ChaCha.Paper20261030.SeparatorPath

namespace ChaCha.Paper20261030.SecondaryDecomposition

open PreferredProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

def decodeSource : Source Nat Cached → PrefRouter Nat
  | .leaf key _ => .leaf key
  | .fork record l r => .fork (followsRight record) (decodeSource l) (decodeSource r)

theorem decodeSource_source {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool) :
    decodeSource (source reference p) = Secondary.decodeDepth reference p := by
  induction reference <;> simp_all [source,decodeSource,followsRight,Secondary.decodeDepth]

theorem decode_update_outside {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (split : DepthSplit) (fresh : Bool) (outside : split ∉ reference.nodes) :
    Secondary.decodeDepth reference (Function.update p split fresh) = Secondary.decodeDepth reference p := by
  have same : source reference (Function.update p split fresh) = source reference p := by
    apply source_congr
    intro s hs
    have hne : s ≠ split := by intro he; subst s; exact outside hs
    exact Function.update_of_ne hne _ _
  simpa only [decodeSource_source] using congrArg decodeSource same

theorem decode_flip_root {a b cut : Nat} (ha : a ≤ cut) (hb : cut < b)
    (l : DepthTree a cut) (r : DepthTree (cut + 1) b) (p : DepthSplit → Bool) (fresh : Bool) :
    Secondary.decodeDepth (.node cut ha hb l r) (Function.update p ⟨a,cut,b⟩ fresh) =
      .fork fresh (Secondary.decodeDepth l p) (Secondary.decodeDepth r p) := by
  have same := congrArg decodeSource (source_flip_root ha hb l r p fresh)
  simpa only [decodeSource_source,decodeSource,followsRight] using same

structure PreferredSplit {a b : Nat} (p : DepthSplit → Bool) (reference : DepthTree a b) where
  split : DepthSplit
  lo_le_cut : split.lo ≤ split.cut
  cut_lt_hi : split.cut < split.hi
  left : DepthTree split.lo split.cut
  right : DepthTree (split.cut + 1) split.hi
  below : SeparatorPath.Descendant p reference (.node split.cut lo_le_cut cut_lt_hi left right)

theorem PreferredSplit.mem {a b : Nat} {p : DepthSplit → Bool} {reference : DepthTree a b}
    (v : PreferredSplit p reference) : v.split ∈ reference.nodes :=
  v.below.node_mem (by simp [DepthTree.nodes])

theorem decoded_head_pivot_spec {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    {request depth : Nat} {after : PrefRouter Nat}
    (step : PrefRouter.HeadStep request depth (Secondary.decodeDepth reference p) after) :
    ∃ v : PreferredSplit p reference,
      Secondary.decodeDepth reference (Function.update p v.split (!p v.split)) = after ∧
        SeparatorPath.Exit request ⟨v.split.cut,(v.split,p v.split)⟩ := by
  induction reference generalizing p depth after with
  | leaf a => cases step
  | @node a b cut ha hb l r ihl ihr =>
    cases bit : p ⟨a,cut,b⟩
    · simp only [Secondary.decodeDepth,bit] at step
      cases step with
      | rightRoot _ _ hl hr =>
        refine ⟨⟨⟨a,cut,b⟩,ha,hb,l,r,.refl _⟩,?_,?_⟩
        · rw [decode_flip_root]
          simp only [bit,Bool.not_false]
        · have bounds := (Secondary.decodeDepth_mem r p request).mp hr
          change a ≤ request ∧ request ≤ b ∧ p ⟨a,cut,b⟩ ≠ decide (cut < request)
          refine ⟨by omega,bounds.2,?_⟩
          simp [bit,show cut < request by omega]
      | leftDown _ step =>
        obtain ⟨v,he,exit⟩ := ihl p step
        let lifted : PreferredSplit p (.node cut ha hb l r) :=
          ⟨v.split,v.lo_le_cut,v.cut_lt_hi,v.left,v.right,.left ha hb l r _ bit v.below⟩
        have bounds := l.node_bounds v.mem
        have rootNe : (⟨a,cut,b⟩ : DepthSplit) ≠ v.split := by
          intro hn
          have := congrArg DepthSplit.cut hn
          simp only at this
          omega
        have outside : v.split ∉ r.nodes := by
          intro hm
          have := r.node_bounds hm
          omega
        refine ⟨lifted,?_,exit⟩
        change Secondary.decodeDepth (.node cut ha hb l r) (Function.update p v.split (!p v.split)) = _
        rw [Secondary.decodeDepth,Function.update_of_ne rootNe,bit,he,decode_update_outside r p _ _ outside]
    · simp only [Secondary.decodeDepth,bit] at step
      cases step with
      | leftRoot _ _ hl =>
        refine ⟨⟨⟨a,cut,b⟩,ha,hb,l,r,.refl _⟩,?_,?_⟩
        · rw [decode_flip_root]
          simp only [bit,Bool.not_true]
        · have bounds := (Secondary.decodeDepth_mem l p request).mp hl
          change a ≤ request ∧ request ≤ b ∧ p ⟨a,cut,b⟩ ≠ decide (cut < request)
          refine ⟨bounds.1,by omega,?_⟩
          simp [bit,show ¬ cut < request by omega]
      | rightDown _ hl step =>
        obtain ⟨v,he,exit⟩ := ihr p step
        let lifted : PreferredSplit p (.node cut ha hb l r) :=
          ⟨v.split,v.lo_le_cut,v.cut_lt_hi,v.left,v.right,.right ha hb l r _ bit v.below⟩
        have bounds := r.node_bounds v.mem
        have rootNe : (⟨a,cut,b⟩ : DepthSplit) ≠ v.split := by
          intro hn
          have := congrArg DepthSplit.cut hn
          simp only at this
          omega
        have outside : v.split ∉ l.nodes := by
          intro hm
          have := l.node_bounds hm
          omega
        refine ⟨lifted,?_,exit⟩
        change Secondary.decodeDepth (.node cut ha hb l r) (Function.update p v.split (!p v.split)) = _
        rw [Secondary.decodeDepth,Function.update_of_ne rootNe,bit,he,decode_update_outside l p _ _ outside]

theorem decoded_head_pivot {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    {request depth : Nat} {after : PrefRouter Nat}
    (step : PrefRouter.HeadStep request depth (Secondary.decodeDepth reference p) after) :
    ∃ v : PreferredSplit p reference,
      Secondary.decodeDepth reference (Function.update p v.split (!p v.split)) = after := by
  obtain ⟨v,decoded,_⟩ := decoded_head_pivot_spec reference p step
  exact ⟨v,decoded⟩

end ChaCha.Paper20261030.SecondaryDecomposition
