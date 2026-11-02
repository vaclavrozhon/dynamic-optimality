import ChaCha.Paper20261030.SecondaryCore
import ChaCha.Paper20261030.BuiltCore

/-!
# Secondary preferred paths in separator order

The BST representation sorts the internal records of a preferred path
by the reference split label, rather than by reference depth. `word`
performs this ordering directly along the path. It contains exactly the
same records as the depth-ordered core, has strictly increasing separator
keys, and has length at most the secondary reference height.
-/

namespace ChaCha.Paper20261030.SeparatorPath

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open Auxiliary Auxiliary.Metadata RouterProjection

abbrev Record := SecondaryCore.Record
abbrev Entry := SecondaryCore.Entry

def rekey (entry : Entry) : Entry := ⟨entry.2.1.cut,entry.2⟩

def word : {a b : Nat} → DepthTree a b → (DepthSplit → Bool) → List Entry
  | _,_,.leaf _,_ => []
  | a,b,.node cut _ _ l r,preference =>
    if preference ⟨a,cut,b⟩ then
      ⟨cut,(⟨a,cut,b⟩,true)⟩ :: word r preference
    else word l preference ++ [⟨cut,(⟨a,cut,b⟩,false)⟩]

theorem word_perm (start : Nat) {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) :
    (word reference preference).Perm ((SecondaryCore.word start reference preference).map rekey) := by
  induction reference generalizing start with
  | leaf => exact .refl []
  | @node a b cut ha hb l r ihl ihr =>
    cases hp : preference ⟨a,cut,b⟩
    · simp only [word,SecondaryCore.word,hp,Bool.false_eq_true,if_false,List.map_cons,rekey]
      exact (List.perm_append_comm).trans (List.Perm.cons _ (ihl (start + 1)))
    · simp only [word,SecondaryCore.word,hp,if_true,List.map_cons,rekey]
      exact List.Perm.cons _ (ihr (start + 1))

theorem mem_word {a b : Nat} (reference : DepthTree a b) (preference : DepthSplit → Bool)
    {entry : Entry} (he : entry ∈ word reference preference) :
    entry.2.1 ∈ reference.nodes ∧ entry.1 = entry.2.1.cut := by
  have hm := (word_perm 0 reference preference).mem_iff.mp he
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hm
  exact ⟨(SecondaryCore.mem_word 0 reference preference ho).1,rfl⟩

theorem key_bounds {a b : Nat} (reference : DepthTree a b) (preference : DepthSplit → Bool)
    {entry : Entry} (he : entry ∈ word reference preference) : a ≤ entry.1 ∧ entry.1 < b := by
  obtain ⟨hm,hkey⟩ := mem_word reference preference he
  have hb := reference.node_bounds hm
  omega

theorem keys_increasing {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) :
    (word reference preference).Pairwise (fun e f => e.1 < f.1) := by
  induction reference with
  | leaf => exact .nil
  | @node a b cut ha hb l r ihl ihr =>
    cases hp : preference ⟨a,cut,b⟩
    · simp only [word,hp,Bool.false_eq_true,if_false]
      apply List.pairwise_append.mpr
      refine ⟨ihl,by simp,?_⟩
      intro e he f hf
      have hf' : f = ⟨cut,(⟨a,cut,b⟩,false)⟩ := List.mem_singleton.mp hf
      subst f
      exact (key_bounds l preference he).2
    · simp only [word,hp,if_true]
      apply List.pairwise_cons.mpr
      refine ⟨?_,ihr⟩
      intro e he
      have hb := (key_bounds r preference he).1
      change cut < e.1
      omega

theorem word_length {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) :
    (word reference preference).length ≤ (LocalReferences.depthReference reference).height := by
  have he := (word_perm 0 reference preference).length_eq
  rw [List.length_map] at he
  rw [he]
  exact SecondaryCore.word_length 0 reference preference

def inInterval (lo hi : Nat) (entry : Entry) : Bool := decide (lo ≤ entry.1 ∧ entry.1 < hi)

theorem filter_whole {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) :
    (word reference preference).filter (inInterval a b) = word reference preference := by
  apply List.filter_eq_self.mpr
  intro e he
  exact decide_eq_true (key_bounds reference preference he)

/-- A preferred descendant is reached using only the stored preference bits. -/
inductive Descendant (preference : DepthSplit → Bool) :
    {a b c d : Nat} → DepthTree a b → DepthTree c d → Prop
  | refl {a b : Nat} (reference : DepthTree a b) : Descendant preference reference reference
  | left {a b cut c d : Nat} (ha : a ≤ cut) (hb : cut < b)
      (l : DepthTree a cut) (r : DepthTree (cut + 1) b) (subtree : DepthTree c d)
      (bit : preference ⟨a,cut,b⟩ = false) (below : Descendant preference l subtree) :
      Descendant preference (.node cut ha hb l r) subtree
  | right {a b cut c d : Nat} (ha : a ≤ cut) (hb : cut < b)
      (l : DepthTree a cut) (r : DepthTree (cut + 1) b) (subtree : DepthTree c d)
      (bit : preference ⟨a,cut,b⟩ = true) (below : Descendant preference r subtree) :
      Descendant preference (.node cut ha hb l r) subtree

theorem Descendant.bounds {preference : DepthSplit → Bool} {a b c d : Nat}
    {reference : DepthTree a b} {subtree : DepthTree c d}
    (h : Descendant preference reference subtree) : a ≤ c ∧ d ≤ b := by
  induction h with
  | refl => exact ⟨le_rfl,le_rfl⟩
  | left ha hb l r subtree bit below ih => omega
  | right ha hb l r subtree bit below ih => omega

/-- The suffix beginning at any preferred descendant is exactly the
separator interval of that descendant, including all its record values. -/
theorem Descendant.interval_suffix {preference : DepthSplit → Bool} {a b c d : Nat}
    {reference : DepthTree a b} {subtree : DepthTree c d}
    (h : Descendant preference reference subtree) :
    (word reference preference).filter (inInterval c d) = word subtree preference := by
  induction h with
  | refl => exact filter_whole _ _
  | @left a b cut c d ha hb l r subtree bit below ih =>
    have hb := below.bounds
    have hn : inInterval c d ⟨cut,(⟨a,cut,b⟩,false)⟩ = false := by
      simp only [inInterval,decide_eq_false_iff_not]
      omega
    simp only [word,bit,Bool.false_eq_true,if_false,List.filter_append,List.filter_cons,
      hn,Bool.false_eq_true,List.filter_nil,List.append_nil,ih]
  | @right a b cut c d ha hb l r subtree bit below ih =>
    have hb := below.bounds
    have hn : inInterval c d ⟨cut,(⟨a,cut,b⟩,true)⟩ = false := by
      simp only [inInterval,decide_eq_false_iff_not]
      omega
    simp only [word,bit,if_true,List.filter_cons,hn,Bool.false_eq_true,if_false,ih]

end ChaCha.Paper20261030.SeparatorPath
