import TangoSquared.Paper20261030.PrimaryAddresses
import TangoSquared.Paper20261030.FragmentCount
import Mathlib.Data.Finset.Card

/-!
# The finite set of persistent secondary memories

A memory key consists of an internal secondary interval and the address
of a primary vertex at its starting depth. The set below enumerates these
actual pairs. Primary accesses preserve the set even when preferred paths
are reassembled. Its cardinality is bounded by the weighted interval count.
-/

namespace TangoSquared.Paper20261030.Secondary

open PreferredProjection

abbrev MemoryKey := DepthSplit × List Bool

def memoryKeys {α : Type*} (primary : PrefRouter α) :
    {a b : Nat} → DepthTree a b → Finset MemoryKey
  | _, _, .leaf _ => ∅
  | a, b, .node c _ _ l r =>
      (((primary.ownerPaths a).toFinset.image (fun u => (⟨a,c,b⟩,u))) ∪
        memoryKeys primary l) ∪ memoryKeys primary r

theorem memoryKeys_access {α : Type*} [DecidableEq α] (primary : PrefRouter α)
    {a b : Nat} (secondary : DepthTree a b) (x : α) :
    memoryKeys (primary.access x) secondary = memoryKeys primary secondary := by
  induction secondary with
  | leaf a => rfl
  | node c ha hb l r ihl ihr =>
    simp only [memoryKeys,PrefRouter.ownerPaths_access,ihl,ihr]

theorem mem_memoryKeys {α : Type*} (primary : PrefRouter α) {a b : Nat}
    (secondary : DepthTree a b) (s : DepthSplit) (u : List Bool) :
    (s,u) ∈ memoryKeys primary secondary ↔
      s ∈ secondary.nodes ∧ u ∈ primary.ownerPaths s.lo := by
  induction secondary with
  | leaf a => simp [memoryKeys,DepthTree.nodes]
  | @node a b c ha hb l r ihl ihr =>
    simp only [memoryKeys,Finset.mem_union,Finset.mem_image,List.mem_toFinset,ihl,ihr,
      DepthTree.nodes,Finset.mem_insert]
    constructor
    · rintro ((⟨v,hv,he⟩ | ⟨hs,hu⟩) | ⟨hs,hu⟩)
      · have he' := Prod.mk.inj he
        cases he'.1
        cases he'.2
        exact ⟨Or.inl rfl,hv⟩
      · exact ⟨Or.inr (Or.inl hs),hu⟩
      · exact ⟨Or.inr (Or.inr hs),hu⟩
    · rintro ⟨hs,hu⟩
      rcases hs with rfl | hs | hs
      · exact Or.inl (Or.inl ⟨u,hu,rfl⟩)
      · exact Or.inl (Or.inr ⟨hs,hu⟩)
      · exact Or.inr ⟨hs,hu⟩

theorem memoryKeys_card {α : Type*} [DecidableEq α] {primary : PrefRouter α}
    {H a b : Nat} (hp : primary.Perfect H) (secondary : DepthTree a b) (hb : b < H) :
    (memoryKeys primary secondary).card ≤ memoryCount secondary := by
  induction secondary with
  | leaf a => simp [memoryKeys,memoryCount]
  | @node a b c ha hcb l r ihl ihr =>
    have hl := ihl (by omega)
    have hr := ihr hb
    have howner : (primary.ownerPaths a).length = 2 ^ a :=
      PrefRouter.ownerPaths_length hp (by omega)
    have hroot := Finset.card_image_le (s := (primary.ownerPaths a).toFinset)
      (f := fun u => ((⟨a,c,b⟩ : DepthSplit),u))
    have hlist := List.toFinset_card_le (l := primary.ownerPaths a)
    have hfirst := Finset.card_union_le
      ((primary.ownerPaths a).toFinset.image (fun u => ((⟨a,c,b⟩ : DepthSplit),u)))
      (memoryKeys primary l)
    have hsecond := Finset.card_union_le
      (((primary.ownerPaths a).toFinset.image (fun u => ((⟨a,c,b⟩ : DepthSplit),u))) ∪
        memoryKeys primary l) (memoryKeys primary r)
    simp only [memoryKeys,memoryCount]
    omega

/-- There is no allocation proportional to a full secondary reference per
primary leaf: the actual genuine memory set is linear in the leaf count. -/
theorem root_memoryKeys_card {α : Type*} [DecidableEq α] {primary : PrefRouter α}
    {h : Nat} (hp : primary.Perfect (h + 1)) (secondary : DepthTree 0 h) :
    (memoryKeys primary secondary).card + 1 ≤ 2 ^ h := by
  have hk := memoryKeys_card hp secondary (by omega)
  have hc := root_memoryCount_bound secondary
  omega

end TangoSquared.Paper20261030.Secondary
