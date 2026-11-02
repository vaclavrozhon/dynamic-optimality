import ChaCha.Paper20261030.CanonicalOwners
import ChaCha.Paper20261030.FiberSums

/-!
# Summing memory alternations over the concrete fragment hierarchy

Distinct internal reference intervals have disjoint memory keys. At each
interval, actual owner addresses enumerate exactly the dyadic block indices.
Unvisited owners contribute zero, leaving the same sum as the rectangle
decomposition. This closes the LCA-count bridge for the bit-array algorithm.
-/

namespace ChaCha.Paper20261030.Secondary

open PreferredProjection
open scoped BigOperators

def rootMemoryKeys {α : Type*} (primary : PrefRouter α) (a c b : Nat) : Finset MemoryKey :=
  (primary.ownerPaths a).toFinset.image (fun u => ((⟨a,c,b⟩ : DepthSplit),u))

theorem memoryKeys_disjoint_left {α : Type*} (primary : PrefRouter α)
    {a c b : Nat} (hb : c < b) (left : DepthTree a c) :
    Disjoint (rootMemoryKeys primary a c b) (memoryKeys primary left) := by
  apply Finset.disjoint_left.mpr
  intro key hk hl
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hk
  have hs := ((mem_memoryKeys primary left ⟨a,c,b⟩ u).mp hl).1
  have he := (left.node_bounds hs).2.2.2
  change b ≤ c at he
  omega

theorem memoryKeys_disjoint_right {α : Type*} (primary : PrefRouter α)
    {a c b : Nat} (ha : a ≤ c) (right : DepthTree (c + 1) b) :
    Disjoint (rootMemoryKeys primary a c b) (memoryKeys primary right) := by
  apply Finset.disjoint_left.mpr
  intro key hk hr
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hk
  have hs := ((mem_memoryKeys primary right ⟨a,c,b⟩ u).mp hr).1
  have he := (right.node_bounds hs).1
  change c + 1 ≤ a at he
  omega

theorem memoryKeys_disjoint_children {α : Type*} (primary : PrefRouter α)
    {a c b : Nat} (left : DepthTree a c) (right : DepthTree (c + 1) b) :
    Disjoint (memoryKeys primary left) (memoryKeys primary right) := by
  apply Finset.disjoint_left.mpr
  intro key hl hr
  have hsl := ((mem_memoryKeys primary left key.1 key.2).mp hl).1
  have hsr := ((mem_memoryKeys primary right key.1 key.2).mp hr).1
  obtain ⟨_,hlo,hcut,hhi⟩ := left.node_bounds hsl
  have hlo' := (right.node_bounds hsr).1
  omega

theorem memoryLCA_node {α : Type*} [DecidableEq α] (primary : PrefRouter α)
    {a c b : Nat} (ha : a ≤ c) (hb : c < b)
    (left : DepthTree a c) (right : DepthTree (c + 1) b) (xs : List α) :
    memoryLCA primary (.node c ha hb left right) xs =
      (∑ u ∈ (primary.ownerPaths a).toFinset, keyLCA primary (⟨a,c,b⟩,u) xs) +
        memoryLCA primary left xs + memoryLCA primary right xs := by
  have hl := memoryKeys_disjoint_left primary hb left
  have hr := memoryKeys_disjoint_right primary ha right
  have hc := memoryKeys_disjoint_children primary left right
  have houter := Finset.disjoint_union_left.mpr ⟨hr,hc⟩
  simp only [rootMemoryKeys] at hl houter
  simp only [memoryLCA,memoryKeys]
  rw [Finset.sum_union houter,Finset.sum_union hl,Finset.sum_image]
  intro u hu v hv he
  exact (Prod.mk.inj he).2

end ChaCha.Paper20261030.Secondary

namespace ChaCha.Paper20261030.Dyadic

open PreferredProjection Rectangles Secondary
open scoped BigOperators

theorem sum_all_owners {H a c b : Nat} (ha : a ≤ H) (P : Finset Point)
    (hkeys : ∀ p ∈ P, ValidKey H p.1) :
    (∑ i ∈ (canonical a 0).leaves.toFinset,
      lcaTransitions H c b (fiber (coarsen H a) i P)) =
      ∑ i ∈ P.image (fun p => coarsen H a p.1),
        lcaTransitions H c b (fiber (coarsen H a) i P) := by
  have hsub : P.image (fun p => coarsen H a p.1) ⊆ (canonical a 0).leaves.toFinset := by
    intro i hi
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hi
    apply List.mem_toFinset.mpr
    exact (canonical_zero_mem a _).mpr (coarsen_valid ha (hkeys p hp))
  symm
  apply Finset.sum_subset hsub
  intro i hi hnot
  have hf : fiber (coarsen H a) i P = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
    exact hnot (Finset.mem_image.mpr ⟨p,hp,he⟩)
  simp [hf,lcaTransitions,eventCount]

theorem root_memory_count {H a c b : Nat} (ha : a ≤ c) (hcb : c ≤ b) (hb : b < H)
    (ps : List Point) (hs : Chronological ps) (hkeys : ∀ p ∈ ps, ValidKey H p.1) :
    (∑ u ∈ ((canonical H 0).ownerPaths a).toFinset,
      keyLCA (canonical H 0) (⟨a,c,b⟩,u) (ps.map Prod.fst)) =
      ∑ i ∈ ps.toFinset.image (fun p => coarsen H a p.1),
        lcaTransitions H (c + 1) (b + 1) (fiber (coarsen H a) i ps.toFinset) := by
  calc
    _ = ∑ u ∈ ((canonical H 0).ownerPaths a).toFinset,
        lcaTransitions H (c + 1) (b + 1)
          (fiber (coarsen H a) (descendantIndex 0 u) ps.toFinset) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hlen := (PrefRouter.mem_ownerPaths.mp (List.mem_toFinset.mp hu)).1
      exact canonical_key_count ⟨a,c,b⟩ u hlen ha hcb hb ps hs hkeys
    _ = ∑ i ∈ (canonical a 0).leaves.toFinset,
        lcaTransitions H (c + 1) (b + 1) (fiber (coarsen H a) i ps.toFinset) := by
      rw [← owner_indices H a (by omega) 0,Finset.sum_image]
      exact owner_index_injective H a (by omega)
    _ = _ := sum_all_owners (by omega) ps.toFinset
      (fun p hp => hkeys p (List.mem_toFinset.mp hp))

theorem memoryLCA_eq_flat {H a b : Nat} (reference : DepthTree a b) (hb : b < H)
    (ps : List Point) (hs : Chronological ps) (hkeys : ∀ p ∈ ps, ValidKey H p.1) :
    memoryLCA (canonical H 0) reference (ps.map Prod.fst) = flatLCA H reference ps.toFinset := by
  induction reference with
  | leaf a => simp [memoryLCA,memoryKeys,flatLCA]
  | @node a b c ha hcb l r ihl ihr =>
    rw [memoryLCA_node,root_memory_count ha (by omega) hb ps hs hkeys,ihl (by omega),ihr hb]
    rfl

/-- The concrete algorithm's LCA count is exactly the rectangle theorem's
LCA count, including first visits and repeated access keys. -/
theorem memoryLCA_eq_lcaBound {h : Nat} (reference : DepthTree 0 h) (xs : List Int)
    (hkeys : ∀ x ∈ xs, ValidKey (h + 1) x) :
    memoryLCA (canonical (h + 1) 0) reference xs =
      lcaBound (h + 1) reference (accessPoints xs) := by
  have hps : ∀ p ∈ pointWord 0 xs, ValidKey (h + 1) p.1 := by
    intro p hp
    have hm : p.1 ∈ (pointWord 0 xs).map Prod.fst := List.mem_map.mpr ⟨p,hp,rfl⟩
    rw [pointWord_keys] at hm
    exact hkeys _ hm
  have he := memoryLCA_eq_flat reference (by omega) (pointWord 0 xs)
    (pointWord_chronological 0 xs) hps
  rw [pointWord_keys,root_flatLCA reference (by omega) _
    (fun p hp => hps p (List.mem_toFinset.mp hp)),pointWord_toFinset] at he
  exact he

theorem memoryLCA_le_rectangleBound {h : Nat} (reference : DepthTree 0 h) (xs : List Int)
    (hkeys : ∀ x ∈ xs, ValidKey (h + 1) x) :
    memoryLCA (canonical (h + 1) 0) reference xs ≤ 5 * rectangleBound (accessPoints xs) := by
  rw [memoryLCA_eq_lcaBound reference xs hkeys]
  exact sequence_lcaBound reference xs hkeys

/-- The rectangle upper bound for genuine secondary flips in the concrete
abstract algorithm. Physical BST operation cost is not asserted here. -/
theorem secondaryCost_rectangle_bound {h : Nat} (reference : DepthTree 0 h) (xs : List Int)
    (hkeys : ∀ x ∈ xs, ValidKey (h + 1) x) :
    secondaryCost reference (MemoryState.initial (canonical (h + 1) 0)) xs ≤
      10 * rectangleBound (accessPoints xs) + 2 * (canonical (h + 1) 0).primaryWilber xs +
      5 * (canonical (h + 1) 0).internalVertices := by
  have hflips := secondary_flip_bound reference (MemoryState.initial (canonical (h + 1) 0))
    (canonical_perfect _ _) (canonical_nodup _ _) xs
    (fun x hx => (canonical_zero_mem _ _).mpr (hkeys x hx))
  have hlca := memoryLCA_le_rectangleBound reference xs hkeys
  dsimp only [MemoryState.initial] at hflips ⊢
  omega

end ChaCha.Paper20261030.Dyadic
