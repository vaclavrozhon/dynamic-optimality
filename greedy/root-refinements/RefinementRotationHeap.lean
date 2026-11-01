import HeapSubtreeGeometry
import Splay.Tree.Rotation

/-!
Actual fixed-rank canonical heap changes under a concrete refinement
rotation. The proof deliberately uses a coarser four-record support rather
than the sharper five-port bound of two: only light children at the two
rotated internal nodes can have a changed parent. This constant is enough
for recanonicalization administration, and includes arbitrary whole fringe
subtrees and contextual rotation depth.
-/

namespace GreedyMerge.RefinementRotation

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open HeapGeometry ComparatorHeap

abbrev ParentPair (n : ℕ) := External n × External n

def edgePair {n : ℕ} (edge : Edge n) : ParentPair n := (edge.owner, edge.child)

theorem local_pairs_depth_independent {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) (first second : ℕ) :
    (edgesAtNode snapshot node first).map edgePair =
      (edgesAtNode snapshot node second).map edgePair := by
  simp only [edgesAtNode, List.map_map]
  rfl

theorem tree_pairs_depth_independent {n lo hi : ℕ} (snapshot : Snapshot n)
    (tree : BST lo hi) (hhi : hi ≤ n) (first second : ℕ) :
    (treeEdges snapshot tree hhi first).map edgePair =
      (treeEdges snapshot tree hhi second).map edgePair := by
  induction tree generalizing first second with
  | empty => rfl
  | @node lo root hi left right ihLeft ihRight =>
      simp only [treeEdges, List.map_append]
      rw [local_pairs_depth_independent snapshot _ first second,
        ihLeft _ (first + 1) (second + 1), ihRight _ (first + 1) (second + 1)]

noncomputable def pairs {n lo hi : ℕ} (snapshot : Snapshot n)
    (tree : BST lo hi) (hhi : hi ≤ n) : List (ParentPair n) :=
  (treeEdges snapshot tree hhi 0).map edgePair

noncomputable def nodePairs {n : ℕ} (snapshot : Snapshot n) (node : AtNode n) :
    List (ParentPair n) := (edgesAtNode snapshot node 0).map edgePair

@[simp] theorem pairs_empty {n lo : ℕ} (snapshot : Snapshot n) (hlo : lo ≤ n) :
    pairs snapshot (.empty lo) hlo = [] := rfl

theorem pairs_node {n lo root hi : ℕ} (snapshot : Snapshot n)
    (left : BST lo root) (right : BST (root+1) hi) (hhi : hi ≤ n) :
    pairs snapshot (.node left right) hhi =
      nodePairs snapshot ⟨lo, root, hi, left, right, hhi⟩ ++
      pairs snapshot left (by have := right.lower_le_upper; omega) ++
      pairs snapshot right hhi := by
  unfold pairs
  simp only [treeEdges, List.map_append]
  rw [tree_pairs_depth_independent snapshot left _ 1 0,
    tree_pairs_depth_independent snapshot right _ 1 0]
  rfl

@[simp] theorem nodePairs_length {n : ℕ} (snapshot : Snapshot n) (node : AtNode n) :
    (nodePairs snapshot node).length = 2 := by
  simp only [nodePairs, List.length_map, length_edgesAtNode]

/-- Internal child shapes do not affect the local two parent pairs. -/
theorem nodePairs_shapes {n lo root hi : ℕ} (snapshot : Snapshot n)
    (left₁ left₂ : BST lo root) (right₁ right₂ : BST (root+1) hi) (hhi : hi ≤ n) :
    nodePairs snapshot ⟨lo,root,hi,left₁,right₁,hhi⟩ =
      nodePairs snapshot ⟨lo,root,hi,left₂,right₂,hhi⟩ := rfl

/-- Outside the four old local child slots, every parent pair survives a
root refinement rotation. -/
theorem root_rotation_pair_support {n lo hi : ℕ} (snapshot : Snapshot n)
    {before after : BST lo hi} (rotation : RootRotation before after) (hhi : hi ≤ n) :
    ∃ selected : Finset (External n), selected.card ≤ 4 ∧
      ∀ pair ∈ pairs snapshot before hhi, pair.2 ∉ selected → pair ∈ pairs snapshot after hhi := by
  classical
  cases rotation with
  | @right promoted demoted hi a b c =>
      have hab : promoted ≤ n := by have := b.lower_le_upper; have := c.lower_le_upper; omega
      have hb : demoted ≤ n := by have := c.lower_le_upper; omega
      let outer : AtNode n := ⟨lo,demoted,hi,.node a b,c,hhi⟩
      let inner : AtNode n := ⟨lo,promoted,demoted,a,b,hb⟩
      let localPairs := nodePairs snapshot outer ++ nodePairs snapshot inner
      let selected := (localPairs.map Prod.snd).toFinset
      refine ⟨selected, ?_, ?_⟩
      · have bound := List.toFinset_card_le (localPairs.map Prod.snd)
        simp only [List.length_map, localPairs, List.length_append, nodePairs_length] at bound
        exact bound
      · intro pair member outside
        have notOuter : pair ∉ nodePairs snapshot outer := by
          intro localMember
          apply outside
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨pair, List.mem_append_left _ localMember, rfl⟩)
        have notInner : pair ∉ nodePairs snapshot inner := by
          intro localMember
          apply outside
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨pair, List.mem_append_right _ localMember, rfl⟩)
        simp only [pairs_node, List.mem_append] at member ⊢
        change ((pair ∈ nodePairs snapshot outer ∨
          ((pair ∈ nodePairs snapshot inner ∨ pair ∈ pairs snapshot a hab) ∨ pair ∈ pairs snapshot b hb)) ∨
          pair ∈ pairs snapshot c hhi) at member
        rcases member with (oldOuter | (oldInner | inA) | inB) | inC
        · exact False.elim (notOuter oldOuter)
        · exact False.elim (notInner oldInner)
        · exact Or.inl (Or.inr inA)
        · exact Or.inr (Or.inl (Or.inr inB))
        · exact Or.inr (Or.inr inC)
  | @left demoted promoted hi a b c =>
      have ha : demoted ≤ n := by have := b.lower_le_upper; have := c.lower_le_upper; omega
      have hb : promoted ≤ n := by have := c.lower_le_upper; omega
      let outer : AtNode n := ⟨lo,demoted,hi,a,.node b c,hhi⟩
      let inner : AtNode n := ⟨demoted+1,promoted,hi,b,c,hhi⟩
      let localPairs := nodePairs snapshot outer ++ nodePairs snapshot inner
      let selected := (localPairs.map Prod.snd).toFinset
      refine ⟨selected, ?_, ?_⟩
      · have bound := List.toFinset_card_le (localPairs.map Prod.snd)
        simp only [List.length_map, localPairs, List.length_append, nodePairs_length] at bound
        exact bound
      · intro pair member outside
        have notOuter : pair ∉ nodePairs snapshot outer := by
          intro localMember
          apply outside
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨pair, List.mem_append_left _ localMember, rfl⟩)
        have notInner : pair ∉ nodePairs snapshot inner := by
          intro localMember
          apply outside
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨pair, List.mem_append_right _ localMember, rfl⟩)
        simp only [pairs_node, List.mem_append] at member ⊢
        change ((pair ∈ nodePairs snapshot outer ∨ pair ∈ pairs snapshot a ha) ∨
          ((pair ∈ nodePairs snapshot inner ∨ pair ∈ pairs snapshot b hb) ∨ pair ∈ pairs snapshot c hhi)) at member
        rcases member with (oldOuter | inA) | (oldInner | inB) | inC
        · exact False.elim (notOuter oldOuter)
        · exact Or.inl (Or.inr (Or.inl (Or.inr inA)))
        · exact False.elim (notInner oldInner)
        · exact Or.inl (Or.inr (Or.inr inB))
        · exact Or.inr inC

/-- The same four-record parent-pair support survives arbitrary enclosing
refinement contexts. Ancestor local pairs depend only on interval bounds. -/
theorem rotation_pair_support {n lo hi depth : ℕ} (snapshot : Snapshot n)
    {before after : BST lo hi} (rotation : RotationAt depth before after) (hhi : hi ≤ n) :
    ∃ selected : Finset (External n), selected.card ≤ 4 ∧
      ∀ pair ∈ pairs snapshot before hhi, pair.2 ∉ selected → pair ∈ pairs snapshot after hhi := by
  induction rotation with
  | root step => exact root_rotation_pair_support snapshot step hhi
  | leftContext step right ih =>
      have rootBound := right.lower_le_upper
      obtain ⟨selected, cardinal, preserved⟩ := ih (by omega)
      refine ⟨selected, cardinal, ?_⟩
      intro pair member outside
      simp only [pairs_node, List.mem_append] at member ⊢
      rcases member with (localMember | innerMember) | rightMember
      · exact Or.inl (Or.inl localMember)
      · exact Or.inl (Or.inr (preserved pair innerMember outside))
      · exact Or.inr rightMember
  | rightContext left step ih =>
      obtain ⟨selected, cardinal, preserved⟩ := ih hhi
      refine ⟨selected, cardinal, ?_⟩
      intro pair member outside
      simp only [pairs_node, List.mem_append] at member ⊢
      rcases member with (localMember | leftMember) | innerMember
      · exact Or.inl (Or.inl localMember)
      · exact Or.inl (Or.inr leftMember)
      · exact Or.inr (preserved pair innerMember outside)

/-- Actual heap-parent functions agree away from four selected records,
for a fixed snapshot and any contextual refinement rotation. -/
theorem rotation_parent_support {n depth : ℕ} (snapshot : Snapshot n)
    {before after : BST 0 n} (rotation : RotationAt depth before after) :
    ∃ selected : Finset (External n), selected.card ≤ 4 ∧
      ∀ child, child ∉ selected →
        canonicalParent snapshot after child = canonicalParent snapshot before child := by
  obtain ⟨selected, cardinal, preserved⟩ := rotation_pair_support snapshot rotation (Nat.le_refl n)
  refine ⟨selected, cardinal, ?_⟩
  intro child outside
  have sameRoot : canonicalRoot snapshot before = canonicalRoot snapshot after := rfl
  by_cases atRoot : child = canonicalRoot snapshot before
  · rw [atRoot, canonicalParent_canonicalRoot]
    rw [sameRoot, canonicalParent_canonicalRoot]
  · obtain ⟨edge, lookup, member, childEq⟩ :=
      exists_incomingEdge?_eq_some_of_ne_root snapshot before atRoot
    have oldPair : (edge.owner, child) ∈ pairs snapshot before (Nat.le_refl n) := by
      exact List.mem_map.mpr ⟨edge, member, by simp only [edgePair, childEq]⟩
    have newPair := preserved (edge.owner, child) oldPair outside
    obtain ⟨newEdge, newMember, pairEq⟩ := List.mem_map.mp newPair
    have ownerEq : newEdge.owner = edge.owner := congrArg Prod.fst pairEq
    have newChildEq : newEdge.child = child := congrArg Prod.snd pairEq
    have oldParent := parent_of_fullEdge snapshot before edge member
    have newParent := parent_of_fullEdge snapshot after newEdge newMember
    rw [childEq] at oldParent
    rw [newChildEq, ownerEq] at newParent
    exact newParent.trans oldParent.symm

noncomputable def changedParents {n : ℕ} (snapshot : Snapshot n)
    (before after : BST 0 n) : Finset (External n) := by
  classical
  exact Finset.univ.filter fun child =>
    canonicalParent snapshot after child ≠ canonicalParent snapshot before child

/-- A full concrete fixed-rank refinement rotation changes at most four
heap parents. No local-port abstraction or fringe-invariance premise is
assumed in this theorem. -/
theorem changed_parents_card_le_four {n depth : ℕ} (snapshot : Snapshot n)
    {before after : BST 0 n} (rotation : RotationAt depth before after) :
    (changedParents snapshot before after).card ≤ 4 := by
  classical
  obtain ⟨selected, cardinal, preserved⟩ := rotation_parent_support snapshot rotation
  apply le_trans (Finset.card_le_card ?_) cardinal
  intro child member
  have different := (Finset.mem_filter.mp member).2
  by_contra outside
  exact different (preserved child outside)

end GreedyMerge.RefinementRotation

#print axioms GreedyMerge.RefinementRotation.root_rotation_pair_support

#print axioms GreedyMerge.RefinementRotation.changed_parents_card_le_four
