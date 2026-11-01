import Splay.Accounting.PairingHeapChildEndpoints

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

/-- The heap-parent content of an edge, independent of its BST attachment
depth. Rotations may change that depth even in an untouched hanging subtree. -/
def heapLink {n : ℕ} (edge : Edge n) : External n × External n := (edge.owner, edge.child)

/-- Changing only the ambient depth of a subtree preserves every heap link. -/
theorem treeEdges_heapLink_depth_eq {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) (firstDepth secondDepth : ℕ) :
    (treeEdges snapshot tree upper_le_n firstDepth).map heapLink =
      (treeEdges snapshot tree upper_le_n secondDepth).map heapLink := by
  induction tree generalizing firstDepth secondDepth with
  | empty => rfl
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
      have localEq : (edgesAtNode snapshot node firstDepth).map heapLink =
          (edgesAtNode snapshot node secondDepth).map heapLink := by
        simp [edgesAtNode, List.map_map, Function.comp_def, heapLink, edgeFor]
      simp only [treeEdges, List.map_append]
      rw [localEq, ihLeft _ (firstDepth + 1) (secondDepth + 1), ihRight _ (firstDepth + 1) (secondDepth + 1)]

/-- All canonical heap links inside an interval-indexed subtree. -/
noncomputable def heapLinks {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) : Finset (External n × External n) :=
  ((treeEdges snapshot tree upper_le_n 0).map heapLink).toFinset

theorem heapLinks_eq_at_depth {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) (depth : ℕ) :
    heapLinks snapshot tree upper_le_n = ((treeEdges snapshot tree upper_le_n depth).map heapLink).toFinset := by
  unfold heapLinks
  rw [treeEdges_heapLink_depth_eq snapshot tree upper_le_n 0 depth]

@[simp]
theorem heapLinks_empty {n boundary : ℕ} (snapshot : Snapshot n) (bound : boundary ≤ n) :
    heapLinks snapshot (.empty boundary) bound = ∅ := rfl

/-- The two local light links and the two unchanged subtree link sets. -/
theorem heapLinks_node {n lower root upper : ℕ} (snapshot : Snapshot n)
    (left : BST lower root) (right : BST (root + 1) upper) (upper_le_n : upper ≤ n) :
    heapLinks snapshot (.node left right) upper_le_n =
      ((edgesAtNode snapshot ⟨lower, root, upper, left, right, upper_le_n⟩ 0).map heapLink).toFinset ∪
        heapLinks snapshot left (by have := right.lower_le_upper; omega) ∪ heapLinks snapshot right upper_le_n := by
  rw [heapLinks_eq_at_depth snapshot (.node left right) upper_le_n 0]
  simp only [treeEdges, List.map_append, List.toFinset_append]
  rw [← heapLinks_eq_at_depth snapshot left _ 1, ← heapLinks_eq_at_depth snapshot right _ 1]

/-- At a full-tree endpoint, link membership is exactly the canonical parent
relation; the attachment depth and enumeration order are irrelevant. -/
theorem mem_heapLinks_iff_parent {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (owner child : External n) :
    (owner, child) ∈ heapLinks snapshot tree (Nat.le_refl n) ↔
      canonicalParent snapshot tree child = some owner := by
  constructor
  · intro member
    obtain ⟨edge, edgeMember, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    have endpoints : edge.owner = owner ∧ edge.child = child := Prod.mk.inj equal
    have parent := canonicalParent_eq_some_of_mem_fullEdges snapshot tree edge edgeMember
    simpa [endpoints.1, endpoints.2] using parent
  · intro parent
    simp only [canonicalParent, Option.map_eq_some_iff] at parent
    obtain ⟨edge, found, ownerEq⟩ := parent
    have source := incomingEdge?_some_mem snapshot tree found
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨edge, source.1, Prod.ext ownerEq source.2⟩

/-- Each true phase pairing supplies a link of the concrete zig-zig endpoint,
inside arbitrary untouched search context. -/
theorem ZigZigPairingEndpointsAt.mem_after_heapLinks {n lower upper : ℕ} {snapshot : Snapshot n}
    {phase : PairingPhase} {depth key : ℕ} {before after : BST lower upper}
    {winner loser : External n}
    (endpoints : ZigZigPairingEndpointsAt snapshot phase (depth := depth) (key := key) before after winner loser)
    (upper_le_n : upper ≤ n) :
    (winner, loser) ∈ heapLinks snapshot after upper_le_n := by
  obtain ⟨edge, member, ownerEq, childEq⟩ := endpoints.exists_after_edge upper_le_n 0
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨edge, member, Prod.ext ownerEq childEq⟩)

end Splay.Accounting
