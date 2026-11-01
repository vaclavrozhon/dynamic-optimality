import Splay.Lazy.CanonicalView
import Splay.Lazy.OrderedChildren

namespace Splay.Lazy.Canonical

open Splay.Rank

/--
The side of a canonical heap child is the side recorded by its incoming light
edge.  The canonical root has no incoming edge, so its side is immaterial; we
choose `left`.
-/
noncomputable def canonicalSide {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) (child : External n) : Side :=
  match incomingEdge? snapshot tree child with
  | some edge => edge.side
  | none => .left

/-- A canonical parent-child link respects symmetric external-node order. -/
theorem canonicalSide_order {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    {child owner : External n}
    (parent : canonicalParent snapshot tree child = some owner) :
    match canonicalSide snapshot tree child with
    | .left => child.val < owner.val
    | .right => owner.val < child.val := by
  simp only [canonicalParent, Option.map_eq_some_iff] at parent
  obtain ⟨edge, lookup, ownerEq⟩ := parent
  have edgeSpec := incomingEdge?_some_mem snapshot tree lookup
  have sideOrder :=
    mem_treeEdges_side_order snapshot tree (Nat.le_refl n)
      (show edge ∈ treeEdges snapshot tree (Nat.le_refl n) 0 by
        simpa only [fullEdges] using edgeSpec.1)
  have sideEq : canonicalSide snapshot tree child = edge.side := by
    simp [canonicalSide, lookup]
  rw [sideEq]
  cases edgeSide : edge.side with
  | left =>
      rw [edgeSide] at sideOrder
      simpa only [edgeSpec.2, ownerEq] using sideOrder
  | right =>
      rw [edgeSide] at sideOrder
      simpa only [edgeSpec.2, ownerEq] using sideOrder

/--
The canonical light-edge decomposition of a splay-tree shape under a supplied
comparison-rank snapshot, packaged as the complete transient heap view used
by the lazy interface.
-/
noncomputable def canonicalHeapView {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) : HeapView n where
  rank := snapshot.rank
  root := canonicalRoot snapshot tree
  parent := canonicalParent snapshot tree
  side := canonicalSide snapshot tree
  topDown :=
    orderedChildren (canonicalParent snapshot tree)
      (canonicalSide snapshot tree)
  level := snapshot.rank
  root_parent := canonicalParent_canonicalRoot snapshot tree
  parent_eq_none := fun element parentNone =>
    (canonicalParent_eq_none_iff snapshot tree element).1 parentNone
  parent_level_lt := fun {_ _} parent =>
    rank_canonicalParent_lt snapshot tree parent
  side_order := fun {_ _} parent =>
    canonicalSide_order snapshot tree parent
  topDown_nodup := fun owner childSide =>
    orderedChildren_nodup
      (canonicalParent snapshot tree) (canonicalSide snapshot tree)
      owner childSide
  topDown_ordered := fun owner =>
    orderedChildren_ordered
      (canonicalParent snapshot tree) (canonicalSide snapshot tree) owner
  mem_topDown_iff := by
    intro owner childSide element
    exact
      mem_orderedChildren_iff
        (canonicalParent snapshot tree) (canonicalSide snapshot tree)

/-- The canonical heap view is strictly ordered by the snapshot rank. -/
theorem canonicalHeapView_heapOrdered {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (canonicalHeapView snapshot tree).HeapOrdered := by
  intro child owner parent
  exact rank_canonicalParent_lt snapshot tree parent

/-- The canonical heap inherits the laminar symmetric-order geometry of the
underlying BST decomposition. -/
theorem canonicalHeapView_nestedChildOrder {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (canonicalHeapView snapshot tree).NestedChildOrder := by
  intro owner winner loser child winnerParent loserParent different
    childParent _childSide
  change canonicalParent snapshot tree winner = some owner at winnerParent
  change canonicalParent snapshot tree loser = some owner at loserParent
  change canonicalParent snapshot tree child = some winner at childParent
  simp only [canonicalParent, Option.map_eq_some_iff] at winnerParent loserParent childParent
  obtain ⟨winnerEdge, winnerLookup, winnerOwner⟩ := winnerParent
  obtain ⟨loserEdge, loserLookup, loserOwner⟩ := loserParent
  obtain ⟨childEdge, childLookup, childOwner⟩ := childParent
  have winnerSpec :=
    incomingEdge?_some_mem snapshot tree winnerLookup
  have loserSpec :=
    incomingEdge?_some_mem snapshot tree loserLookup
  have childSpec :=
    incomingEdge?_some_mem snapshot tree childLookup
  have winnerMember : winnerEdge ∈
      treeEdges snapshot tree (Nat.le_refl n) 0 := by
    simpa only [fullEdges] using winnerSpec.1
  have loserMember : loserEdge ∈
      treeEdges snapshot tree (Nat.le_refl n) 0 := by
    simpa only [fullEdges] using loserSpec.1
  have childMember : childEdge ∈
      treeEdges snapshot tree (Nat.le_refl n) 0 := by
    simpa only [fullEdges] using childSpec.1
  have sameOwner : winnerEdge.owner = loserEdge.owner :=
    winnerOwner.trans loserOwner.symm
  have childOwnerEq : childEdge.owner = winnerEdge.child :=
    childOwner.trans winnerSpec.2.symm
  have differentChildren : winnerEdge.child ≠ loserEdge.child := by
    intro equal
    apply different
    rw [← winnerSpec.2, ← loserSpec.2]
    exact equal
  have nested :=
    mem_treeEdges_nested_children snapshot tree (Nat.le_refl n)
      winnerMember loserMember childMember sameOwner childOwnerEq
      differentChildren
  by_cases left : loser.val < winner.val
  · simpa [winnerSpec.2, loserSpec.2, childSpec.2, left] using nested
  · simpa [winnerSpec.2, loserSpec.2, childSpec.2, left] using nested

/-- The root of the canonical heap view has rank zero. -/
@[simp]
theorem canonicalHeapView_root_rank {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (canonicalHeapView snapshot tree).rank
        (canonicalHeapView snapshot tree).root = 0 := by
  exact rank_canonicalRoot_eq_zero snapshot tree

/-- Every non-root canonical heap path has a positive signed raw gap. -/
theorem canonicalHeapView_rawGap_pos_of_ne_root {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    {child : Element n}
    (notRoot : child ≠ (canonicalHeapView snapshot tree).root) :
    0 < (canonicalHeapView snapshot tree).rawGap child := by
  let view := canonicalHeapView snapshot tree
  have parentNe : view.parent child ≠ none :=
    view.parent_ne_none_of_ne_root notRoot
  cases parentEq : view.parent child with
  | none =>
      exact False.elim (parentNe parentEq)
  | some owner =>
      exact
        view.rawGap_pos_of_heapOrdered
          (canonicalHeapView_heapOrdered snapshot tree) parentEq

end Splay.Lazy.Canonical
