import Splay.Accounting.WholeSplayPersistentHeapLinks
import Splay.Accounting.RootHeavyPathBoundaryDecomposition

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open WholeSplayTemporarySpineGeometry WholeSplayTemporaryFocusedSpines

/-- Heap links in the fixed base, accumulated hanging subtrees, and the
unprocessed search context's hanging subtrees. Newly formed spine links are
excluded; their owners are the two fixed boundary minima. -/
noncomputable def focusedProtectedLinks {n lower upper : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n} {base : SpineBase key leftBoundary rightBoundary}
    {tree : BST lower upper} (focused : FocusedSpines snapshot key leftBoundary rightBoundary base tree)
    (upper_le_n : upper ≤ n) : Finset (External n × External n) :=
  match focused with
  | .atKey leftSpine rightSpine => leftPersistentLinks leftSpine ∪ rightPersistentLinks rightSpine
  | .leftContext inner rightTree =>
      focusedProtectedLinks inner (by have := rightTree.lower_le_upper; omega) ∪ heapLinks snapshot rightTree upper_le_n
  | .rightContext leftTree inner =>
      heapLinks snapshot leftTree (by have := FocusedSpines.key_bounds inner; omega) ∪ focusedProtectedLinks inner upper_le_n

theorem focusedProtectedLinks_subset {n lower upper : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n} {base : SpineBase key leftBoundary rightBoundary}
    {tree : BST lower upper} (focused : FocusedSpines snapshot key leftBoundary rightBoundary base tree)
    (upper_le_n : upper ≤ n) :
    focusedProtectedLinks focused upper_le_n ⊆ heapLinks snapshot tree upper_le_n := by
  induction focused with
  | atKey leftSpine rightSpine => exact focusedPersistentLinks_subset (.atKey leftSpine rightSpine) upper_le_n
  | leftContext focused rightTree ih =>
      intro link member
      rw [heapLinks_node]
      rcases Finset.mem_union.mp member with inner | hanging
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (ih _ inner))))
      · exact Finset.mem_union.mpr (Or.inr hanging)
  | rightContext leftTree focused ih =>
      intro link member
      rw [heapLinks_node]
      rcases Finset.mem_union.mp member with hanging | inner
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hanging)))
      · exact Finset.mem_union.mpr (Or.inr (ih _ inner))

/-- Outside the accessed owner and the two fixed base owners, every actual
heap link belongs to a protected subtree. This accounts for arbitrary
unprocessed search context as well as both accumulated spines. -/
theorem heapLink_protected_of_owner_ne {n lower upper : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n} {base : SpineBase key leftBoundary rightBoundary}
    {tree : BST lower upper} (focused : FocusedSpines snapshot key leftBoundary rightBoundary base tree)
    (upper_le_n : upper ≤ n) (rankZero : snapshot.rank (valuePos key) = 0)
    {link : External n × External n} (member : link ∈ heapLinks snapshot tree upper_le_n)
    (notAccessed : link.1 ≠ valuePos key)
    (notLeft : link.1 ≠ subtreeOwner snapshot base.leftTree (Nat.le_of_lt key.isLt))
    (notRight : link.1 ≠ subtreeOwner snapshot base.rightTree focused.spinePair.rightSpine.base_le_n) :
    link ∈ focusedProtectedLinks focused upper_le_n := by
  induction focused with
  | @atKey lower upper leftTree rightTree leftSpine rightSpine =>
      rw [heapLinks_node] at member
      rcases Finset.mem_union.mp member with localOrLeft | rightMember
      · rcases Finset.mem_union.mp localOrLeft with localMember | leftMember
        · obtain ⟨edge, edgeMember, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp localMember)
          let node : AtNode n := ⟨lower, key.val, upper, leftTree, rightTree, upper_le_n⟩
          have edgeValid := mem_edgesAtNode_valid snapshot node 0 edgeMember
          have owner := atNode_owner_eq_accessed snapshot node key.val leftTree.lower_le_upper
            (by change key.val < upper; have := rightTree.lower_le_upper; omega) key.isLt rankZero
          exact (notAccessed ((congrArg Prod.fst equal).symm.trans (edgeValid.2.1.trans owner))).elim
        · exact Finset.mem_union.mpr (Or.inl (leftSpine_link_persistent_of_owner_ne leftSpine leftMember notLeft))
      · exact Finset.mem_union.mpr (Or.inr (rightSpine_link_persistent_of_owner_ne rightSpine rightMember notRight))
  | @leftContext lower root upper inner focused rightTree ih =>
      rw [heapLinks_node] at member
      rcases Finset.mem_union.mp member with localOrInner | hangingMember
      · rcases Finset.mem_union.mp localOrInner with localMember | innerMember
        · obtain ⟨edge, edgeMember, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp localMember)
          let node : AtNode n := ⟨lower, root, upper, inner, rightTree, upper_le_n⟩
          have edgeValid := mem_edgesAtNode_valid snapshot node 0 edgeMember
          have bounds := focused.key_bounds
          have owner := atNode_owner_eq_accessed snapshot node key.val bounds.1
            (by change key.val < upper; have := rightTree.lower_le_upper; omega) key.isLt rankZero
          exact (notAccessed ((congrArg Prod.fst equal).symm.trans (edgeValid.2.1.trans owner))).elim
        · exact Finset.mem_union.mpr (Or.inl (ih _ innerMember notRight))
      · exact Finset.mem_union.mpr (Or.inr hangingMember)
  | @rightContext lower root upper leftTree inner focused ih =>
      rw [heapLinks_node] at member
      rcases Finset.mem_union.mp member with localOrHanging | innerMember
      · rcases Finset.mem_union.mp localOrHanging with localMember | hangingMember
        · obtain ⟨edge, edgeMember, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp localMember)
          let node : AtNode n := ⟨lower, root, upper, leftTree, inner, upper_le_n⟩
          have edgeValid := mem_edgesAtNode_valid snapshot node 0 edgeMember
          have bounds := focused.key_bounds
          have owner := atNode_owner_eq_accessed snapshot node key.val
            (by change lower ≤ key.val; have := leftTree.lower_le_upper; omega) bounds.2 key.isLt rankZero
          exact (notAccessed ((congrArg Prod.fst equal).symm.trans (edgeValid.2.1.trans owner))).elim
        · exact Finset.mem_union.mpr (Or.inl hangingMember)
      · exact Finset.mem_union.mpr (Or.inr (ih _ innerMember notRight))

end Splay.Accounting
