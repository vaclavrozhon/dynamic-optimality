import Splay.Accounting.WholeSplayFinalHeapLinks

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

/-- At the promoted key the two local light links point exactly to the
canonical owners of its left and right BST subtrees. -/
theorem accessed_root_local_heapLinks {n lower upper : ℕ} (snapshot : Snapshot n) (key : Fin n)
    (left : BST lower key.val) (right : BST (key.val + 1) upper) (bound : upper ≤ n)
    (rankZero : snapshot.rank (valuePos key) = 0) :
    ((edgesAtNode snapshot ⟨lower, key.val, upper, left, right, bound⟩ 0).map heapLink).toFinset =
      {(valuePos key, subtreeOwner snapshot left (Nat.le_of_lt key.isLt)),
       (valuePos key, subtreeOwner snapshot right bound)} := by
  let node : AtNode n := ⟨lower, key.val, upper, left, right, bound⟩
  have ownerEq := atNode_owner_eq_accessed snapshot node key.val left.lower_le_upper
    (by change key.val < upper; have := right.lower_le_upper; omega) key.isLt rankZero
  have heavy : node.heavyBranch snapshot = .middle := by
    apply node.heavyBranch_eq_of_rank_eq_zero snapshot .middle (valuePos key) rankZero
    · change 2 * lower ≤ 2 * key.val + 1 ∧ 2 * key.val + 1 ≤ 2 * upper
      have := left.lower_le_upper
      have := right.lower_le_upper
      omega
    · simp only [TernaryBranch.middle_contains_iff, node, valuePos]
  change ((edgesAtNode snapshot node 0).map heapLink).toFinset = _
  rw [edgesAtNode_heapLinks_eq_pairings]
  simp only [HeapChildPairing.ofNode, heavy, HeapChildPairing.loserBranch, ownerEq]
  exact Finset.pair_comm _ _

/-- No internal link of either subtree can have the accessed key as owner. -/
theorem accessed_root_heapLink_iff {n lower upper : ℕ} (snapshot : Snapshot n) (key : Fin n)
    (left : BST lower key.val) (right : BST (key.val + 1) upper) (bound : upper ≤ n)
    (rankZero : snapshot.rank (valuePos key) = 0) (child : External n) :
    (valuePos key, child) ∈ heapLinks snapshot (.node left right) bound ↔
      child = subtreeOwner snapshot left (Nat.le_of_lt key.isLt) ∨ child = subtreeOwner snapshot right bound := by
  rw [heapLinks_node, accessed_root_local_heapLinks _ _ _ _ _ rankZero]
  constructor
  · intro member
    rcases Finset.mem_union.mp member with localOrLeft | rightMember
    · rcases Finset.mem_union.mp localOrLeft with localMember | leftMember
      · simpa using localMember
      · have bounds := mem_heapLinks_bounds snapshot left _ leftMember
        change 2 * lower ≤ 2 * key.val + 1 ∧ 2 * key.val + 1 ≤ 2 * key.val ∧ _ at bounds
        omega
    · have bounds := mem_heapLinks_bounds snapshot right bound rightMember
      change 2 * (key.val + 1) ≤ 2 * key.val + 1 ∧ _ at bounds
      omega
  · intro equal
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    simpa using equal

/-- Below an accessed root, every heap link not owned by that root stays
entirely on one side of the accessed key. This excludes transfer to the
opposite artificial boundary. -/
theorem heapLink_sameSide_of_accessed_root {n lower upper : ℕ} (snapshot : Snapshot n) (key : Fin n)
    (left : BST lower key.val) (right : BST (key.val + 1) upper) (bound : upper ≤ n)
    (rankZero : snapshot.rank (valuePos key) = 0) {link : External n × External n}
    (member : link ∈ heapLinks snapshot (.node left right) bound) (notRoot : link.1 ≠ valuePos key) :
    (link.1 < valuePos key ∧ link.2 < valuePos key) ∨
      (valuePos key < link.1 ∧ valuePos key < link.2) := by
  rw [heapLinks_node, accessed_root_local_heapLinks _ _ _ _ _ rankZero] at member
  rcases Finset.mem_union.mp member with localOrLeft | rightMember
  · rcases Finset.mem_union.mp localOrLeft with localMember | leftMember
    · simp only [Finset.mem_insert, Finset.mem_singleton] at localMember
      rcases localMember with equal | equal <;> exact (notRoot (congrArg Prod.fst equal)).elim
    · have bounds := mem_heapLinks_bounds snapshot left _ leftMember
      left
      change link.1.val < 2 * key.val + 1 ∧ link.2.val < 2 * key.val + 1
      omega
  · have bounds := mem_heapLinks_bounds snapshot right bound rightMember
    right
    change 2 * key.val + 1 < link.1.val ∧ 2 * key.val + 1 < link.2.val
    omega

end Splay.Accounting
