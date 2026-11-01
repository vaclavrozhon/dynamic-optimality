import Splay.Accounting.WholeSplayBaseRootChildren
import Splay.Accounting.CanonicalEdgeUnbroken
import Splay.Accounting.CanonicalJunctionParentCells

namespace Splay.Accounting

open Splay.Rank Splay.Tree Splay.Tree.BST Splay.Lazy Splay.Lazy.Canonical
open WholeSplayTemporarySpineGeometry WholeSplayTemporaryFocusedSpines

private theorem edge_below_accessed_root {n : ℕ} (snapshot : Snapshot n) (key : Fin n)
    (left : BST 0 key.val) (right : BST (key.val + 1) n)
    (rankZero : snapshot.rank (valuePos key) = 0) {edge : Edge n}
    (member : edge ∈ fullEdges snapshot (.node left right))
    (notRoot : edge.owner ≠ valuePos key) :
    edge ∈ treeEdges snapshot left (Nat.le_of_lt key.isLt) 1 ∨
      edge ∈ treeEdges snapshot right (Nat.le_refl n) 1 := by
  let node : AtNode n := ⟨0, key.val, n, left, right, Nat.le_refl n⟩
  have ownerEq : node.owner snapshot = valuePos key :=
    atNode_owner_eq_accessed snapshot node key.val (Nat.zero_le _) key.isLt key.isLt rankZero
  rcases List.mem_append.mp member with localOrLeft | inRight
  · rcases List.mem_append.mp localOrLeft with localEdge | inLeft
    · exact (notRoot ((mem_edgesAtNode_valid snapshot node 0 localEdge).2.1.trans ownerEq)).elim
    · exact Or.inl inLeft
  · exact Or.inr inRight

/-- A block of newly attached right-spine children is unbroken, independently
of how its payload was interleaved before the splay. -/
theorem FinalTwoSpines.right_prefix_unbroken {n : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n} {base : SpineBase key leftBoundary rightBoundary}
    {tree : BST 0 n} (spines : FinalTwoSpines snapshot key leftBoundary rightBoundary base tree)
    (rankZero : snapshot.rank (valuePos key) = 0) (block : Block n)
    (owner : block.owner = subtreeOwner snapshot base.rightTree (by cases spines with | atRoot l r => exact r.base_le_n))
    (side : block.side = .right)
    (parents : ∀ element ∈ block.elements, canonicalParent snapshot tree element = some block.owner)
    (outside : ∀ element ∈ block.elements, 2 * base.rightUpper < element.val) :
    canonicalBlockCrossSideUnbroken snapshot tree block := by
  cases spines with
  | @atRoot left right leftSpine rightSpine =>
    have ownerLow : 2 * (key.val + 1) ≤ block.owner.val := by
      rw [owner]
      exact (subtreeOwner_isMin snapshot base.rightTree rightSpine.base_le_n).1
    have notRoot : block.owner ≠ valuePos key := by
      intro eq
      rw [eq] at ownerLow
      change 2 * (key.val + 1) ≤ 2 * key.val + 1 at ownerLow
      omega
    have location : ∀ edge ∈ fullEdges snapshot (.node left right), edge.owner = block.owner →
        edge ∈ treeEdges snapshot right rightSpine.upper_le_n 1 := by
      intro edge member edgeOwner
      rcases edge_below_accessed_root snapshot key left right rankZero member
        (by rw [edgeOwner]; exact notRoot) with inLeft | inRight
      · have high : edge.owner.val ≤ 2 * key.val :=
          (mem_treeEdges_inside snapshot left (Nat.le_of_lt key.isLt) inLeft).2.1
        rw [edgeOwner] at high
        omega
      · exact inRight
    apply (edgeBlockUnbroken_iff_canonical snapshot (.node left right) block).mp
    intro first firstMember firstIn last lastMember lastIn middle middleMember middleOwner opposite between
    have payloadOwner : ∀ edge ∈ fullEdges snapshot (.node left right), edge.child ∈ block.elements → edge.owner = block.owner := by
      intro edge member inBlock
      exact Option.some.inj ((canonicalParent_eq_some_of_mem_fullEdges snapshot (.node left right) edge member).symm.trans (parents edge.child inBlock))
    have middleSide : middle.side = .left := by cases h : middle.side <;> simp_all
    have firstAbove := Splay.Accounting.RightSpine.prefix_above_opposite rightSpine 1 (location first firstMember (payloadOwner first firstMember firstIn))
      (location middle middleMember middleOwner) ((payloadOwner first firstMember firstIn).trans owner)
      (middleOwner.trans owner) (outside first.child firstIn) middleSide
    have lastAbove := Splay.Accounting.RightSpine.prefix_above_opposite rightSpine 1 (location last lastMember (payloadOwner last lastMember lastIn))
      (location middle middleMember middleOwner) ((payloadOwner last lastMember lastIn).trans owner)
      (middleOwner.trans owner) (outside last.child lastIn) middleSide
    unfold edgeBetween edgeStrictlyAbove at between
    omega

/-- Symmetric statement for the new left-spine children. -/
theorem FinalTwoSpines.left_prefix_unbroken {n : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n} {base : SpineBase key leftBoundary rightBoundary}
    {tree : BST 0 n} (spines : FinalTwoSpines snapshot key leftBoundary rightBoundary base tree)
    (rankZero : snapshot.rank (valuePos key) = 0) (block : Block n)
    (owner : block.owner = subtreeOwner snapshot base.leftTree (Nat.le_of_lt key.isLt))
    (side : block.side = .left)
    (parents : ∀ element ∈ block.elements, canonicalParent snapshot tree element = some block.owner)
    (outside : ∀ element ∈ block.elements, element.val < 2 * base.leftLower) :
    canonicalBlockCrossSideUnbroken snapshot tree block := by
  cases spines with
  | @atRoot left right leftSpine rightSpine =>
    have ownerHigh : block.owner.val ≤ 2 * key.val := by
      rw [owner]
      exact (subtreeOwner_isMin snapshot base.leftTree leftSpine.base_le_n).2.1
    have notRoot : block.owner ≠ valuePos key := by
      intro eq
      rw [eq] at ownerHigh
      change 2 * key.val + 1 ≤ 2 * key.val at ownerHigh
      omega
    have location : ∀ edge ∈ fullEdges snapshot (.node left right), edge.owner = block.owner →
        edge ∈ treeEdges snapshot left leftSpine.upper_le_n 1 := by
      intro edge member edgeOwner
      rcases edge_below_accessed_root snapshot key left right rankZero member
        (by rw [edgeOwner]; exact notRoot) with inLeft | inRight
      · exact inLeft
      · have low : 2 * (key.val + 1) ≤ edge.owner.val :=
          (mem_treeEdges_inside snapshot right (Nat.le_refl n) inRight).1
        rw [edgeOwner] at low
        omega
    apply (edgeBlockUnbroken_iff_canonical snapshot (.node left right) block).mp
    intro first firstMember firstIn last lastMember lastIn middle middleMember middleOwner opposite between
    have payloadOwner : ∀ edge ∈ fullEdges snapshot (.node left right), edge.child ∈ block.elements → edge.owner = block.owner := by
      intro edge member inBlock
      exact Option.some.inj ((canonicalParent_eq_some_of_mem_fullEdges snapshot (.node left right) edge member).symm.trans (parents edge.child inBlock))
    have middleSide : middle.side = .right := by cases h : middle.side <;> simp_all
    have firstAbove := Splay.Accounting.LeftSpine.prefix_above_opposite leftSpine 1 (location first firstMember (payloadOwner first firstMember firstIn))
      (location middle middleMember middleOwner) ((payloadOwner first firstMember firstIn).trans owner)
      (middleOwner.trans owner) (outside first.child firstIn) middleSide
    have lastAbove := Splay.Accounting.LeftSpine.prefix_above_opposite leftSpine 1 (location last lastMember (payloadOwner last lastMember lastIn))
      (location middle middleMember middleOwner) ((payloadOwner last lastMember lastIn).trans owner)
      (middleOwner.trans owner) (outside last.child lastIn) middleSide
    unfold edgeBetween edgeStrictlyAbove at between
    omega

/-- Every surviving old root-child interval transferred to the right base
owner is unbroken after the complete splay. No old unbroken hypothesis or
positive pass count is needed, so this also covers its first splay. -/
theorem ExecutionTwoSpines.right_transferred_unbroken {n : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n} {before after : BST 0 n}
    (spines : ExecutionTwoSpines snapshot key leftBoundary rightBoundary before after)
    (rankZero : snapshot.rank (valuePos key) = 0) (block : Block n)
    (owner : block.owner = subtreeOwner snapshot spines.base.rightTree spines.baseFocus.rightUpper_le_upper)
    (side : block.side = .right)
    (oldParents : ∀ element ∈ block.elements, canonicalParent snapshot before element = some (valuePos key))
    (parents : ∀ element ∈ block.elements, canonicalParent snapshot after element = some block.owner)
    (sides : ∀ element ∈ block.elements, canonicalSide snapshot after element = block.side) :
    canonicalBlockCrossSideUnbroken snapshot after block := by
  apply Splay.Accounting.FinalTwoSpines.right_prefix_unbroken spines.finalSpines rankZero block owner side parents
  intro element member
  have elementHigh := canonicalSide_order snapshot after (parents element member)
  rw [sides element member, side] at elementHigh
  have rightLow : 2 * (key.val + 1) ≤ block.owner.val := by
    rw [owner]
    exact (subtreeOwner_isMin snapshot spines.base.rightTree spines.baseFocus.rightUpper_le_upper).1
  have leftHigh : (subtreeOwner snapshot spines.base.leftTree (Nat.le_of_lt key.isLt)).val ≤ 2 * key.val :=
    (subtreeOwner_isMin snapshot spines.base.leftTree (Nat.le_of_lt key.isLt)).2.1
  obtain ⟨edge, edgeMember, edgeOwner, child⟩ := JunctionBendReduction.exists_edge_of_canonicalParent snapshot before (oldParents element member)
  have outside := spines.baseFocus.root_child_outside_base snapshot (Nat.le_refl n) 0 rankZero edgeMember edgeOwner
    (by intro eq; have h := congrArg Fin.val (child.symm.trans eq); omega)
    (by intro eq; have h := congrArg Fin.val (child.symm.trans (eq.trans owner.symm)); omega)
  rw [child] at outside
  have leftBound := spines.base.leftTree.lower_le_upper
  omega

/-- The corresponding first-splay result for a surviving left source. -/
theorem ExecutionTwoSpines.left_transferred_unbroken {n : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n} {before after : BST 0 n}
    (spines : ExecutionTwoSpines snapshot key leftBoundary rightBoundary before after)
    (rankZero : snapshot.rank (valuePos key) = 0) (block : Block n)
    (owner : block.owner = subtreeOwner snapshot spines.base.leftTree (Nat.le_of_lt key.isLt))
    (side : block.side = .left)
    (oldParents : ∀ element ∈ block.elements, canonicalParent snapshot before element = some (valuePos key))
    (parents : ∀ element ∈ block.elements, canonicalParent snapshot after element = some block.owner)
    (sides : ∀ element ∈ block.elements, canonicalSide snapshot after element = block.side) :
    canonicalBlockCrossSideUnbroken snapshot after block := by
  apply Splay.Accounting.FinalTwoSpines.left_prefix_unbroken spines.finalSpines rankZero block owner side parents
  intro element member
  have elementLow := canonicalSide_order snapshot after (parents element member)
  rw [sides element member, side] at elementLow
  have leftHigh : block.owner.val ≤ 2 * key.val := by
    rw [owner]
    exact (subtreeOwner_isMin snapshot spines.base.leftTree (Nat.le_of_lt key.isLt)).2.1
  have rightLow : 2 * (key.val + 1) ≤ (subtreeOwner snapshot spines.base.rightTree spines.baseFocus.rightUpper_le_upper).val :=
    (subtreeOwner_isMin snapshot spines.base.rightTree spines.baseFocus.rightUpper_le_upper).1
  obtain ⟨edge, edgeMember, edgeOwner, child⟩ := JunctionBendReduction.exists_edge_of_canonicalParent snapshot before (oldParents element member)
  have outside := spines.baseFocus.root_child_outside_base snapshot (Nat.le_refl n) 0 rankZero edgeMember edgeOwner
    (by intro eq; have h := congrArg Fin.val (child.symm.trans (eq.trans owner.symm)); omega)
    (by intro eq; have h := congrArg Fin.val (child.symm.trans eq); omega)
  rw [child] at outside
  have rightBound := spines.base.rightTree.lower_le_upper
  omega

end Splay.Accounting
