import Splay.Accounting.WholeSplayProtectedHeapLinks

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open WholeSplayTemporarySpineGeometry WholeSplayTemporaryFocusedSpines

/-- Both endpoints of a subtree heap link stay in its external interval. -/
theorem mem_heapLinks_bounds {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (bound : upper ≤ n) {link : External n × External n}
    (member : link ∈ heapLinks snapshot tree bound) :
    2 * lower ≤ link.1.val ∧ link.1.val ≤ 2 * upper ∧
      2 * lower ≤ link.2.val ∧ link.2.val ≤ 2 * upper := by
  obtain ⟨edge, edgeMember, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  have inside := mem_treeEdges_inside snapshot tree bound edgeMember
  have endpoints : edge.owner = link.1 ∧ edge.child = link.2 := Prod.mk.inj equal
  change 2 * lower ≤ edge.owner.val ∧ edge.owner.val ≤ 2 * upper ∧
    2 * lower ≤ edge.child.val ∧ edge.child.val ≤ 2 * upper at inside
  simpa only [endpoints.1, endpoints.2] using inside

/-- Removing an owner outside a subtree's interval removes no internal link. -/
theorem heapLinks_filter_owner_ne_of_outside {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (bound : upper ≤ n) (owner : External n)
    (outside : owner.val < 2 * lower ∨ 2 * upper < owner.val) :
    (heapLinks snapshot tree bound).filter (fun link => link.1 ≠ owner) = heapLinks snapshot tree bound := by
  apply Finset.filter_eq_self.mpr
  intro link member equal
  have bounds := mem_heapLinks_bounds snapshot tree bound member
  rw [equal] at bounds
  omega

/-- At an accessed-path node the local light links disappear when its owner
is removed; the same filter acts independently on the two hanging trees. -/
theorem heapLinks_filter_owner_node {n lower root upper : ℕ} (snapshot : Snapshot n)
    (left : BST lower root) (right : BST (root + 1) upper) (bound : upper ≤ n)
    (owner : External n)
    (ownerEq : AtNode.owner snapshot ⟨lower, root, upper, left, right, bound⟩ = owner) :
    (heapLinks snapshot (.node left right) bound).filter (fun link => link.1 ≠ owner) =
      (heapLinks snapshot left (by have := right.lower_le_upper; omega)).filter (fun link => link.1 ≠ owner) ∪
      (heapLinks snapshot right bound).filter (fun link => link.1 ≠ owner) := by
  rw [heapLinks_node, Finset.filter_union, Finset.filter_union]
  have localEmpty : (((edgesAtNode snapshot ⟨lower, root, upper, left, right, bound⟩ 0).map heapLink).toFinset.filter
      (fun link => link.1 ≠ owner)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro link member
    obtain ⟨edge, edgeMember, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_filter.mp member).1)
    have valid := mem_edgesAtNode_valid snapshot ⟨lower, root, upper, left, right, bound⟩ 0 edgeMember
    exact (Finset.mem_filter.mp member).2 ((congrArg Prod.fst equal).symm.trans (valid.2.1.trans ownerEq))
  rw [localEmpty, Finset.empty_union]

/-- The original zipper builds genuinely trivial base spines. This definition
makes their initialization independent of any subsequently chosen witness. -/
def WholeSplayTemporaryFocusedSpines.BaseFocus.initialFocused {n lower upper : ℕ}
    {key : Fin n} {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary} {tree : BST lower upper}
    (focus : BaseFocus key leftBoundary rightBoundary base tree)
    (snapshot : Snapshot n) (bound : upper ≤ n) :
    FocusedSpines snapshot key leftBoundary rightBoundary base tree :=
  match focus with
  | .root => .atKey (.base (Nat.le_of_lt key.isLt)) (.base bound)
  | .leftContext inner right => .leftContext (inner.initialFocused snapshot (by have := right.lower_le_upper; omega)) right
  | .rightContext left inner => .rightContext left (inner.initialFocused snapshot bound)

/-- Initially the protected links are exactly all heap links whose owner is
not the accessed root. In particular all original hanging subtrees are kept. -/
theorem WholeSplayTemporaryFocusedSpines.BaseFocus.initialFocused_protected_eq {n lower upper : ℕ}
    {key : Fin n} {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary} {tree : BST lower upper}
    (focus : BaseFocus key leftBoundary rightBoundary base tree)
    (snapshot : Snapshot n) (bound : upper ≤ n) (rankZero : snapshot.rank (valuePos key) = 0) :
    focusedProtectedLinks (focus.initialFocused snapshot bound) bound =
      (heapLinks snapshot tree bound).filter (fun link => link.1 ≠ valuePos key) := by
  induction focus with
  | root =>
      let node : AtNode n := ⟨base.leftLower, key.val, base.rightUpper, base.leftTree, base.rightTree, bound⟩
      have ownerEq := atNode_owner_eq_accessed snapshot node key.val base.leftTree.lower_le_upper
        (by change key.val < base.rightUpper; have := base.rightTree.lower_le_upper; omega) key.isLt rankZero
      rw [heapLinks_filter_owner_node _ _ _ _ _ ownerEq,
        heapLinks_filter_owner_ne_of_outside _ _ _ _ (Or.inr (by change 2 * key.val < 2 * key.val + 1; omega)),
        heapLinks_filter_owner_ne_of_outside _ _ _ _ (Or.inl (by change 2 * key.val + 1 < 2 * (key.val + 1); omega))]
      rfl
  | @leftContext lower root upper inner focus right ih =>
      let node : AtNode n := ⟨lower, root, upper, inner, right, bound⟩
      have keyBounds := (focus.initialFocused snapshot (by have := right.lower_le_upper; omega)).key_bounds
      have ownerEq := atNode_owner_eq_accessed snapshot node key.val keyBounds.1
        (by change key.val < upper; have := right.lower_le_upper; omega) key.isLt rankZero
      rw [heapLinks_filter_owner_node _ _ _ _ _ ownerEq,
        heapLinks_filter_owner_ne_of_outside snapshot right bound (valuePos key) (Or.inl (by change 2 * key.val + 1 < 2 * (root + 1); omega))]
      exact congrArg (fun links => links ∪ heapLinks snapshot right bound) (ih _)
  | @rightContext lower root upper left inner focus ih =>
      let node : AtNode n := ⟨lower, root, upper, left, inner, bound⟩
      have keyBounds := (focus.initialFocused snapshot bound).key_bounds
      have ownerEq := atNode_owner_eq_accessed snapshot node key.val
        (by change lower ≤ key.val; have := left.lower_le_upper; omega) keyBounds.2 key.isLt rankZero
      rw [heapLinks_filter_owner_node _ _ _ _ _ ownerEq,
        heapLinks_filter_owner_ne_of_outside snapshot left _ (valuePos key) (Or.inr (by change 2 * root < 2 * key.val + 1; omega))]
      exact congrArg (fun links => heapLinks snapshot left _ ∪ links) (ih _)

end Splay.Accounting
