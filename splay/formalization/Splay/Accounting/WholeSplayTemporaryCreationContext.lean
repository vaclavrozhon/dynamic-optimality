import Splay.Accounting.ContextualBendGeometry

namespace Splay.Accounting.WholeSplayTemporaryCreationContext

open Splay.Rank
open Splay.Tree.BST
open Splay.Lazy.Canonical
open Splay.Accounting.LocalBendGeometry

/-!
Context lifting for locally created bend identities.

The surrounding node and sibling are unchanged by a contextual rotation.
An identity inside the rotated child therefore cannot be confused with the
context root or sibling, and a local set-difference witness lifts to the
whole enclosing subtree.
-/

/--
A creation in a node whose left child changed must already be a creation in
that child under the incoming edge selected by the unchanged context node.
-/
theorem created_leftContext_local
    {n lower root upper : ℕ}
    (snapshot : Snapshot n)
    (before after : BST lower root)
    (right : BST (root + 1) upper)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch)
    {created : Fin n}
    (globalCreated :
      created ∈
        (bendsFrom snapshot (.node after right) upper_le_n incoming) \
          (bendsFrom snapshot (.node before right) upper_le_n incoming)) :
    let node : AtNode n := {
      lower := lower
      root := root
      upper := upper
      left := before
      right := right
      upper_le_n := upper_le_n
    }
    let outgoing := node.heavyBranch snapshot
    created ∈
      (bendsFrom snapshot after (by
          have rightBounds := right.lower_le_upper
          omega) (childIncoming outgoing .left)) \
        (bendsFrom snapshot before (by
          have rightBounds := right.lower_le_upper
          omega) (childIncoming outgoing .left)) := by
  let beforeNode : AtNode n := {
    lower := lower
    root := root
    upper := upper
    left := before
    right := right
    upper_le_n := upper_le_n
  }
  let afterNode : AtNode n := {
    lower := lower
    root := root
    upper := upper
    left := after
    right := right
    upper_le_n := upper_le_n
  }
  have branchEq :
      afterNode.heavyBranch snapshot =
        beforeNode.heavyBranch snapshot := by
    simp [AtNode.heavyBranch, AtNode.wholeLower, AtNode.wholeUpper,
      beforeNode, afterNode]
  have beforeDecomposition :
      bendsFrom snapshot (.node before right) upper_le_n incoming =
        bendAt ⟨root, by
            have rightBounds := right.lower_le_upper
            omega⟩ incoming (beforeNode.heavyBranch snapshot) ∪
          (bendsFrom snapshot before (by
              have rightBounds := right.lower_le_upper
              omega)
            (childIncoming (beforeNode.heavyBranch snapshot) .left) ∪
           bendsFrom snapshot right upper_le_n
            (childIncoming (beforeNode.heavyBranch snapshot) .right)) := by
    simp only [bendsFrom]
    simp [beforeNode]
  have afterDecomposition :
      bendsFrom snapshot (.node after right) upper_le_n incoming =
        bendAt ⟨root, by
            have rightBounds := right.lower_le_upper
            omega⟩ incoming (beforeNode.heavyBranch snapshot) ∪
          (bendsFrom snapshot after (by
              have rightBounds := right.lower_le_upper
              omega)
            (childIncoming (beforeNode.heavyBranch snapshot) .left) ∪
           bendsFrom snapshot right upper_le_n
            (childIncoming (beforeNode.heavyBranch snapshot) .right)) := by
    simp only [bendsFrom]
    rw [branchEq]
  rw [afterDecomposition, beforeDecomposition] at globalCreated
  simp only [Finset.mem_sdiff, Finset.mem_union] at globalCreated ⊢
  tauto

/--
A creation in a node whose right child changed must already be a creation in
that child under the incoming edge selected by the unchanged context node.
-/
theorem created_rightContext_local
    {n lower root upper : ℕ}
    (snapshot : Snapshot n)
    (left : BST lower root)
    (before after : BST (root + 1) upper)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch)
    {created : Fin n}
    (globalCreated :
      created ∈
        (bendsFrom snapshot (.node left after) upper_le_n incoming) \
          (bendsFrom snapshot (.node left before) upper_le_n incoming)) :
    let node : AtNode n := {
      lower := lower
      root := root
      upper := upper
      left := left
      right := before
      upper_le_n := upper_le_n
    }
    let outgoing := node.heavyBranch snapshot
    created ∈
      (bendsFrom snapshot after upper_le_n
          (childIncoming outgoing .right)) \
        (bendsFrom snapshot before upper_le_n
          (childIncoming outgoing .right)) := by
  let beforeNode : AtNode n := {
    lower := lower
    root := root
    upper := upper
    left := left
    right := before
    upper_le_n := upper_le_n
  }
  let afterNode : AtNode n := {
    lower := lower
    root := root
    upper := upper
    left := left
    right := after
    upper_le_n := upper_le_n
  }
  have branchEq :
      afterNode.heavyBranch snapshot =
        beforeNode.heavyBranch snapshot := by
    simp [AtNode.heavyBranch, AtNode.wholeLower, AtNode.wholeUpper,
      beforeNode, afterNode]
  have beforeDecomposition :
      bendsFrom snapshot (.node left before) upper_le_n incoming =
        bendAt ⟨root, by
            have beforeBounds := before.lower_le_upper
            omega⟩ incoming (beforeNode.heavyBranch snapshot) ∪
          (bendsFrom snapshot left (by
              have beforeBounds := before.lower_le_upper
              omega)
            (childIncoming (beforeNode.heavyBranch snapshot) .left) ∪
           bendsFrom snapshot before upper_le_n
            (childIncoming (beforeNode.heavyBranch snapshot) .right)) := by
    simp only [bendsFrom]
    simp [beforeNode]
  have afterDecomposition :
      bendsFrom snapshot (.node left after) upper_le_n incoming =
        bendAt ⟨root, by
            have afterBounds := after.lower_le_upper
            omega⟩ incoming (beforeNode.heavyBranch snapshot) ∪
          (bendsFrom snapshot left (by
              have afterBounds := after.lower_le_upper
              omega)
            (childIncoming (beforeNode.heavyBranch snapshot) .left) ∪
           bendsFrom snapshot after upper_le_n
            (childIncoming (beforeNode.heavyBranch snapshot) .right)) := by
    simp only [bendsFrom]
    rw [branchEq]
  rw [afterDecomposition, beforeDecomposition] at globalCreated
  simp only [Finset.mem_sdiff, Finset.mem_union] at globalCreated ⊢
  tauto

/-- Lift a created identity through an unchanged right sibling. -/
theorem lift_created_leftContext
    {n lower root upper : ℕ}
    (snapshot : Snapshot n)
    (before after : BST lower root)
    (right : BST (root + 1) upper)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch)
    {created : Fin n}
    (localCreated :
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := before
        right := right
        upper_le_n := upper_le_n
      }
      let outgoing := node.heavyBranch snapshot
      created ∈
        (bendsFrom snapshot after (by
            have rightBounds := right.lower_le_upper
            omega) (childIncoming outgoing .left)) \
          (bendsFrom snapshot before (by
            have rightBounds := right.lower_le_upper
            omega) (childIncoming outgoing .left))) :
    created ∈
      (bendsFrom snapshot (.node after right) upper_le_n incoming) \
        (bendsFrom snapshot (.node before right) upper_le_n incoming) := by
  let node : AtNode n := {
    lower := lower
    root := root
    upper := upper
    left := before
    right := right
    upper_le_n := upper_le_n
  }
  let outgoing := node.heavyBranch snapshot
  have inner_le_n : root ≤ n := by
    have rightBounds := right.lower_le_upper
    omega
  have localCreated' :
      created ∈
        (bendsFrom snapshot after inner_le_n
            (childIncoming outgoing .left)) \
          (bendsFrom snapshot before inner_le_n
            (childIncoming outgoing .left)) := by
    simpa [node, outgoing] using localCreated
  have localAfter := (Finset.mem_sdiff.mp localCreated').1
  have localBefore := (Finset.mem_sdiff.mp localCreated').2
  have createdBounds :=
    mem_bendsFrom_bounds snapshot after inner_le_n
      (childIncoming outgoing .left) localAfter
  have afterMember :
      created ∈
        bendsFrom snapshot (.node after right) upper_le_n incoming := by
    simp only [bendsFrom, Finset.mem_union]
    exact Or.inr (Or.inl localAfter)
  have beforeNotMember :
      created ∉
        bendsFrom snapshot (.node before right) upper_le_n incoming := by
    intro member
    simp only [bendsFrom, Finset.mem_union] at member
    rcases member with atRoot | inInner | inRight
    · unfold bendAt at atRoot
      split at atRoot
      · have created_eq :
            created.val = root := by
          simpa using congrArg Fin.val (Finset.mem_singleton.mp atRoot)
        omega
      · simp at atRoot
    · exact localBefore inInner
    · have siblingBounds :=
        mem_bendsFrom_bounds snapshot right upper_le_n _ inRight
      omega
  exact Finset.mem_sdiff.mpr ⟨afterMember, beforeNotMember⟩

/-- Lift a created identity through an unchanged left sibling. -/
theorem lift_created_rightContext
    {n lower root upper : ℕ}
    (snapshot : Snapshot n)
    (left : BST lower root)
    (before after : BST (root + 1) upper)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch)
    {created : Fin n}
    (localCreated :
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := before
        upper_le_n := upper_le_n
      }
      let outgoing := node.heavyBranch snapshot
      created ∈
        (bendsFrom snapshot after upper_le_n
            (childIncoming outgoing .right)) \
          (bendsFrom snapshot before upper_le_n
            (childIncoming outgoing .right))) :
    created ∈
      (bendsFrom snapshot (.node left after) upper_le_n incoming) \
        (bendsFrom snapshot (.node left before) upper_le_n incoming) := by
  let node : AtNode n := {
    lower := lower
    root := root
    upper := upper
    left := left
    right := before
    upper_le_n := upper_le_n
  }
  let outgoing := node.heavyBranch snapshot
  have localCreated' :
      created ∈
        (bendsFrom snapshot after upper_le_n
            (childIncoming outgoing .right)) \
          (bendsFrom snapshot before upper_le_n
            (childIncoming outgoing .right)) := by
    simpa [node, outgoing] using localCreated
  have localAfter := (Finset.mem_sdiff.mp localCreated').1
  have localBefore := (Finset.mem_sdiff.mp localCreated').2
  have createdBounds :=
    mem_bendsFrom_bounds snapshot after upper_le_n
      (childIncoming outgoing .right) localAfter
  have left_le_n : root ≤ n := by
    have beforeBounds := before.lower_le_upper
    omega
  have afterMember :
      created ∈
        bendsFrom snapshot (.node left after) upper_le_n incoming := by
    simp only [bendsFrom, Finset.mem_union]
    exact Or.inr (Or.inr localAfter)
  have beforeNotMember :
      created ∉
        bendsFrom snapshot (.node left before) upper_le_n incoming := by
    intro member
    simp only [bendsFrom, Finset.mem_union] at member
    rcases member with atRoot | inLeft | inInner
    · unfold bendAt at atRoot
      split at atRoot
      · have created_eq :
            created.val = root := by
          simpa using congrArg Fin.val (Finset.mem_singleton.mp atRoot)
        omega
      · simp at atRoot
    · have siblingBounds :=
        mem_bendsFrom_bounds snapshot left left_le_n _ inLeft
      omega
    · exact localBefore inInner
  exact Finset.mem_sdiff.mpr ⟨afterMember, beforeNotMember⟩

end Splay.Accounting.WholeSplayTemporaryCreationContext
