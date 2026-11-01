import Splay.Accounting.JunctionBendReduction
import Splay.Lazy.RankRaiseGeometry

namespace Splay.Accounting.JunctionBendReduction

open Splay.Rank Splay.Tree Splay.Lazy.Canonical

/-- A direct heavy-branch change is charged to one of the two successive
changes through any intermediate snapshot. -/
theorem junctionCountFrom_triangle {n lower upper : ℕ} (first middle last : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) :
    junctionCountFrom first last tree upper_le_n ≤
      junctionCountFrom first middle tree upper_le_n + junctionCountFrom middle last tree upper_le_n := by
  classical
  induction tree with
  | empty => simp [junctionCountFrom]
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
      have leftBound : root ≤ n := by have := right.lower_le_upper; omega
      have localBound : (if node.heavyBranch first = node.heavyBranch last then 0 else 1) ≤
          (if node.heavyBranch first = node.heavyBranch middle then 0 else 1) +
            (if node.heavyBranch middle = node.heavyBranch last then 0 else 1) := by
        split_ifs <;> grind
      have l := ihLeft leftBound
      have r := ihRight upper_le_n
      simp only [junctionCountFrom]
      change (if node.heavyBranch first = node.heavyBranch last then 0 else 1) + _ + _ ≤
        ((if node.heavyBranch first = node.heavyBranch middle then 0 else 1) + _ + _) +
          ((if node.heavyBranch middle = node.heavyBranch last then 0 else 1) + _ + _)
      omega

/-- Only heavy-branch choices enter junction counts. -/
theorem junctionCountFrom_eq_of_heavyBranch_eq {n lower upper : ℕ} (before first second : Snapshot n)
    (same : ∀ node : AtNode n, node.heavyBranch first = node.heavyBranch second)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) :
    junctionCountFrom before first tree upper_le_n = junctionCountFrom before second tree upper_le_n := by
  induction tree with
  | empty => simp [junctionCountFrom]
  | @node lower root upper left right ihLeft ihRight =>
      simp only [junctionCountFrom]
      rw [same, ihLeft, ihRight]

/-- New heavy-path owners at the actual nodes whose outgoing heavy branch
changes. Repetitions are removed; long common path pieces add no entries. -/
noncomputable def junctionOwnersFrom {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) : Finset (External n) := by
  classical
  exact match tree with
  | .empty _ => ∅
  | .node (root := root) left right =>
      let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
      (if node.heavyBranch before = node.heavyBranch after then ∅ else {node.owner after}) ∪
        junctionOwnersFrom before after left (by have := right.lower_le_upper; omega) ∪
        junctionOwnersFrom before after right upper_le_n

/-- The support size is bounded by the original junction count, with no
extra charge for the lengths of the paths between junctions. -/
theorem junctionOwnersFrom_card_le {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) :
    (junctionOwnersFrom before after tree upper_le_n).card ≤ junctionCountFrom before after tree upper_le_n := by
  classical
  induction tree with
  | empty => simp [junctionOwnersFrom, junctionCountFrom]
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
      have leftBound : root ≤ n := by have := right.lower_le_upper; omega
      have localBound :
          (if node.heavyBranch before = node.heavyBranch after then (∅ : Finset (External n)) else {node.owner after}).card ≤
            if node.heavyBranch before = node.heavyBranch after then 0 else 1 := by
        split <;> simp
      rw [junctionCountFrom]
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add ((Finset.card_union_le _ _).trans
          (Nat.add_le_add localBound (ihLeft leftBound))) (ihRight upper_le_n))

/-- A changed minimum propagates along unchanged heavy edges until a real
junction is reached. Consequently its new identity is in the junction
support even when the root of this subtree is not itself a junction. -/
theorem subtreeOwner_mem_junctionOwnersFrom_of_ne {n lower upper : ℕ}
    (before after : Snapshot n) (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (changed : subtreeOwner before tree upper_le_n ≠ subtreeOwner after tree upper_le_n) :
    subtreeOwner after tree upper_le_n ∈ junctionOwnersFrom before after tree upper_le_n := by
  classical
  induction tree with
  | empty boundary =>
      have old := subtreeOwner_isMin before (.empty boundary) upper_le_n
      have new := subtreeOwner_isMin after (.empty boundary) upper_le_n
      apply False.elim (changed ?_)
      apply Fin.ext
      have oldLower := old.1
      have oldUpper := old.2.1
      have newLower := new.1
      have newUpper := new.2.1
      change 2 * boundary ≤ _ at oldLower newLower
      change _ ≤ 2 * boundary at oldUpper newUpper
      omega
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
      have leftBound : root ≤ n := by have := right.lower_le_upper; omega
      change node.owner before ≠ node.owner after at changed
      change node.owner after ∈
        (if node.heavyBranch before = node.heavyBranch after then ∅ else {node.owner after}) ∪
          junctionOwnersFrom before after left leftBound ∪ junctionOwnersFrom before after right upper_le_n
      by_cases same : node.heavyBranch before = node.heavyBranch after
      · simp only [same, ↓reduceIte, Finset.empty_union, Finset.mem_union]
        have oldOwner := node.owner_eq_branchMin_heavy before
        have newOwner := node.owner_eq_branchMin_heavy after
        rw [same] at oldOwner
        cases branch : node.heavyBranch after with
        | left =>
            rw [branch] at oldOwner newOwner
            change node.owner before = subtreeOwner before left leftBound at oldOwner
            change node.owner after = subtreeOwner after left leftBound at newOwner
            apply Or.inl
            rw [newOwner]
            apply ihLeft leftBound
            intro sameChild
            exact changed (oldOwner.trans (sameChild.trans newOwner.symm))
        | right =>
            rw [branch] at oldOwner newOwner
            change node.owner before = subtreeOwner before right upper_le_n at oldOwner
            change node.owner after = subtreeOwner after right upper_le_n at newOwner
            apply Or.inr
            rw [newOwner]
            apply ihRight upper_le_n
            intro sameChild
            exact changed (oldOwner.trans (sameChild.trans newOwner.symm))
        | middle =>
            rw [branch] at oldOwner newOwner
            apply False.elim (changed ?_)
            rw [oldOwner, newOwner]
            apply Fin.ext
            exact (node.branchMin_in_branch before .middle).trans (node.branchMin_in_branch after .middle).symm
      · simp [same]

/-- Each new edge is either an old edge, owned by a new junction owner, or
replaces an old edge leading to a changed minimum. This also accounts for
the parent above a changed heavy path, which need not itself be a junction. -/
theorem new_edge_owner_cases {n lower upper : ℕ} {before after : Snapshot n}
    {changed : Finset (External n)} (changes : before.MinimumChangesFrom after changed)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) (depth : ℕ)
    {edge : Edge n} (member : edge ∈ treeEdges after tree upper_le_n depth) :
    edge ∈ treeEdges before tree upper_le_n depth ∨
      edge.owner ∈ junctionOwnersFrom before after tree upper_le_n ∨
        ∃ oldEdge ∈ treeEdges before tree upper_le_n depth,
          oldEdge.owner = edge.owner ∧ oldEdge.child ∈ changed := by
  classical
  induction tree generalizing depth with
  | empty => exact Or.inl member
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
      have leftBound : root ≤ n := by have := right.lower_le_upper; omega
      have leftSubset : ∀ e ∈ treeEdges before left leftBound (depth + 1),
          e ∈ treeEdges before (.node left right) upper_le_n depth := by
        intro e inside
        exact List.mem_append_left _ (List.mem_append_right _ inside)
      have rightSubset : ∀ e ∈ treeEdges before right upper_le_n (depth + 1),
          e ∈ treeEdges before (.node left right) upper_le_n depth := by
        intro e inside
        exact List.mem_append_right _ inside
      rcases List.mem_append.mp member with localOrLeft | rightEdge
      · rcases List.mem_append.mp localOrLeft with localEdge | leftEdge
        · obtain ⟨branch, light, rfl⟩ := List.mem_map.mp localEdge
          by_cases sameOwner : node.owner after = node.owner before
          · have heavyEq := node.heavyBranch_eq_of_owner_eq sameOwner
            have oldLight : branch ∈ lightBranches before node := by
              rw [mem_lightBranches_iff]
              rw [mem_lightBranches_iff, heavyEq] at light
              exact light
            have oldMember : edgeFor before node depth branch ∈ treeEdges before (.node left right) upper_le_n depth :=
              List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨branch, oldLight, rfl⟩))
            by_cases childChanged : node.branchMin before branch ∈ changed
            · exact Or.inr (Or.inr ⟨edgeFor before node depth branch, oldMember, sameOwner.symm, childChanged⟩)
            · have childEq := node.branchMin_eq_of_minimumChangesFrom changes branch childChanged
              have edgeEq : edgeFor after node depth branch = edgeFor before node depth branch := by
                simp only [edgeFor, sameOwner, childEq]
              exact Or.inl (edgeEq.symm ▸ oldMember)
          · apply Or.inr ∘ Or.inl
            exact subtreeOwner_mem_junctionOwnersFrom_of_ne before after (.node left right) upper_le_n
              (Ne.symm sameOwner)
        · rcases ihLeft leftBound (depth + 1) leftEdge with old | junction | ⟨oldEdge, oldMember, ownerEq, marked⟩
          · exact Or.inl (leftSubset _ old)
          · apply Or.inr ∘ Or.inl
            exact Finset.mem_union_left _ (Finset.mem_union_right _ junction)
          · exact Or.inr (Or.inr ⟨oldEdge, leftSubset _ oldMember, ownerEq, marked⟩)
      · rcases ihRight upper_le_n (depth + 1) rightEdge with old | junction | ⟨oldEdge, oldMember, ownerEq, marked⟩
        · exact Or.inl (rightSubset _ old)
        · exact Or.inr (Or.inl (Finset.mem_union_right _ junction))
        · exact Or.inr (Or.inr ⟨oldEdge, rightSubset _ oldMember, ownerEq, marked⟩)

/-- All possible destinations of a changed parent edge: junction owners and
the former parents of changed vertices. -/
noncomputable def newParentSupport {n : ℕ} (before after : Snapshot n)
    (changed : Finset (External n)) (tree : BST 0 n) : Finset (External n) :=
  junctionOwnersFrom before after tree (Nat.le_refl n) ∪
    changed.image (fun element => (canonicalParent before tree element).getD (canonicalRoot before tree))

theorem newParentSupport_card_le {n : ℕ} (before after : Snapshot n)
    (changed : Finset (External n)) (tree : BST 0 n) :
    (newParentSupport before after changed tree).card ≤ junctionCount before after tree + changed.card :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add
    (junctionOwnersFrom_card_le before after tree (Nat.le_refl n)) (Finset.card_image_le))

/-- Every actual parent change lands in the bounded, explicitly constructed
support. This concerns the full canonical parent maps, not supplied lists of
operations or an assumed junction realization. -/
theorem changed_parent_mem_newParentSupport {n : ℕ} {before after : Snapshot n}
    {changed : Finset (External n)} (changes : before.MinimumChangesFrom after changed)
    (tree : BST 0 n) {owner child : External n}
    (parent : canonicalParent after tree child = some owner)
    (different : canonicalParent before tree child ≠ some owner) :
    owner ∈ newParentSupport before after changed tree := by
  classical
  simp only [canonicalParent, Option.map_eq_some_iff] at parent
  obtain ⟨edge, found, ownerEq⟩ := parent
  obtain ⟨member, childEq⟩ := incomingEdge?_some_mem after tree found
  rcases new_edge_owner_cases changes tree (Nat.le_refl n) 0 member with old | junction | ⟨oldEdge, oldMember, ownerSame, marked⟩
  · have oldParent := canonicalParent_eq_some_of_mem_fullEdges before tree edge old
    exact (different (by simpa only [ownerEq, childEq] using oldParent)).elim
  · exact Finset.mem_union_left _ (ownerEq ▸ junction)
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨oldEdge.child, marked, ?_⟩
    rw [canonicalParent_eq_some_of_mem_fullEdges before tree oldEdge oldMember]
    exact ownerSame.trans ownerEq

/-- Owners whose child orders may change in a rank restoration. -/
noncomputable def affectedOwnerSupport {n : ℕ} (before after : Snapshot n)
    (changed : Finset (External n)) (tree : BST 0 n) : Finset (External n) :=
  changed ∪ newParentSupport before after changed tree

theorem affectedOwnerSupport_card_le {n : ℕ} (before after : Snapshot n)
    (changed : Finset (External n)) (tree : BST 0 n) :
    (affectedOwnerSupport before after changed tree).card ≤ junctionCount before after tree + 2 * changed.card := by
  have unionBound := Finset.card_union_le changed (newParentSupport before after changed tree)
  have supportBound := newParentSupport_card_le before after changed tree
  change (changed ∪ newParentSupport before after changed tree).card ≤ _
  omega

/-- An owner outside the support neither gains nor loses children. -/
theorem parent_iff_of_not_mem_affectedOwnerSupport {n : ℕ} {before after : Snapshot n}
    {changed : Finset (External n)} (changes : before.MinimumChangesFrom after changed)
    (tree : BST 0 n) {owner : External n}
    (outside : owner ∉ affectedOwnerSupport before after changed tree) (child : External n) :
    canonicalParent after tree child = some owner ↔ canonicalParent before tree child = some owner := by
  classical
  have ordinary : owner ∉ changed := fun inside => outside (Finset.mem_union_left _ inside)
  have notNew : owner ∉ newParentSupport before after changed tree := fun inside => outside (Finset.mem_union_right _ inside)
  constructor
  · intro parent
    by_contra different
    exact notNew (changed_parent_mem_newParentSupport changes tree parent different)
  · intro parent
    have childOrdinary : child ∉ changed := by
      intro marked
      apply notNew
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨child, marked, by simp [parent]⟩
    exact canonicalParent_eq_of_minimumChangesFrom changes tree parent ordinary childOrdinary

/-- The complete sorted child lists of every unrelated owner are identical;
all its lazy intervals can therefore be retained without splitting. -/
theorem topDown_eq_of_not_mem_affectedOwnerSupport {n : ℕ} {before after : Snapshot n}
    {changed : Finset (External n)} (changes : before.MinimumChangesFrom after changed)
    (tree : BST 0 n) {owner : External n}
    (outside : owner ∉ affectedOwnerSupport before after changed tree) (side : Lazy.Side) :
    (canonicalHeapView after tree).topDown owner side = (canonicalHeapView before tree).topDown owner side := by
  have parents := parent_iff_of_not_mem_affectedOwnerSupport changes tree outside
  have sameSide {child : External n} (old : canonicalParent before tree child = some owner)
      (new : canonicalParent after tree child = some owner) :
      canonicalSide after tree child = canonicalSide before tree child := by
    have oldOrder := canonicalSide_order before tree old
    have newOrder := canonicalSide_order after tree new
    cases oldSide : canonicalSide before tree child <;>
      cases newSide : canonicalSide after tree child <;>
      simp only [oldSide, newSide] at oldOrder newOrder ⊢ <;> omega
  have members : ∀ child, child ∈ (canonicalHeapView after tree).topDown owner side ↔
      child ∈ (canonicalHeapView before tree).topDown owner side := by
    intro child
    rw [Lazy.HeapView.mem_topDown_iff, Lazy.HeapView.mem_topDown_iff]
    constructor
    · rintro ⟨parent, childSide⟩
      have oldParent := (parents child).mp parent
      exact ⟨oldParent, (sameSide oldParent parent).symm.trans childSide⟩
    · rintro ⟨parent, childSide⟩
      have newParent := (parents child).mpr parent
      exact ⟨newParent, (sameSide parent newParent).trans childSide⟩
  cases side with
  | left =>
      exact List.Pairwise.eq_of_mem_iff ((canonicalHeapView after tree).topDown_ordered owner).1
        ((canonicalHeapView before tree).topDown_ordered owner).1 members
  | right =>
      exact List.Pairwise.eq_of_mem_iff ((canonicalHeapView after tree).topDown_ordered owner).2
        ((canonicalHeapView before tree).topDown_ordered owner).2 members

end Splay.Accounting.JunctionBendReduction
