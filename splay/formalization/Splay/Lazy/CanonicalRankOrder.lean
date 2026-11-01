import Splay.Lazy.CanonicalHeapView

namespace Splay.Lazy.Canonical

open Splay.Rank Splay.Tree Splay.Tree.BST

/-- The old subtree owner stays minimal under any ranks increasing along
all old light edges. No comparison between unrelated siblings is needed. -/
theorem subtreeOwner_isMin_of_edge_order
    {n lower upper : ℕ} (snapshot : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (depth : ℕ) (rank : External n → ℕ)
    (ordered : ∀ edge ∈ treeEdges snapshot tree upper_le_n depth,
      rank edge.owner < rank edge.child) :
    IsIntervalMin rank (subtreeLower tree upper_le_n) (subtreeUpper tree upper_le_n)
      (subtreeOwner snapshot tree upper_le_n) := by
  induction tree generalizing depth with
  | empty boundary =>
      have oldMin := subtreeOwner_isMin snapshot (.empty boundary) upper_le_n
      refine ⟨oldMin.1, oldMin.2.1, ?_⟩
      intro element elementLower elementUpper
      have equal : element = subtreeOwner snapshot (.empty boundary) upper_le_n := by
        apply Fin.ext
        change 2 * boundary ≤ element.val at elementLower
        change element.val ≤ 2 * boundary at elementUpper
        have minLower : 2 * boundary ≤ (subtreeOwner snapshot (.empty boundary) upper_le_n).val := oldMin.1
        have minUpper : (subtreeOwner snapshot (.empty boundary) upper_le_n).val ≤ 2 * boundary := oldMin.2.1
        omega
      rw [equal]
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
      have leftBound : root ≤ n := by have := right.lower_le_upper; omega
      have localOrdered : ∀ edge ∈ edgesAtNode snapshot node depth, rank edge.owner < rank edge.child := by
        intro edge member
        exact ordered edge (List.mem_append_left _ (List.mem_append_left _ member))
      have leftOrdered : ∀ edge ∈ treeEdges snapshot left leftBound (depth + 1), rank edge.owner < rank edge.child := by
        intro edge member
        exact ordered edge (List.mem_append_left _ (List.mem_append_right _ member))
      have rightOrdered : ∀ edge ∈ treeEdges snapshot right upper_le_n (depth + 1), rank edge.owner < rank edge.child := by
        intro edge member
        exact ordered edge (List.mem_append_right _ member)
      have leftMin := ihLeft leftBound (depth + 1) leftOrdered
      have rightMin := ihRight upper_le_n (depth + 1) rightOrdered
      have ownerLe : ∀ branch, rank (node.owner snapshot) ≤ rank (node.branchMin snapshot branch) := by
        intro branch
        by_cases heavy : branch = node.heavyBranch snapshot
        · rw [heavy, ← node.owner_eq_branchMin_heavy snapshot]
        · exact Nat.le_of_lt (localOrdered (edgeFor snapshot node depth branch)
            (List.mem_map.mpr ⟨branch, (mem_lightBranches_iff _ _ _).mpr heavy, rfl⟩))
      have oldMin := node.owner_isMin snapshot
      refine ⟨oldMin.1, oldMin.2.1, ?_⟩
      intro element elementLower elementUpper
      change 2 * lower ≤ element.val at elementLower
      change element.val ≤ 2 * upper at elementUpper
      change rank (node.owner snapshot) ≤ rank element
      by_cases onLeft : element.val ≤ 2 * root
      · exact (ownerLe .left).trans (leftMin.2.2 element elementLower onLeft)
      · by_cases atRoot : element.val = 2 * root + 1
        · have equal : node.branchMin snapshot .middle = element := by
            apply Fin.ext
            have contains := node.branchMin_in_branch snapshot .middle
            change (node.branchMin snapshot .middle).val = 2 * root + 1 at contains
            omega
          rw [← equal]
          exact ownerLe .middle
        · exact (ownerLe .right).trans (rightMin.2.2 element (by change 2 * (root + 1) ≤ element.val; omega) elementUpper)

/-- Respecting the old light-edge order keeps the exact canonical owner. -/
theorem subtreeOwner_eq_of_edge_order
    {n lower upper : ℕ} (first second : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (depth : ℕ)
    (ordered : ∀ edge ∈ treeEdges first tree upper_le_n depth,
      second.rank edge.owner < second.rank edge.child) :
    subtreeOwner second tree upper_le_n = subtreeOwner first tree upper_le_n := by
  symm
  exact second.intervalMin_unique _ _ _
    (subtreeOwner_isMin_of_edge_order first tree upper_le_n depth second.rank ordered)

/-- Preserving the order of every old light edge preserves the entire
canonical decomposition, including attachments and sides. -/
theorem treeEdges_eq_of_edge_order
    {n lower upper : ℕ} (first second : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (depth : ℕ)
    (ordered : ∀ edge ∈ treeEdges first tree upper_le_n depth,
      second.rank edge.owner < second.rank edge.child) :
    treeEdges second tree upper_le_n depth = treeEdges first tree upper_le_n depth := by
  induction tree generalizing depth with
  | empty boundary => rfl
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
      have leftBound : root ≤ n := by have := right.lower_le_upper; omega
      have leftOrdered : ∀ edge ∈ treeEdges first left leftBound (depth + 1),
          second.rank edge.owner < second.rank edge.child := by
        intro edge member
        exact ordered edge (List.mem_append_left _ (List.mem_append_right _ member))
      have rightOrdered : ∀ edge ∈ treeEdges first right upper_le_n (depth + 1),
          second.rank edge.owner < second.rank edge.child := by
        intro edge member
        exact ordered edge (List.mem_append_right _ member)
      have ownerEq : node.owner second = node.owner first :=
        subtreeOwner_eq_of_edge_order first second (.node left right) upper_le_n depth ordered
      have branchEq : ∀ branch, node.branchMin second branch = node.branchMin first branch := by
        intro branch
        cases branch with
        | left => exact subtreeOwner_eq_of_edge_order first second left leftBound (depth + 1) leftOrdered
        | right => exact subtreeOwner_eq_of_edge_order first second right upper_le_n (depth + 1) rightOrdered
        | middle =>
            apply Fin.ext
            exact (node.branchMin_in_branch second .middle).trans (node.branchMin_in_branch first .middle).symm
      have heavyEq : node.heavyBranch second = node.heavyBranch first := by
        apply first.heavyBranch_unique
        refine ⟨node.owner first, node.owner_isMin first, ?_⟩
        rw [← ownerEq]
        exact node.owner_in_heavyBranch second
      have localEq : edgesAtNode second node depth = edgesAtNode first node depth := by
        simp only [edgesAtNode, lightBranches, heavyEq]
        apply List.map_congr_left
        intro branch _
        simp only [edgeFor, ownerEq, branchEq]
      change edgesAtNode second node depth ++ treeEdges second left leftBound (depth + 1) ++
          treeEdges second right upper_le_n (depth + 1) =
        edgesAtNode first node depth ++ treeEdges first left leftBound (depth + 1) ++
          treeEdges first right upper_le_n (depth + 1)
      rw [localEq, ihLeft leftBound (depth + 1) leftOrdered, ihRight upper_le_n (depth + 1) rightOrdered]

/-- A canonical heap remains canonical under any target snapshot which
orders its existing edges. Ranks and the canonical depth witness may change. -/
theorem canonical_parent_side_eq_of_order
    {n : ℕ} (first second : Snapshot n) (tree : BST 0 n)
    (ordered : ∀ {element owner}, canonicalParent first tree element = some owner →
      second.rank owner < second.rank element) :
    canonicalRoot second tree = canonicalRoot first tree ∧
      canonicalParent second tree = canonicalParent first tree ∧
      canonicalSide second tree = canonicalSide first tree := by
  have edgeOrdered : ∀ edge ∈ fullEdges first tree,
      second.rank edge.owner < second.rank edge.child := by
    intro edge member
    have childNotRoot : edge.child ≠ canonicalRoot first tree := by
      intro equal
      have strict := mem_treeEdges_rank_lt first tree (Nat.le_refl n) member
      rw [equal, rank_canonicalRoot_eq_zero] at strict
      omega
    obtain ⟨incoming, lookup, inEdges, child⟩ := exists_incomingEdge?_eq_some_of_ne_root first tree childNotRoot
    obtain ⟨unique, _, uniqueness⟩ := existsUnique_fullEdge_child_of_ne_root first tree edge.child childNotRoot
    have equal : incoming = edge :=
      (uniqueness incoming ⟨inEdges, child⟩).trans (uniqueness edge ⟨member, rfl⟩).symm
    apply ordered
    simp [canonicalParent, lookup, equal]
  have edgesEq : fullEdges second tree = fullEdges first tree :=
    treeEdges_eq_of_edge_order first second tree (Nat.le_refl n) 0 edgeOrdered
  have rootEq : canonicalRoot second tree = canonicalRoot first tree :=
    subtreeOwner_eq_of_edge_order first second tree (Nat.le_refl n) 0 edgeOrdered
  have incomingEq : ∀ element, incomingEdge? second tree element = incomingEdge? first tree element := by
    intro element
    by_cases root : element = canonicalRoot first tree
    · simp [incomingEdge?, rootEq, root]
    · have notSecond : element ≠ canonicalRoot second tree := by simpa [rootEq] using root
      obtain ⟨oldEdge, oldLookup, oldMember, oldChild⟩ :=
        exists_incomingEdge?_eq_some_of_ne_root first tree root
      obtain ⟨newEdge, newLookup, newMember, newChild⟩ :=
        exists_incomingEdge?_eq_some_of_ne_root second tree notSecond
      obtain ⟨unique, _, uniqueness⟩ := existsUnique_fullEdge_child_of_ne_root first tree element root
      rw [edgesEq] at newMember
      have equal : newEdge = oldEdge :=
        (uniqueness newEdge ⟨newMember, newChild⟩).trans (uniqueness oldEdge ⟨oldMember, oldChild⟩).symm
      rw [newLookup, oldLookup, equal]
  refine ⟨rootEq, ?_, ?_⟩
  · funext element
    simp only [canonicalParent, incomingEq]
  · funext element
    simp only [canonicalSide, incomingEq]

end Splay.Lazy.Canonical
