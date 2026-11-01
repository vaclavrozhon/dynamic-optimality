import Splay.Accounting.JunctionOwnerSupport

namespace Splay.Accounting.JunctionBendReduction

open Splay.Rank Splay.Tree Splay.Lazy.Canonical

theorem junctionCountFrom_comm {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) :
    junctionCountFrom before after tree upper_le_n = junctionCountFrom after before tree upper_le_n := by
  induction tree with
  | empty => simp [junctionCountFrom]
  | @node lower root upper left right ihLeft ihRight =>
      simp only [junctionCountFrom, ihLeft, ihRight]
      split_ifs <;> grind

/-- Only old and new junction owners can change their incoming attachment
node or outgoing ternary branch. These are the vertices to isolate before a
simultaneous block relocation. -/
noncomputable def junctionVerticesFrom {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) : Finset (External n) :=
  junctionOwnersFrom before after tree upper_le_n ∪ junctionOwnersFrom after before tree upper_le_n

theorem junctionVerticesFrom_card_le {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) :
    (junctionVerticesFrom before after tree upper_le_n).card ≤ 2 * junctionCountFrom before after tree upper_le_n := by
  have first := junctionOwnersFrom_card_le before after tree upper_le_n
  have second := junctionOwnersFrom_card_le after before tree upper_le_n
  rw [← junctionCountFrom_comm before after] at second
  have unionBound := Finset.card_union_le (junctionOwnersFrom before after tree upper_le_n)
    (junctionOwnersFrom after before tree upper_le_n)
  unfold junctionVerticesFrom
  omega

theorem junctionVerticesFrom_comm {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) :
    junctionVerticesFrom before after tree upper_le_n = junctionVerticesFrom after before tree upper_le_n :=
  Finset.union_comm _ _

/-- After excluding the bounded junction vertices, each canonical light
edge retains its exact child, attachment key, attachment depth and branch.
Only its heavy-path owner and hence its side may change. -/
theorem exists_edge_same_attachment_of_not_mem_junctionVertices {n lower upper : ℕ}
    (before after : Snapshot n) (tree : BST lower upper) (upper_le_n : upper ≤ n) (depth : ℕ)
    {edge : Edge n} (member : edge ∈ treeEdges before tree upper_le_n depth)
    (ordinary : edge.child ∉ junctionVerticesFrom before after tree upper_le_n) :
    ∃ next ∈ treeEdges after tree upper_le_n depth,
      next.child = edge.child ∧ next.branch = edge.branch ∧
        next.attachmentKey = edge.attachmentKey ∧ next.attachmentDepth = edge.attachmentDepth := by
  classical
  induction tree generalizing depth with
  | empty => simp [treeEdges] at member
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
      have leftBound : root ≤ n := by have := right.lower_le_upper; omega
      have leftSubset : junctionVerticesFrom before after left leftBound ⊆
          junctionVerticesFrom before after (.node left right) upper_le_n := by
        intro element inside
        rcases Finset.mem_union.mp inside with forward | backward
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ forward))
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ backward))
      have rightSubset : junctionVerticesFrom before after right upper_le_n ⊆
          junctionVerticesFrom before after (.node left right) upper_le_n := by
        intro element inside
        rcases Finset.mem_union.mp inside with forward | backward
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ forward)
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ backward)
      rcases List.mem_append.mp member with localOrLeft | rightEdge
      · rcases List.mem_append.mp localOrLeft with localEdge | leftEdge
        · obtain ⟨branch, light, rfl⟩ := List.mem_map.mp localEdge
          have childSame : node.branchMin after branch = node.branchMin before branch := by
            by_contra changed
            apply ordinary
            cases branch with
            | left =>
                apply leftSubset
                apply Finset.mem_union_right
                exact subtreeOwner_mem_junctionOwnersFrom_of_ne after before left leftBound changed
            | right =>
                apply rightSubset
                apply Finset.mem_union_right
                exact subtreeOwner_mem_junctionOwnersFrom_of_ne after before right upper_le_n changed
            | middle =>
                apply False.elim (changed ?_)
                apply Fin.ext
                exact (node.branchMin_in_branch after .middle).trans (node.branchMin_in_branch before .middle).symm
          have stillLight : branch ≠ node.heavyBranch after := by
            intro nowHeavy
            have oldLight := (mem_lightBranches_iff before node branch).mp light
            have junction : node.heavyBranch before ≠ node.heavyBranch after := by
              intro same
              exact oldLight (nowHeavy.trans same.symm)
            have childOwner : node.branchMin before branch = node.owner after := by
              rw [← childSame, nowHeavy]
              exact (node.owner_eq_branchMin_heavy after).symm
            apply ordinary
            change node.branchMin before branch ∈ _
            rw [childOwner]
            apply Finset.mem_union_left
            apply Finset.mem_union_left
            apply Finset.mem_union_left
            change node.owner after ∈ (if node.heavyBranch before = node.heavyBranch after then ∅ else {node.owner after})
            rw [if_neg junction]
            exact Finset.mem_singleton_self _
          refine ⟨edgeFor after node depth branch, ?_, childSame, rfl, rfl, rfl⟩
          apply List.mem_append_left
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨branch, (mem_lightBranches_iff after node branch).mpr stillLight, rfl⟩
        · obtain ⟨next, nextMember, properties⟩ := ihLeft leftBound (depth + 1) leftEdge
            (fun inside => ordinary (leftSubset inside))
          exact ⟨next, List.mem_append_left _ (List.mem_append_right _ nextMember), properties⟩
      · obtain ⟨next, nextMember, properties⟩ := ihRight upper_le_n (depth + 1) rightEdge
          (fun inside => ordinary (rightSubset inside))
        exact ⟨next, List.mem_append_right _ nextMember, properties⟩

end Splay.Accounting.JunctionBendReduction
