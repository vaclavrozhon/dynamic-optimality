import Splay.Accounting.JunctionAttachmentOrder
import Splay.Accounting.JunctionCutRootOwner
import Splay.Accounting.JunctionExceptionalChildren

namespace Splay.Accounting.JunctionBendReduction

open Splay.Rank Splay.Tree Splay.Lazy Splay.Lazy.Canonical

theorem treeEdge_depth_le {n lower upper : ℕ} (snapshot : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (depth : ℕ) {edge : Edge n}
    (member : edge ∈ treeEdges snapshot tree upper_le_n depth) : depth ≤ edge.attachmentDepth := by
  induction tree generalizing depth with
  | empty => simp [treeEdges] at member
  | @node lower root upper left right ihLeft ihRight =>
      rcases List.mem_append.mp member with localOrLeft | inRight
      · rcases List.mem_append.mp localOrLeft with localEdge | inLeft
        · have valid := mem_edgesAtNode_valid snapshot ⟨lower, root, upper, left, right, upper_le_n⟩ depth localEdge
          exact Nat.le_of_eq valid.2.2.2.2.2.1.symm
        · exact (Nat.le_add_right depth 1).trans (ihLeft _ _ inLeft)
      · exact (Nat.le_add_right depth 1).trans (ihRight _ _ inRight)

private theorem sideOf_eq_of_same_branches {n root : ℕ} {heavy light : TernaryBranch}
    {oldOwner newOwner oldChild newChild : External n}
    (different : light ≠ heavy)
    (oldOwnerIn : heavy.Contains root oldOwner.val) (newOwnerIn : heavy.Contains root newOwner.val)
    (oldChildIn : light.Contains root oldChild.val) (newChildIn : light.Contains root newChild.val) :
    sideOf oldOwner oldChild = sideOf newOwner newChild := by
  have order : oldChild.val < oldOwner.val ↔ newChild.val < newOwner.val := by
    cases heavy <;> cases light
    all_goals simp only [TernaryBranch.Contains] at *
    all_goals first | exact (different rfl).elim | omega
  simp only [sideOf, order]

/-- Corresponding light edges at an unchanged heavy branch retain side and
attachment, even when the light subtree has a different minimum child. -/
theorem exists_old_local_edge_of_heavyBranch_eq {n : ℕ} (before after : Snapshot n)
    (node : AtNode n) (depth : ℕ) (sameBranch : node.heavyBranch before = node.heavyBranch after)
    {next : Edge n} (member : next ∈ edgesAtNode after node depth) :
    ∃ old ∈ edgesAtNode before node depth, old.owner = node.owner before ∧
      old.branch = next.branch ∧ old.attachmentKey = next.attachmentKey ∧
      old.attachmentDepth = next.attachmentDepth ∧ old.side = next.side := by
  obtain ⟨branch, light, rfl⟩ := List.mem_map.mp member
  have afterLight := (mem_lightBranches_iff after node branch).mp light
  have beforeLight : branch ≠ node.heavyBranch before := by simpa only [sameBranch] using afterLight
  refine ⟨edgeFor before node depth branch,
    List.mem_map.mpr ⟨branch, (mem_lightBranches_iff before node branch).mpr beforeLight, rfl⟩,
    rfl, rfl, rfl, rfl, ?_⟩
  exact sideOf_eq_of_same_branches beforeLight (node.owner_in_heavyBranch before)
    (by rw [sameBranch]; exact node.owner_in_heavyBranch after)
    (node.branchMin_in_branch before branch) (node.branchMin_in_branch after branch)

/-- A cut-free root-to-endpoint corridor admits a reverse correspondence for
every new root-owned edge above that endpoint. The child itself may change;
the branch, attachment node, depth, side, and old ownership are recovered. -/
theorem exists_old_prefix_edge_of_sameCutCell_outside {n lower upper : ℕ}
    (before after : Snapshot n) (tree : BST lower upper) (upper_le_n : upper ≤ n) (depth : ℕ)
    {endpoint next : Edge n} {reference : External n}
    (endpointMember : endpoint ∈ treeEdges before tree upper_le_n depth)
    (endpointOwner : endpoint.owner = subtreeOwner before tree upper_le_n)
    (outside : reference.val < 2 * lower ∨ 2 * upper < reference.val)
    (sameCell : SameCutCell (junctionCutsFrom before after tree upper_le_n) reference endpoint.child)
    (nextMember : next ∈ treeEdges after tree upper_le_n depth)
    (nextOwner : next.owner = subtreeOwner after tree upper_le_n)
    (above : next.attachmentDepth ≤ endpoint.attachmentDepth) :
    ∃ old ∈ treeEdges before tree upper_le_n depth, old.owner = subtreeOwner before tree upper_le_n ∧
      old.branch = next.branch ∧ old.attachmentKey = next.attachmentKey ∧
      old.attachmentDepth = next.attachmentDepth ∧ old.side = next.side := by
  classical
  induction tree generalizing depth with
  | empty => simp [treeEdges] at endpointMember
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
      have leftBound : root ≤ n := by have := right.lower_le_upper; omega
      have inside := (mem_treeEdges_inside before (.node left right) upper_le_n endpointMember).2.2
      have sameBranch : node.heavyBranch before = node.heavyBranch after :=
        heavyBranch_eq_of_sameCutCell_outside before after left right upper_le_n outside inside sameCell
      change endpoint.owner = node.owner before at endpointOwner
      change next.owner = node.owner after at nextOwner
      change ∃ old ∈ treeEdges before (.node left right) upper_le_n depth, old.owner = node.owner before ∧ _
      by_cases localNext : next ∈ edgesAtNode after node depth
      · obtain ⟨old, oldMember, properties⟩ := exists_old_local_edge_of_heavyBranch_eq before after node depth sameBranch localNext
        exact ⟨old, List.mem_append_left _ (List.mem_append_left _ oldMember), properties⟩
      have nextCases : next ∈ treeEdges after left leftBound (depth + 1) ∨
          next ∈ treeEdges after right upper_le_n (depth + 1) := by
        rcases List.mem_append.mp nextMember with prefixMember | inRight
        · exact Or.inl ((List.mem_append.mp prefixMember).resolve_left localNext)
        · exact Or.inr inRight
      rcases List.mem_append.mp endpointMember with localOrLeft | endpointRight
      · rcases List.mem_append.mp localOrLeft with endpointLocal | endpointLeft
        · have endpointDepth := (mem_edgesAtNode_valid before node depth endpointLocal).2.2.2.2.2.1
          rcases nextCases with nextLeft | nextRight
          · have below := treeEdge_depth_le after left leftBound (depth + 1) nextLeft
            omega
          · have below := treeEdge_depth_le after right upper_le_n (depth + 1) nextRight
            omega
        · have oldInside := mem_treeEdges_inside before left leftBound endpointLeft
          have heavyBefore := node.heavyBranch_eq_left_of_owner_le_root before (by rw [← endpointOwner]; exact oldInside.2.1)
          have heavyAfter : node.heavyBranch after = .left := sameBranch.symm.trans heavyBefore
          have oldRoot := node.owner_eq_branchMin_heavy before
          have newRoot := node.owner_eq_branchMin_heavy after
          rw [heavyBefore] at oldRoot
          rw [heavyAfter] at newRoot
          change node.owner before = subtreeOwner before left leftBound at oldRoot
          change node.owner after = subtreeOwner after left leftBound at newRoot
          rcases nextCases with nextLeft | nextRight
          · obtain ⟨old, oldMember, ownerEq, agreement⟩ := ihLeft leftBound (depth + 1) endpointLeft
              (endpointOwner.trans oldRoot)
              (by have := right.lower_le_upper; omega)
              (sameCell.mono (by intro cut member; exact Finset.mem_union_left _ (Finset.mem_union_right _ member)))
              nextLeft (nextOwner.trans newRoot)
            exact ⟨old, List.mem_append_left _ (List.mem_append_right _ oldMember), ownerEq.trans oldRoot.symm, agreement⟩
          · have impossible := mem_treeEdges_inside after right upper_le_n nextRight
            have ownerHigh : 2 * (root + 1) ≤ next.owner.val := impossible.1
            have ownerLow := node.owner_in_heavyBranch after
            rw [heavyAfter, ← nextOwner] at ownerLow
            change next.owner.val ≤ 2 * root at ownerLow
            omega
      · have oldInside := mem_treeEdges_inside before right upper_le_n endpointRight
        have heavyBefore := node.heavyBranch_eq_right_of_root_lt_owner before (by rw [← endpointOwner]; exact oldInside.1)
        have heavyAfter : node.heavyBranch after = .right := sameBranch.symm.trans heavyBefore
        have oldRoot := node.owner_eq_branchMin_heavy before
        have newRoot := node.owner_eq_branchMin_heavy after
        rw [heavyBefore] at oldRoot
        rw [heavyAfter] at newRoot
        change node.owner before = subtreeOwner before right upper_le_n at oldRoot
        change node.owner after = subtreeOwner after right upper_le_n at newRoot
        rcases nextCases with nextLeft | nextRight
        · have impossible := mem_treeEdges_inside after left leftBound nextLeft
          have ownerLow : next.owner.val ≤ 2 * root := impossible.2.1
          have ownerHigh := node.owner_in_heavyBranch after
          rw [heavyAfter, ← nextOwner] at ownerHigh
          change 2 * root + 2 ≤ next.owner.val at ownerHigh
          omega
        · obtain ⟨old, oldMember, ownerEq, agreement⟩ := ihRight upper_le_n (depth + 1) endpointRight
            (endpointOwner.trans oldRoot)
            (by have := left.lower_le_upper; omega)
            (sameCell.mono (by intro cut member; exact Finset.mem_union_right _ member))
            nextRight (nextOwner.trans newRoot)
          exact ⟨old, List.mem_append_right _ oldMember, ownerEq.trans oldRoot.symm, agreement⟩

/-- An unmarked local light child certifies that its attachment node is not
a junction. This also covers changes of the minimum in a light subtree. -/
theorem heavyBranch_eq_of_local_child_ordinary {n lower root upper : ℕ}
    (before after : Snapshot n) (left : BST lower root) (right : BST (root + 1) upper)
    (upper_le_n : upper ≤ n) (depth : ℕ) {edge : Edge n}
    (localEdge : edge ∈ edgesAtNode before ⟨lower, root, upper, left, right, upper_le_n⟩ depth)
    (ordinary : edge.child ∉ junctionChildrenFrom before after (.node left right) upper_le_n) :
    (⟨lower, root, upper, left, right, upper_le_n⟩ : AtNode n).heavyBranch before =
      (⟨lower, root, upper, left, right, upper_le_n⟩ : AtNode n).heavyBranch after := by
  classical
  let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
  change node.heavyBranch before = node.heavyBranch after
  by_contra junction
  apply ordinary
  have childMember : edge.child ∈ ((edgesAtNode before node 0).map Edge.child).toFinset := by
    obtain ⟨branch, light, rfl⟩ := List.mem_map.mp localEdge
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨edgeFor before node 0 branch,
      List.mem_map.mpr ⟨branch, light, rfl⟩, rfl⟩)
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  change edge.child ∈ (if node.heavyBranch before = node.heavyBranch after then ∅ else _)
  rw [if_neg junction]
  exact Finset.mem_union_left _ childMember

/-- Recover an old light edge for every new edge strictly between two
ordinary attachments in one cut cell. No unchanged-child assumption is made
for the intermediate edge, which is essential at light-subtree minimum changes. -/
theorem exists_old_between_edge_of_sameCutCell {n lower upper : ℕ}
    (before after : Snapshot n) (tree : BST lower upper) (upper_le_n : upper ≤ n) (depth : ℕ)
    {first last firstNext next : Edge n}
    (firstMember : first ∈ treeEdges before tree upper_le_n depth)
    (lastMember : last ∈ treeEdges before tree upper_le_n depth)
    (sameOwner : first.owner = last.owner)
    (firstOrdinary : first.child ∉ junctionChildrenFrom before after tree upper_le_n)
    (sameCell : SameCutCell (junctionCutsFrom before after tree upper_le_n) first.child last.child)
    (firstNextMember : firstNext ∈ treeEdges after tree upper_le_n depth)
    (firstAttachment : firstNext.attachmentKey = first.attachmentKey)
    (nextMember : next ∈ treeEdges after tree upper_le_n depth)
    (nextOwner : next.owner = firstNext.owner)
    (firstAbove : edgeStrictlyAbove first next) (lastBelow : edgeStrictlyAbove next last) :
    ∃ old ∈ treeEdges before tree upper_le_n depth, old.owner = first.owner ∧
      old.branch = next.branch ∧ old.attachmentKey = next.attachmentKey ∧
      old.attachmentDepth = next.attachmentDepth ∧ old.side = next.side := by
  classical
  have firstDepth : first.attachmentDepth ≤ next.attachmentDepth := by
    rcases firstAbove with less | equal
    · exact Nat.le_of_lt less
    · exact Nat.le_of_eq equal.1
  have lastDepth : next.attachmentDepth ≤ last.attachmentDepth := by
    rcases lastBelow with less | equal
    · exact Nat.le_of_lt less
    · exact Nat.le_of_eq equal.1
  induction tree generalizing depth with
  | empty => simp [treeEdges] at firstMember
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
      have leftBound : root ≤ n := by have := right.lower_le_upper; omega
      have firstLocation := treeEdge_location_iff after left right upper_le_n depth firstNextMember
      by_cases firstLocal : first ∈ edgesAtNode before node depth
      · have firstValid := mem_edgesAtNode_valid before node depth firstLocal
        have firstNextLocal := firstLocation.1.mpr (firstAttachment.trans firstValid.attachmentKey_eq)
        have firstNextValid := mem_edgesAtNode_valid after node depth firstNextLocal
        have sameBranch : node.heavyBranch before = node.heavyBranch after :=
          heavyBranch_eq_of_local_child_ordinary before after left right upper_le_n depth firstLocal firstOrdinary
        by_cases nextLocal : next ∈ edgesAtNode after node depth
        · obtain ⟨old, oldMember, ownerEq, agreement⟩ :=
            exists_old_local_edge_of_heavyBranch_eq before after node depth sameBranch nextLocal
          exact ⟨old, List.mem_append_left _ (List.mem_append_left _ oldMember), ownerEq.trans firstValid.2.1.symm, agreement⟩
        have nextCases : next ∈ treeEdges after left leftBound (depth + 1) ∨
            next ∈ treeEdges after right upper_le_n (depth + 1) := by
          rcases List.mem_append.mp nextMember with prefixMember | inRight
          · exact Or.inl ((List.mem_append.mp prefixMember).resolve_left nextLocal)
          · exact Or.inr inRight
        rcases List.mem_append.mp lastMember with localOrLeft | lastRight
        · rcases List.mem_append.mp localOrLeft with lastLocal | lastLeft
          · have localDepth := (mem_edgesAtNode_valid before node depth lastLocal).2.2.2.2.2.1
            rcases nextCases with nextLeft | nextRight
            · have below := treeEdge_depth_le after left leftBound (depth + 1) nextLeft
              omega
            · have below := treeEdge_depth_le after right upper_le_n (depth + 1) nextRight
              omega
          · have lastOwner : last.owner = node.owner before := sameOwner.symm.trans firstValid.2.1
            have lastInside := mem_treeEdges_inside before left leftBound lastLeft
            have heavyBefore := node.heavyBranch_eq_left_of_owner_le_root before (by rw [← lastOwner]; exact lastInside.2.1)
            have heavyAfter : node.heavyBranch after = .left := sameBranch.symm.trans heavyBefore
            have oldRoot := node.owner_eq_branchMin_heavy before
            have newRoot := node.owner_eq_branchMin_heavy after
            rw [heavyBefore] at oldRoot
            rw [heavyAfter] at newRoot
            change node.owner before = subtreeOwner before left leftBound at oldRoot
            change node.owner after = subtreeOwner after left leftBound at newRoot
            rcases nextCases with nextLeft | nextRight
            · obtain ⟨old, oldMember, ownerEq, agreement⟩ := exists_old_prefix_edge_of_sameCutCell_outside
                before after left leftBound (depth + 1) lastLeft (lastOwner.trans oldRoot)
                (Or.inr (firstValid.child_gt_root_of_heavy_left heavyBefore))
                (sameCell.mono (by intro cut member; exact Finset.mem_union_left _ (Finset.mem_union_right _ member)))
                nextLeft (nextOwner.trans (firstNextValid.2.1.trans newRoot)) lastDepth
              exact ⟨old, List.mem_append_left _ (List.mem_append_right _ oldMember),
                ownerEq.trans (oldRoot.symm.trans firstValid.2.1.symm), agreement⟩
            · have high : 2 * (root + 1) ≤ next.owner.val := (mem_treeEdges_inside after right upper_le_n nextRight).1
              have low := node.owner_in_heavyBranch after
              rw [heavyAfter, ← firstNextValid.2.1, ← nextOwner] at low
              change next.owner.val ≤ 2 * root at low
              omega
        · have lastOwner : last.owner = node.owner before := sameOwner.symm.trans firstValid.2.1
          have lastInside := mem_treeEdges_inside before right upper_le_n lastRight
          have heavyBefore := node.heavyBranch_eq_right_of_root_lt_owner before (by rw [← lastOwner]; exact lastInside.1)
          have heavyAfter : node.heavyBranch after = .right := sameBranch.symm.trans heavyBefore
          have oldRoot := node.owner_eq_branchMin_heavy before
          have newRoot := node.owner_eq_branchMin_heavy after
          rw [heavyBefore] at oldRoot
          rw [heavyAfter] at newRoot
          change node.owner before = subtreeOwner before right upper_le_n at oldRoot
          change node.owner after = subtreeOwner after right upper_le_n at newRoot
          rcases nextCases with nextLeft | nextRight
          · have low : next.owner.val ≤ 2 * root := (mem_treeEdges_inside after left leftBound nextLeft).2.1
            have high := node.owner_in_heavyBranch after
            rw [heavyAfter, ← firstNextValid.2.1, ← nextOwner] at high
            change 2 * root + 2 ≤ next.owner.val at high
            omega
          · obtain ⟨old, oldMember, ownerEq, agreement⟩ := exists_old_prefix_edge_of_sameCutCell_outside
              before after right upper_le_n (depth + 1) lastRight (lastOwner.trans oldRoot)
              (Or.inl (by have outside := firstValid.child_lt_root_of_heavy_right heavyBefore; omega))
              (sameCell.mono (by intro cut member; exact Finset.mem_union_right _ member))
              nextRight (nextOwner.trans (firstNextValid.2.1.trans newRoot)) lastDepth
            exact ⟨old, List.mem_append_right _ oldMember,
              ownerEq.trans (oldRoot.symm.trans firstValid.2.1.symm), agreement⟩
      · have firstCases : first ∈ treeEdges before left leftBound (depth + 1) ∨
            first ∈ treeEdges before right upper_le_n (depth + 1) := by
          rcases List.mem_append.mp firstMember with prefixMember | inRight
          · exact Or.inl ((List.mem_append.mp prefixMember).resolve_left firstLocal)
          · exact Or.inr inRight
        have nextNotLocal : next ∉ edgesAtNode after node depth := by
          intro localNext
          have nextAtRoot := (mem_edgesAtNode_valid after node depth localNext).2.2.2.2.2.1
          rcases firstCases with firstLeft | firstRight
          · have deeper := treeEdge_depth_le before left leftBound (depth + 1) firstLeft
            omega
          · have deeper := treeEdge_depth_le before right upper_le_n (depth + 1) firstRight
            omega
        have lastNotLocal : last ∉ edgesAtNode before node depth := by
          intro localLast
          have lastAtRoot := (mem_edgesAtNode_valid before node depth localLast).2.2.2.2.2.1
          rcases firstCases with firstLeft | firstRight
          · have deeper := treeEdge_depth_le before left leftBound (depth + 1) firstLeft
            omega
          · have deeper := treeEdge_depth_le before right upper_le_n (depth + 1) firstRight
            omega
        have lastCases : last ∈ treeEdges before left leftBound (depth + 1) ∨
            last ∈ treeEdges before right upper_le_n (depth + 1) := by
          rcases List.mem_append.mp lastMember with prefixMember | inRight
          · exact Or.inl ((List.mem_append.mp prefixMember).resolve_left lastNotLocal)
          · exact Or.inr inRight
        have nextCases : next ∈ treeEdges after left leftBound (depth + 1) ∨
            next ∈ treeEdges after right upper_le_n (depth + 1) := by
          rcases List.mem_append.mp nextMember with prefixMember | inRight
          · exact Or.inl ((List.mem_append.mp prefixMember).resolve_left nextNotLocal)
          · exact Or.inr inRight
        rcases firstCases with firstLeft | firstRight
        · have firstNextLeft := firstLocation.2.1.mpr (by rw [firstAttachment]; exact (mem_treeEdges_attachmentKey_bounds before left leftBound firstLeft).2)
          have firstLow : first.owner.val ≤ 2 * root := (mem_treeEdges_inside before left leftBound firstLeft).2.1
          have nextLow : next.owner.val ≤ 2 * root := by rw [nextOwner]; exact (mem_treeEdges_inside after left leftBound firstNextLeft).2.1
          rcases lastCases with lastLeft | lastRight
          · rcases nextCases with nextLeft | nextRight
            · obtain ⟨old, oldMember, properties⟩ := ihLeft leftBound (depth + 1) firstLeft lastLeft
                (fun member => firstOrdinary (Finset.mem_union_left _ (Finset.mem_union_right _ member)))
                (sameCell.mono (by intro cut member; exact Finset.mem_union_left _ (Finset.mem_union_right _ member)))
                firstNextLeft nextLeft
              exact ⟨old, List.mem_append_left _ (List.mem_append_right _ oldMember), properties⟩
            · have high : 2 * (root + 1) ≤ next.owner.val := (mem_treeEdges_inside after right upper_le_n nextRight).1
              omega
          · have high : 2 * (root + 1) ≤ last.owner.val := (mem_treeEdges_inside before right upper_le_n lastRight).1
            have equal := congrArg Fin.val sameOwner
            omega
        · have firstNextRight := firstLocation.2.2.mpr (by rw [firstAttachment]; have bound := (mem_treeEdges_attachmentKey_bounds before right upper_le_n firstRight).1; omega)
          have firstHigh : 2 * (root + 1) ≤ first.owner.val := (mem_treeEdges_inside before right upper_le_n firstRight).1
          have nextHigh : 2 * (root + 1) ≤ next.owner.val := by rw [nextOwner]; exact (mem_treeEdges_inside after right upper_le_n firstNextRight).1
          rcases lastCases with lastLeft | lastRight
          · have low : last.owner.val ≤ 2 * root := (mem_treeEdges_inside before left leftBound lastLeft).2.1
            have equal := congrArg Fin.val sameOwner
            omega
          · rcases nextCases with nextLeft | nextRight
            · have low : next.owner.val ≤ 2 * root := (mem_treeEdges_inside after left leftBound nextLeft).2.1
              omega
            · obtain ⟨old, oldMember, properties⟩ := ihRight upper_le_n (depth + 1) firstRight lastRight
                (fun member => firstOrdinary (Finset.mem_union_right _ member))
                (sameCell.mono (by intro cut member; exact Finset.mem_union_right _ member))
                firstNextRight nextRight
              exact ⟨old, List.mem_append_right _ oldMember, properties⟩

end Splay.Accounting.JunctionBendReduction
