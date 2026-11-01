import Splay.Accounting.RootHeavyPathFullOrder
import Splay.Accounting.WholeSplayTemporaryBoundaryGeometry

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST
open Splay.Lazy.Canonical

/-- Proper-ancestor light edges followed by the two light edges at the
accessed node.  This is the full pre-splay heavy-path child list before the
manuscript isolates `x⁻` and `x⁺`. -/
noncomputable def rootHeavyPathEdgesWithBoundariesTopDown
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key : ℕ) (depth : ℕ := 0) : List (Edge n) :=
  match tree with
  | .empty _ => []
  | .node (root := root) left right =>
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      if key = root then
        edgesAtNode snapshot node depth
      else if key < root then
        (rootHeavyPathCellAt snapshot node depth key).fullTopDownEdges ++
          rootHeavyPathEdgesWithBoundariesTopDown snapshot left (by
            have := right.lower_le_upper
            omega) key (depth + 1)
      else
        (rootHeavyPathCellAt snapshot node depth key).fullTopDownEdges ++
          rootHeavyPathEdgesWithBoundariesTopDown snapshot right upper_le_n
            key (depth + 1)

/-- Rank zero makes the accessed external value the canonical owner at every
node on its search path. -/
theorem atNode_owner_eq_accessed
    {n : ℕ} (snapshot : Snapshot n) (node : AtNode n) (key : ℕ)
    (insideLower : node.lower ≤ key) (insideUpper : key < node.upper)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    node.owner snapshot = valuePos ⟨key, key_lt_n⟩ := by
  let accessed : External n := valuePos ⟨key, key_lt_n⟩
  have insideWhole :
      node.wholeLower ≤ accessed ∧ accessed ≤ node.wholeUpper := by
    change 2 * node.lower ≤ 2 * key + 1 ∧
      2 * key + 1 ≤ 2 * node.upper
    omega
  have accessedIsMin :
      IsIntervalMin snapshot.rank node.wholeLower node.wholeUpper
        accessed := by
    refine ⟨insideWhole.1, insideWhole.2, ?_⟩
    intro other _ _
    rw [show snapshot.rank accessed = 0 by
      simpa only [accessed] using rankZero]
    exact Nat.zero_le _
  exact
    (snapshot.intervalMin_unique
      node.wholeLower node.wholeUpper node.whole_nonempty
      accessedIsMin).symm

/-- Children of a concrete edge list restricted to one heap side. -/
def edgeChildrenOnSide {n : ℕ} (edges : List (Edge n))
    (childSide : Side) : List (External n) :=
  (edges.filter fun edge => decide (edge.side = childSide)).map Edge.child

@[simp] theorem edgeChildrenOnSide_nil {n : ℕ} (childSide : Side) :
    edgeChildrenOnSide ([] : List (Edge n)) childSide = [] := by
  simp [edgeChildrenOnSide]

@[simp] theorem edgeChildrenOnSide_append {n : ℕ}
    (first second : List (Edge n)) (childSide : Side) :
    edgeChildrenOnSide (first ++ second) childSide =
      edgeChildrenOnSide first childSide ++
        edgeChildrenOnSide second childSide := by
  simp [edgeChildrenOnSide]

/-- At an ancestor to the right of the access, the two local light children
are right children, ordered outer-before-middle in top-down order. -/
theorem edgeChildrenOnSide_cell_of_key_lt_root
    {n : ℕ} (snapshot : Snapshot n) (node : AtNode n)
    (depth key : ℕ)
    (insideLower : node.lower ≤ key) (insideUpper : key < node.upper)
    (keyLtRoot : key < node.root) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    edgeChildrenOnSide
        (rootHeavyPathCellAt snapshot node depth key).fullTopDownEdges
        .left = [] ∧
      edgeChildrenOnSide
        (rootHeavyPathCellAt snapshot node depth key).fullTopDownEdges
        .right =
          [node.branchMin snapshot .right,
            node.branchMin snapshot .middle] := by
  have heavy : node.heavyBranch snapshot = .left :=
    heavyBranch_eq_searchBranch snapshot node key insideLower insideUpper
      (by omega) key_lt_n rankZero |>.trans (if_pos keyLtRoot)
  have ownerEq := atNode_owner_eq_accessed snapshot node key insideLower
    insideUpper key_lt_n rankZero
  have middleContains := node.branchMin_in_branch snapshot .middle
  have rightContains := node.branchMin_in_branch snapshot .right
  have accessedLtMiddle :
      (valuePos ⟨key, key_lt_n⟩).val <
        (node.branchMin snapshot .middle).val := by
    change 2 * key + 1 < (node.branchMin snapshot .middle).val
    change (node.branchMin snapshot .middle).val = 2 * node.root + 1 at middleContains
    omega
  have accessedLtRight :
      (valuePos ⟨key, key_lt_n⟩).val <
        (node.branchMin snapshot .right).val := by
    change 2 * key + 1 < (node.branchMin snapshot .right).val
    change 2 * node.root + 2 ≤
      (node.branchMin snapshot .right).val at rightContains
    omega
  have accessedLeMiddle :
      valuePos ⟨key, key_lt_n⟩ ≤ node.branchMin snapshot .middle := by
    exact Fin.mk_le_mk.mpr (Nat.le_of_lt accessedLtMiddle)
  have accessedLeRight :
      valuePos ⟨key, key_lt_n⟩ ≤ node.branchMin snapshot .right := by
    exact Fin.mk_le_mk.mpr (Nat.le_of_lt accessedLtRight)
  constructor <;>
    simp [edgeChildrenOnSide, RootHeavyPathCell.fullTopDownEdges,
      rootHeavyPathCellAt, hitSide, show ¬node.root < key by omega,
      edgesAtNode, lightBranches, allBranches, heavy, edgeFor, sideOf,
      ownerEq, accessedLeMiddle, accessedLeRight]

/-- At an ancestor to the left of the access, the two local light children
are left children, again in top-down order. -/
theorem edgeChildrenOnSide_cell_of_root_lt_key
    {n : ℕ} (snapshot : Snapshot n) (node : AtNode n)
    (depth key : ℕ)
    (insideLower : node.lower ≤ key) (insideUpper : key < node.upper)
    (rootLtKey : node.root < key) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    edgeChildrenOnSide
        (rootHeavyPathCellAt snapshot node depth key).fullTopDownEdges
        .left =
          [node.branchMin snapshot .left,
            node.branchMin snapshot .middle] ∧
      edgeChildrenOnSide
        (rootHeavyPathCellAt snapshot node depth key).fullTopDownEdges
        .right = [] := by
  have heavy : node.heavyBranch snapshot = .right :=
    heavyBranch_eq_searchBranch snapshot node key insideLower insideUpper
      (by omega) key_lt_n rankZero |>.trans (if_neg (by omega))
  have ownerEq := atNode_owner_eq_accessed snapshot node key insideLower
    insideUpper key_lt_n rankZero
  have leftContains := node.branchMin_in_branch snapshot .left
  have middleContains := node.branchMin_in_branch snapshot .middle
  have leftLtAccessed :
      (node.branchMin snapshot .left).val <
        (valuePos ⟨key, key_lt_n⟩).val := by
    change (node.branchMin snapshot .left).val < 2 * key + 1
    change (node.branchMin snapshot .left).val ≤ 2 * node.root at leftContains
    omega
  have middleLtAccessed :
      (node.branchMin snapshot .middle).val <
        (valuePos ⟨key, key_lt_n⟩).val := by
    change (node.branchMin snapshot .middle).val < 2 * key + 1
    change (node.branchMin snapshot .middle).val = 2 * node.root + 1 at middleContains
    omega
  constructor <;>
    simp [edgeChildrenOnSide, RootHeavyPathCell.fullTopDownEdges,
      rootHeavyPathCellAt, hitSide, rootLtKey, edgesAtNode, lightBranches,
      allBranches, heavy, edgeFor, sideOf, ownerEq, leftLtAccessed,
      middleLtAccessed]

/-- At the accessed node itself, the two light branches are precisely one
left and one right boundary child. -/
theorem edgeChildrenOnSide_accessedNode
    {n : ℕ} (snapshot : Snapshot n) (node : AtNode n)
    (depth : ℕ) (key_lt_n : node.root < n)
    (rankZero :
      snapshot.rank (valuePos ⟨node.root, key_lt_n⟩) = 0) :
    edgeChildrenOnSide (edgesAtNode snapshot node depth) .left =
        [node.branchMin snapshot .left] ∧
      edgeChildrenOnSide (edgesAtNode snapshot node depth) .right =
        [node.branchMin snapshot .right] := by
  have insideLower : node.lower ≤ node.root := node.lower_le_root
  have insideUpper : node.root < node.upper := node.root_lt_upper
  have ownerEq := atNode_owner_eq_accessed snapshot node node.root
    insideLower insideUpper key_lt_n rankZero
  have insideWhole :
      node.wholeLower ≤ valuePos ⟨node.root, key_lt_n⟩ ∧
        valuePos ⟨node.root, key_lt_n⟩ ≤ node.wholeUpper := by
    change 2 * node.lower ≤ 2 * node.root + 1 ∧
      2 * node.root + 1 ≤ 2 * node.upper
    omega
  have heavy : node.heavyBranch snapshot = .middle := by
    apply node.heavyBranch_eq_of_rank_eq_zero snapshot .middle
      (valuePos ⟨node.root, key_lt_n⟩) rankZero insideWhole
    simp only [TernaryBranch.middle_contains_iff, valuePos]
  have leftContains := node.branchMin_in_branch snapshot .left
  have rightContains := node.branchMin_in_branch snapshot .right
  have leftLtAccessed :
      (node.branchMin snapshot .left).val <
        (valuePos ⟨node.root, key_lt_n⟩).val := by
    change (node.branchMin snapshot .left).val < 2 * node.root + 1
    change (node.branchMin snapshot .left).val ≤ 2 * node.root at leftContains
    omega
  have accessedLtRight :
      (valuePos ⟨node.root, key_lt_n⟩).val <
        (node.branchMin snapshot .right).val := by
    change 2 * node.root + 1 < (node.branchMin snapshot .right).val
    change 2 * node.root + 2 ≤
      (node.branchMin snapshot .right).val at rightContains
    omega
  have accessedLeRight :
      valuePos ⟨node.root, key_lt_n⟩ ≤
        node.branchMin snapshot .right := by
    exact Fin.mk_le_mk.mpr (Nat.le_of_lt accessedLtRight)
  constructor <;>
    simp [edgeChildrenOnSide, edgesAtNode, lightBranches, allBranches, heavy,
      edgeFor, sideOf, ownerEq, leftLtAccessed, accessedLeRight]

/-- The inclusive search-path list is exactly the set of canonical light
edges whose heap owner is the accessed rank-zero value. -/
theorem mem_rootHeavyPathEdgesWithBoundariesTopDown_iff
    {n lower upper key : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (insideLower : lower ≤ key) (insideUpper : key < upper)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (depth : ℕ) (edge : Edge n) :
    edge ∈ rootHeavyPathEdgesWithBoundariesTopDown
        snapshot tree upper_le_n key depth ↔
      edge ∈ treeEdges snapshot tree upper_le_n depth ∧
        edge.owner = valuePos ⟨key, key_lt_n⟩ := by
  induction tree generalizing depth with
  | empty =>
      omega
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      have nodeOwner :
          node.owner snapshot = valuePos ⟨key, key_lt_n⟩ :=
        atNode_owner_eq_accessed snapshot node key insideLower insideUpper
          key_lt_n rankZero
      by_cases atRoot : key = root
      · subst key
        constructor
        · intro member
          have localMember : edge ∈ edgesAtNode snapshot node depth := by
            simpa [rootHeavyPathEdgesWithBoundariesTopDown] using member
          exact ⟨by
            simp only [treeEdges]
            exact List.mem_append_left _ (List.mem_append_left _ localMember),
            (mem_edgesAtNode_valid snapshot node depth localMember).2.1.trans
              nodeOwner⟩
        · rintro ⟨member, ownerEq⟩
          simp only [treeEdges] at member
          rcases List.mem_append.mp member with prefixMember | rightMember
          · rcases List.mem_append.mp prefixMember with localMember |
                leftMember
            · simpa [rootHeavyPathEdgesWithBoundariesTopDown] using
                localMember
            · have inside :=
                mem_treeEdges_inside snapshot left (by
                  have := right.lower_le_upper
                  omega) leftMember
              rw [ownerEq] at inside
              have ownerUpper := inside.2.1
              change (valuePos ⟨root, key_lt_n⟩).val ≤ 2 * root at ownerUpper
              simp only [valuePos] at ownerUpper
              omega
          · have inside :=
              mem_treeEdges_inside snapshot right upper_le_n rightMember
            rw [ownerEq] at inside
            have ownerLower := inside.1
            change 2 * (root + 1) ≤
              (valuePos ⟨root, key_lt_n⟩).val at ownerLower
            simp only [valuePos] at ownerLower
            omega
      · by_cases inLeft : key < root
        · have leftUpper : root ≤ n := by
            have := right.lower_le_upper
            omega
          constructor
          · intro member
            have member' := member
            simp only [rootHeavyPathEdgesWithBoundariesTopDown, atRoot,
              inLeft, ↓reduceIte] at member'
            have cases :
                edge ∈ (rootHeavyPathCellAt snapshot node depth key).fullTopDownEdges ∨
                  edge ∈ rootHeavyPathEdgesWithBoundariesTopDown
                    snapshot left leftUpper key (depth + 1) := by
              simpa only [node] using List.mem_append.mp member'
            rcases cases with localMember | childMember
            · have rawMember :
                  edge ∈ edgesAtNode snapshot node depth :=
                (rootHeavyPathCellAt snapshot node depth key)
                  |>.fullTopDownEdges_perm_edges.mem_iff.mp localMember
              exact ⟨by
                simp only [treeEdges]
                exact List.mem_append_left _
                  (List.mem_append_left _ rawMember),
                (rootHeavyPathCellAt_edge_geometry snapshot node depth key
                  insideLower insideUpper atRoot key_lt_n rankZero
                  rawMember).1⟩
            · have childSpec :=
                (ihLeft leftUpper insideLower inLeft (depth + 1)).mp
                  childMember
              exact ⟨by
                simp only [treeEdges]
                exact List.mem_append_left _
                  (List.mem_append_right _ childSpec.1), childSpec.2⟩
          · rintro ⟨member, ownerEq⟩
            simp only [treeEdges] at member
            rcases List.mem_append.mp member with prefixMember | rightMember
            · rcases List.mem_append.mp prefixMember with localMember |
                  leftMember
              · have fullMember :
                    edge ∈
                      RootHeavyPathCell.fullTopDownEdges
                        (rootHeavyPathCellAt snapshot node depth key) := by
                    have perm :=
                      RootHeavyPathCell.fullTopDownEdges_perm_edges
                        (rootHeavyPathCellAt snapshot node depth key)
                    exact perm.mem_iff.mpr localMember
                have result := List.mem_append_left
                    (rootHeavyPathEdgesWithBoundariesTopDown
                      snapshot left leftUpper key (depth + 1)) fullMember
                simpa [rootHeavyPathEdgesWithBoundariesTopDown, atRoot,
                    inLeft, node] using result
              · have childMember :=
                    (ihLeft leftUpper insideLower inLeft (depth + 1)).mpr
                      ⟨leftMember, ownerEq⟩
                have result := List.mem_append_right
                  (RootHeavyPathCell.fullTopDownEdges
                    (rootHeavyPathCellAt snapshot node depth key)) childMember
                simpa [rootHeavyPathEdgesWithBoundariesTopDown, atRoot,
                    inLeft, node] using result
            · have inside :=
                mem_treeEdges_inside snapshot right upper_le_n rightMember
              rw [ownerEq] at inside
              have ownerLower := inside.1
              change 2 * (root + 1) ≤
                (valuePos ⟨key, key_lt_n⟩).val at ownerLower
              simp only [valuePos] at ownerLower
              omega
        · have rootLtKey : root < key := by omega
          constructor
          · intro member
            have member' := member
            simp only [rootHeavyPathEdgesWithBoundariesTopDown, atRoot,
              inLeft, ↓reduceIte] at member'
            have cases :
                edge ∈ (rootHeavyPathCellAt snapshot node depth key).fullTopDownEdges ∨
                  edge ∈ rootHeavyPathEdgesWithBoundariesTopDown
                    snapshot right upper_le_n key (depth + 1) := by
              simpa only [node] using List.mem_append.mp member'
            rcases cases with localMember | childMember
            · have rawMember :
                  edge ∈ edgesAtNode snapshot node depth :=
                (rootHeavyPathCellAt snapshot node depth key)
                  |>.fullTopDownEdges_perm_edges.mem_iff.mp localMember
              exact ⟨by
                simp only [treeEdges]
                exact List.mem_append_left _
                  (List.mem_append_left _ rawMember),
                (rootHeavyPathCellAt_edge_geometry snapshot node depth key
                  insideLower insideUpper atRoot key_lt_n rankZero
                  rawMember).1⟩
            · have childSpec :=
                (ihRight upper_le_n (by omega) insideUpper (depth + 1)).mp
                  childMember
              exact ⟨by
                simp only [treeEdges]
                exact List.mem_append_right _ childSpec.1, childSpec.2⟩
          · rintro ⟨member, ownerEq⟩
            simp only [treeEdges] at member
            rcases List.mem_append.mp member with prefixMember | rightMember
            · rcases List.mem_append.mp prefixMember with localMember |
                  leftMember
              · have fullMember :
                    edge ∈
                      RootHeavyPathCell.fullTopDownEdges
                        (rootHeavyPathCellAt snapshot node depth key) := by
                    have perm :=
                      RootHeavyPathCell.fullTopDownEdges_perm_edges
                        (rootHeavyPathCellAt snapshot node depth key)
                    exact perm.mem_iff.mpr localMember
                have result := List.mem_append_left
                    (rootHeavyPathEdgesWithBoundariesTopDown
                      snapshot right upper_le_n key (depth + 1)) fullMember
                simpa [rootHeavyPathEdgesWithBoundariesTopDown, atRoot,
                    inLeft, node] using result
              · have inside :=
                  mem_treeEdges_inside snapshot left (by
                    have := right.lower_le_upper
                    omega) leftMember
                rw [ownerEq] at inside
                have ownerUpper := inside.2.1
                change (valuePos ⟨key, key_lt_n⟩).val ≤ 2 * root at ownerUpper
                simp only [valuePos] at ownerUpper
                omega
            · have childMember :=
                  (ihRight upper_le_n (by omega) insideUpper
                    (depth + 1)).mpr ⟨rightMember, ownerEq⟩
              have result := List.mem_append_right
                (RootHeavyPathCell.fullTopDownEdges
                  (rootHeavyPathCellAt snapshot node depth key)) childMember
              simpa [rootHeavyPathEdgesWithBoundariesTopDown, atRoot,
                inLeft, node] using result

/-- Side-restricted child projection of the inclusive search-path edge list. -/
noncomputable def rootHeavyPathChildrenWithBoundariesTopDown
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key : ℕ) (childSide : Side) (depth : ℕ := 0) :
    List (External n) :=
  edgeChildrenOnSide
    (rootHeavyPathEdgesWithBoundariesTopDown
      snapshot tree upper_le_n key depth) childSide

/-- Every inclusive search-path child stays in the indexed subtree interval. -/
theorem rootHeavyPathChildrenWithBoundariesTopDown_bounds
    {n lower upper key : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (insideLower : lower ≤ key) (insideUpper : key < upper)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (depth : ℕ) (childSide : Side) {child : External n}
    (member : child ∈ rootHeavyPathChildrenWithBoundariesTopDown
      snapshot tree upper_le_n key childSide depth) :
    subtreeLower tree upper_le_n ≤ child ∧
      child ≤ subtreeUpper tree upper_le_n := by
  obtain ⟨edge, edgeMember, childEq⟩ := List.mem_map.mp member
  have inclusiveMember :
      edge ∈ rootHeavyPathEdgesWithBoundariesTopDown
        snapshot tree upper_le_n key depth :=
    (List.mem_filter.mp edgeMember).1
  have treeMember :=
    (mem_rootHeavyPathEdgesWithBoundariesTopDown_iff snapshot tree upper_le_n
      insideLower insideUpper key_lt_n rankZero depth edge).mp
      inclusiveMember |>.1
  have inside := mem_treeEdges_inside snapshot tree upper_le_n treeMember
  subst child
  exact ⟨inside.2.2.1, inside.2.2.2⟩

/-- The two side projections of the inclusive list already have exactly the
left-increasing/right-decreasing order used by `HeapView.topDown`. -/
theorem rootHeavyPathChildrenWithBoundariesTopDown_pairwise
    {n lower upper key : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (insideLower : lower ≤ key) (insideUpper : key < upper)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (depth : ℕ) :
    (rootHeavyPathChildrenWithBoundariesTopDown
        snapshot tree upper_le_n key .left depth).Pairwise
          (fun earlier later => earlier.val < later.val) ∧
      (rootHeavyPathChildrenWithBoundariesTopDown
        snapshot tree upper_le_n key .right depth).Pairwise
          (fun earlier later => later.val < earlier.val) := by
  induction tree generalizing depth with
  | empty =>
      omega
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      by_cases atRoot : key = root
      · subst key
        have localChildren := edgeChildrenOnSide_accessedNode snapshot node depth
          key_lt_n rankZero
        have leftEq :
            rootHeavyPathChildrenWithBoundariesTopDown snapshot
                (.node left right) upper_le_n root .left depth =
              [node.branchMin snapshot .left] := by
          simpa [rootHeavyPathChildrenWithBoundariesTopDown,
            rootHeavyPathEdgesWithBoundariesTopDown, node] using localChildren.1
        have rightEq :
            rootHeavyPathChildrenWithBoundariesTopDown snapshot
                (.node left right) upper_le_n root .right depth =
              [node.branchMin snapshot .right] := by
          simpa [rootHeavyPathChildrenWithBoundariesTopDown,
            rootHeavyPathEdgesWithBoundariesTopDown, node] using localChildren.2
        rw [leftEq, rightEq]
        simp
      · by_cases inLeft : key < root
        · have leftUpper : root ≤ n := by
            have := right.lower_le_upper
            omega
          have localChildren := edgeChildrenOnSide_cell_of_key_lt_root
            snapshot node depth key insideLower insideUpper inLeft key_lt_n
            rankZero
          have childPairwise :=
            ihLeft leftUpper insideLower inLeft (depth + 1)
          have leftEq :
              rootHeavyPathChildrenWithBoundariesTopDown snapshot
                  (.node left right) upper_le_n key .left depth =
                rootHeavyPathChildrenWithBoundariesTopDown snapshot left
                  leftUpper key .left (depth + 1) := by
            simp [rootHeavyPathChildrenWithBoundariesTopDown,
              rootHeavyPathEdgesWithBoundariesTopDown, atRoot, inLeft,
              localChildren.1, node]
          have rightEq :
              rootHeavyPathChildrenWithBoundariesTopDown snapshot
                  (.node left right) upper_le_n key .right depth =
                [node.branchMin snapshot .right,
                    node.branchMin snapshot .middle] ++
                  rootHeavyPathChildrenWithBoundariesTopDown snapshot left
                    leftUpper key .right (depth + 1) := by
            simp [rootHeavyPathChildrenWithBoundariesTopDown,
              rootHeavyPathEdgesWithBoundariesTopDown, atRoot, inLeft,
              localChildren.2, node]
          rw [leftEq, rightEq]
          refine ⟨childPairwise.1, List.pairwise_append.mpr ⟨?_,
            childPairwise.2, ?_⟩⟩
          · apply List.pairwise_pair.mpr
            have middleContains := node.branchMin_in_branch snapshot .middle
            have rightContains := node.branchMin_in_branch snapshot .right
            change (node.branchMin snapshot .middle).val <
              (node.branchMin snapshot .right).val
            change (node.branchMin snapshot .middle).val = 2 * root + 1 at middleContains
            change 2 * root + 2 ≤
              (node.branchMin snapshot .right).val at rightContains
            omega
          · intro first firstMember second secondMember
            have secondBounds :=
              rootHeavyPathChildrenWithBoundariesTopDown_bounds snapshot left
                leftUpper insideLower inLeft key_lt_n rankZero (depth + 1)
                .right secondMember
            have secondUpper : second.val ≤ 2 * root := by
              have raw := Fin.mk_le_mk.mp secondBounds.2
              simpa [subtreeUpper] using raw
            simp only [List.mem_pair] at firstMember
            rcases firstMember with firstEq | firstEq <;> subst first
            · have rightContains := node.branchMin_in_branch snapshot .right
              change 2 * root + 2 ≤
                (node.branchMin snapshot .right).val at rightContains
              omega
            · have middleContains := node.branchMin_in_branch snapshot .middle
              change (node.branchMin snapshot .middle).val =
                2 * root + 1 at middleContains
              omega
        · have rootLtKey : root < key := by omega
          have localChildren := edgeChildrenOnSide_cell_of_root_lt_key
            snapshot node depth key insideLower insideUpper rootLtKey key_lt_n
            rankZero
          have childPairwise :=
            ihRight upper_le_n (by omega) insideUpper (depth + 1)
          have leftEq :
              rootHeavyPathChildrenWithBoundariesTopDown snapshot
                  (.node left right) upper_le_n key .left depth =
                [node.branchMin snapshot .left,
                    node.branchMin snapshot .middle] ++
                  rootHeavyPathChildrenWithBoundariesTopDown snapshot right
                    upper_le_n key .left (depth + 1) := by
            simp [rootHeavyPathChildrenWithBoundariesTopDown,
              rootHeavyPathEdgesWithBoundariesTopDown, atRoot, inLeft,
              localChildren.1, node]
          have rightEq :
              rootHeavyPathChildrenWithBoundariesTopDown snapshot
                  (.node left right) upper_le_n key .right depth =
                rootHeavyPathChildrenWithBoundariesTopDown snapshot right
                  upper_le_n key .right (depth + 1) := by
            simp [rootHeavyPathChildrenWithBoundariesTopDown,
              rootHeavyPathEdgesWithBoundariesTopDown, atRoot, inLeft,
              localChildren.2, node]
          rw [leftEq, rightEq]
          refine ⟨List.pairwise_append.mpr ⟨?_, childPairwise.1, ?_⟩,
            childPairwise.2⟩
          · apply List.pairwise_pair.mpr
            have leftContains := node.branchMin_in_branch snapshot .left
            have middleContains := node.branchMin_in_branch snapshot .middle
            change (node.branchMin snapshot .left).val <
              (node.branchMin snapshot .middle).val
            change (node.branchMin snapshot .left).val ≤ 2 * root at leftContains
            change (node.branchMin snapshot .middle).val = 2 * root + 1 at middleContains
            omega
          · intro first firstMember second secondMember
            have secondBounds :=
              rootHeavyPathChildrenWithBoundariesTopDown_bounds snapshot right
                upper_le_n (by omega) insideUpper key_lt_n rankZero
                (depth + 1) .left secondMember
            have secondLower : 2 * (root + 1) ≤ second.val := by
              have raw := Fin.mk_le_mk.mp secondBounds.1
              simpa [subtreeLower] using raw
            simp only [List.mem_pair] at firstMember
            rcases firstMember with firstEq | firstEq <;> subst first
            · have leftContains := node.branchMin_in_branch snapshot .left
              change (node.branchMin snapshot .left).val ≤ 2 * root at leftContains
              omega
            · have middleContains := node.branchMin_in_branch snapshot .middle
              change (node.branchMin snapshot .middle).val =
                2 * root + 1 at middleContains
              omega

/-- The inclusive search-path projection is exactly the canonical heap-child
list of the accessed rank-zero element.  The two edges at the accessed node
account for the two boundary children that the manuscript isolates first. -/
theorem mem_rootHeavyPathChildrenWithBoundariesTopDown_iff_topDown
    {n key : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (childSide : Side) (child : External n) :
    child ∈ rootHeavyPathChildrenWithBoundariesTopDown snapshot tree
        (Nat.le_refl n) key childSide 0 ↔
      child ∈ (canonicalHeapView snapshot tree).topDown
        (valuePos ⟨key, key_lt_n⟩) childSide := by
  constructor
  · intro member
    obtain ⟨edge, edgeMember, childEq⟩ := List.mem_map.mp member
    have filtered := List.mem_filter.mp edgeMember
    have inclusiveSpec :=
      (mem_rootHeavyPathEdgesWithBoundariesTopDown_iff snapshot tree
        (Nat.le_refl n) (Nat.zero_le key) key_lt_n key_lt_n rankZero
        0 edge).mp filtered.1
    have fullMember : edge ∈ fullEdges snapshot tree := by
      simpa only [fullEdges] using inclusiveSpec.1
    have lookup :=
      incomingEdge?_eq_edge_of_mem_fullEdges snapshot tree fullMember
    have edgeSide : edge.side = childSide := by
      simpa only [decide_eq_true_eq] using filtered.2
    subst child
    apply (canonicalHeapView snapshot tree).mem_topDown_iff.mpr
    constructor
    · change canonicalParent snapshot tree edge.child =
          some (valuePos ⟨key, key_lt_n⟩)
      simp [canonicalParent, lookup, inclusiveSpec.2]
    · change canonicalSide snapshot tree edge.child = childSide
      simp [canonicalSide, lookup, edgeSide]
  · intro member
    have childFacts :=
      (canonicalHeapView snapshot tree).mem_topDown_iff.mp member
    obtain ⟨parentEq, childSideEq⟩ := childFacts
    change canonicalParent snapshot tree child =
      some (valuePos ⟨key, key_lt_n⟩) at parentEq
    change canonicalSide snapshot tree child = childSide at childSideEq
    simp only [canonicalParent, Option.map_eq_some_iff] at parentEq
    obtain ⟨edge, lookup, ownerEq⟩ := parentEq
    have edgeSpec := incomingEdge?_some_mem snapshot tree lookup
    have treeMember :
        edge ∈ treeEdges snapshot tree (Nat.le_refl n) 0 := by
      simpa only [fullEdges] using edgeSpec.1
    have inclusiveMember :=
      (mem_rootHeavyPathEdgesWithBoundariesTopDown_iff snapshot tree
        (Nat.le_refl n) (Nat.zero_le key) key_lt_n key_lt_n rankZero
        0 edge).mpr ⟨treeMember, ownerEq⟩
    have edgeSide : edge.side = childSide := by
      rw [← edgeSpec.2] at childSideEq
      have lookupChild :=
        incomingEdge?_eq_edge_of_mem_fullEdges snapshot tree edgeSpec.1
      simpa [canonicalSide, lookupChild] using childSideEq
    apply List.mem_map.mpr
    exact ⟨edge, List.mem_filter.mpr ⟨inclusiveMember, by
      simpa only [decide_eq_true_eq] using edgeSide⟩, edgeSpec.2⟩

/-- Hence the inclusive search-path projection and the canonical article
order agree as lists, not merely as sets. -/
theorem rootHeavyPathChildrenWithBoundariesTopDown_eq_topDown
    {n key : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (childSide : Side) :
    rootHeavyPathChildrenWithBoundariesTopDown snapshot tree
        (Nat.le_refl n) key childSide 0 =
      (canonicalHeapView snapshot tree).topDown
        (valuePos ⟨key, key_lt_n⟩) childSide := by
  have inclusiveOrdered :=
    rootHeavyPathChildrenWithBoundariesTopDown_pairwise snapshot tree
      (Nat.le_refl n) (Nat.zero_le key) key_lt_n key_lt_n rankZero 0
  have canonicalOrdered :=
    (canonicalHeapView snapshot tree).topDown_ordered
      (valuePos ⟨key, key_lt_n⟩)
  cases childSide with
  | left =>
      apply List.Pairwise.eq_of_mem_iff inclusiveOrdered.1 canonicalOrdered.1
      intro child
      exact mem_rootHeavyPathChildrenWithBoundariesTopDown_iff_topDown
        snapshot tree key_lt_n rankZero .left child
  | right =>
      apply List.Pairwise.eq_of_mem_iff inclusiveOrdered.2 canonicalOrdered.2
      intro child
      exact mem_rootHeavyPathChildrenWithBoundariesTopDown_iff_topDown
        snapshot tree key_lt_n rankZero .right child

namespace WholeSplayTemporaryBoundaryGeometry.KeyFocus

/-- The two canonical child minima at the terminal node selected by a focus. -/
noncomputable def boundaryChildrenFrom
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key : Fin n) (focus : KeyFocus key.val tree) :
    External n × External n := by
  induction focus with
  | @root lower upper left right =>
      exact
        (subtreeOwner snapshot left (by
            have bounds := right.lower_le_upper
            omega),
          subtreeOwner snapshot right upper_le_n)
  | @leftContext lower root upper left focus right ih =>
      exact ih (by
        have bounds := right.lower_le_upper
        omega)
  | @rightContext lower root upper left right focus ih =>
      exact ih upper_le_n

/-- The boundary record used by article Step 2 selects exactly those two
terminal child minima. -/
theorem boundaryMinimumSelectionFrom_pair_eq_boundaryChildrenFrom
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key : Fin n) (focus : KeyFocus key.val tree) :
    let selection :=
      boundaryMinimumSelectionFrom snapshot tree upper_le_n key focus
    (selection.left, selection.right) =
      boundaryChildrenFrom snapshot tree upper_le_n key focus := by
  induction focus with
  | @root lower upper left right =>
      rfl
  | @leftContext lower root upper left focus right ih =>
      simpa only [boundaryMinimumSelectionFrom,
        focusedBoundaryMinimumSelectionFrom, boundaryChildrenFrom] using
          ih (by
            have bounds := right.lower_le_upper
            omega)
  | @rightContext lower root upper left right focus ih =>
      simpa only [boundaryMinimumSelectionFrom,
        focusedBoundaryMinimumSelectionFrom, boundaryChildrenFrom] using
          ih upper_le_n

end WholeSplayTemporaryBoundaryGeometry.KeyFocus

/-- Before Step 2, each canonical side consists of the proper-ancestor
children followed by its one terminal boundary child. -/
theorem rootHeavyPathChildrenWithBoundariesTopDown_eq_proper_append_boundaryFrom
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key : Fin n)
    (focus : WholeSplayTemporaryBoundaryGeometry.KeyFocus key.val tree)
    (rankZero : snapshot.rank (valuePos key) = 0)
    (depth : ℕ) (childSide : Side) :
    rootHeavyPathChildrenWithBoundariesTopDown snapshot tree upper_le_n
        key.val childSide depth =
      edgeChildrenOnSide
          (rootHeavyPathEdgesTopDown snapshot tree upper_le_n key.val depth)
          childSide ++
        [match childSide with
          | .left =>
              (WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryChildrenFrom
                snapshot tree upper_le_n key focus).1
          | .right =>
              (WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryChildrenFrom
                snapshot tree upper_le_n key focus).2] := by
  induction focus generalizing depth with
  | @root lower upper left right =>
      let node : AtNode n := {
        lower := lower
        root := key.val
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      have localChildren :=
        edgeChildrenOnSide_accessedNode snapshot node depth key.isLt rankZero
      cases childSide <;>
        simp [rootHeavyPathChildrenWithBoundariesTopDown,
          rootHeavyPathEdgesWithBoundariesTopDown,
          rootHeavyPathEdgesTopDown, rootHeavyPathCellsTopDown,
          WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryChildrenFrom,
          localChildren.1, localChildren.2, node]
  | @leftContext lower root upper left focus right ih =>
      have keyLtRoot : key.val < root := focus.key_bounds.2
      have keyNeRoot : key.val ≠ root := ne_of_lt keyLtRoot
      have leftUpper : root ≤ n := by
        have bounds := right.lower_le_upper
        omega
      have childEq := ih leftUpper (depth + 1)
      simpa [rootHeavyPathChildrenWithBoundariesTopDown,
        rootHeavyPathEdgesWithBoundariesTopDown,
        rootHeavyPathEdgesTopDown, rootHeavyPathCellsTopDown,
        WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryChildrenFrom,
        keyNeRoot, keyLtRoot, childEq, List.append_assoc]
  | @rightContext lower root upper left right focus ih =>
      have rootLtKey : root < key.val := by
        have bounds := focus.key_bounds.1
        omega
      have keyNeRoot : key.val ≠ root := ne_of_gt rootLtKey
      have notLeft : ¬key.val < root := by omega
      have childEq := ih upper_le_n (depth + 1)
      simpa [rootHeavyPathChildrenWithBoundariesTopDown,
        rootHeavyPathEdgesWithBoundariesTopDown,
        rootHeavyPathEdgesTopDown, rootHeavyPathCellsTopDown,
        WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryChildrenFrom,
        keyNeRoot, notLeft, childEq, List.append_assoc]

/-- Filtering edge children by their canonical side is the same operation as
filtering the edge records before projecting their children. -/
theorem filter_map_edgeChild_canonicalSide_eq_edgeChildrenOnSide
    {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (edges : List (Edge n))
    (allFull : ∀ edge ∈ edges, edge ∈ fullEdges snapshot tree)
    (childSide : Side) :
    (edges.map Edge.child).filter (fun child => decide
        (canonicalSide snapshot tree child = childSide)) =
      edgeChildrenOnSide edges childSide := by
  induction edges with
  | nil =>
      simp [edgeChildrenOnSide]
  | cons edge edges ih =>
      have headFull := allFull edge (by simp)
      have tailFull : ∀ other ∈ edges, other ∈ fullEdges snapshot tree := by
        intro other member
        exact allFull other (by simp [member])
      have lookup :=
        incomingEdge?_eq_edge_of_mem_fullEdges snapshot tree headFull
      have sideEq :
          canonicalSide snapshot tree edge.child = edge.side := by
        simp [canonicalSide, lookup]
      have tailEq := ih tailFull
      by_cases selected : edge.side = childSide
      · simp [edgeChildrenOnSide, sideEq, selected, tailEq]
      · simp [edgeChildrenOnSide, sideEq, selected, tailEq]

/-- The side-filtered proper-ancestor article order is precisely the side
projection of the proper-ancestor edge list. -/
theorem rootHeavyPathCanonicalChildOrder_filter_eq_edgeChildrenOnSide
    {n key : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (childSide : Side) :
    (rootHeavyPathCanonicalChildOrder snapshot tree key_lt_n rankZero).elements.filter
        (fun child => decide
          (canonicalSide snapshot tree child = childSide)) =
      edgeChildrenOnSide
        (rootHeavyPathEdgesTopDown snapshot tree (Nat.le_refl n) key 0)
        childSide := by
  apply filter_map_edgeChild_canonicalSide_eq_edgeChildrenOnSide
  intro edge member
  exact rootHeavyPathEdgesTopDown_mem_fullEdges snapshot tree member

/-- Exact article geometry before Step 2: the canonical side list is the
proper-ancestor list followed by its selected boundary minimum. -/
theorem canonicalTopDown_eq_proper_filter_append_boundary
    {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    (childSide : Side) :
    let selection :=
      WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
        snapshot tree key
    (canonicalHeapView snapshot tree).topDown (valuePos key) childSide =
      (rootHeavyPathCanonicalChildOrder snapshot tree key.isLt rankZero).elements.filter
          (fun child => decide
            (canonicalSide snapshot tree child = childSide)) ++
        [match childSide with
          | .left => selection.left
          | .right => selection.right] := by
  let focus :=
    WholeSplayTemporaryBoundaryGeometry.KeyFocus.ofFin tree key
  let selection :=
    WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
      snapshot tree key
  have inclusiveEq :=
    rootHeavyPathChildrenWithBoundariesTopDown_eq_topDown snapshot tree
      key.isLt rankZero childSide
  have decomposed :=
    rootHeavyPathChildrenWithBoundariesTopDown_eq_proper_append_boundaryFrom
      snapshot tree (Nat.le_refl n) key focus rankZero 0 childSide
  have selectedPair :=
    WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelectionFrom_pair_eq_boundaryChildrenFrom
      snapshot tree (Nat.le_refl n) key focus
  have selectedPair' :
      (selection.left, selection.right) =
        WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryChildrenFrom
          snapshot tree (Nat.le_refl n) key focus := by
    simpa only [selection, focus,
      WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection]
      using selectedPair
  have properEq :=
    rootHeavyPathCanonicalChildOrder_filter_eq_edgeChildrenOnSide
      snapshot tree key.isLt rankZero childSide
  cases childSide with
  | left =>
      calc
        (canonicalHeapView snapshot tree).topDown (valuePos key) .left =
            rootHeavyPathChildrenWithBoundariesTopDown snapshot tree
              (Nat.le_refl n) key.val .left 0 := inclusiveEq.symm
        _ = edgeChildrenOnSide
              (rootHeavyPathEdgesTopDown snapshot tree (Nat.le_refl n)
                key.val 0) .left ++
              [(WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryChildrenFrom
                  snapshot tree (Nat.le_refl n)
                  key focus).1] := decomposed
        _ = edgeChildrenOnSide
              (rootHeavyPathEdgesTopDown snapshot tree (Nat.le_refl n)
                key.val 0) .left ++ [selection.left] := by
              rw [(congrArg Prod.fst selectedPair').symm]
        _ = (rootHeavyPathCanonicalChildOrder snapshot tree key.isLt
                rankZero).elements.filter
              (fun child => decide
                (canonicalSide snapshot tree child = .left)) ++
              [selection.left] := by rw [properEq]
  | right =>
      calc
        (canonicalHeapView snapshot tree).topDown (valuePos key) .right =
            rootHeavyPathChildrenWithBoundariesTopDown snapshot tree
              (Nat.le_refl n) key.val .right 0 := inclusiveEq.symm
        _ = edgeChildrenOnSide
              (rootHeavyPathEdgesTopDown snapshot tree (Nat.le_refl n)
                key.val 0) .right ++
              [(WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryChildrenFrom
                  snapshot tree (Nat.le_refl n)
                  key focus).2] := decomposed
        _ = edgeChildrenOnSide
              (rootHeavyPathEdgesTopDown snapshot tree (Nat.le_refl n)
                key.val 0) .right ++ [selection.right] := by
              rw [(congrArg Prod.snd selectedPair').symm]
        _ = (rootHeavyPathCanonicalChildOrder snapshot tree key.isLt
                rankZero).elements.filter
              (fun child => decide
                (canonicalSide snapshot tree child = .right)) ++
              [selection.right] := by rw [properEq]

/-- Erasing the selected boundary singleton from a canonical side leaves
exactly the proper-ancestor projection used by the pairing fraction lemma. -/
theorem proper_filter_eq_erase_boundary_canonicalTopDown
    {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    (childSide : Side) :
    let selection :=
      WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
        snapshot tree key
    let boundary := match childSide with
      | .left => selection.left
      | .right => selection.right
    (rootHeavyPathCanonicalChildOrder snapshot tree key.isLt rankZero).elements.filter
        (fun child => decide
          (canonicalSide snapshot tree child = childSide)) =
      [boundary].foldl List.erase
        ((canonicalHeapView snapshot tree).topDown (valuePos key) childSide) := by
  let selection :=
    WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
      snapshot tree key
  let boundary := match childSide with
    | .left => selection.left
    | .right => selection.right
  let proper :=
    (rootHeavyPathCanonicalChildOrder snapshot tree key.isLt rankZero).elements.filter
      (fun child => decide
        (canonicalSide snapshot tree child = childSide))
  have topEq :
      (canonicalHeapView snapshot tree).topDown (valuePos key) childSide =
        proper ++ [boundary] := by
    simpa only [selection, boundary, proper] using
      canonicalTopDown_eq_proper_filter_append_boundary
        snapshot tree key rankZero childSide
  have topNodup :=
    (canonicalHeapView snapshot tree).topDown_nodup
      (valuePos key) childSide
  rw [topEq] at topNodup
  have boundaryFresh : boundary ∉ proper := by
    have disjoint := (List.nodup_append'.mp topNodup).2.2
    simpa using disjoint
  change proper = [boundary].foldl List.erase
    ((canonicalHeapView snapshot tree).topDown (valuePos key) childSide)
  simp only [List.foldl_cons, List.foldl_nil]
  rw [topEq, List.erase_append_right [boundary] boundaryFresh]
  simp

/-- Completeness means that `attachedTopDown` removes no heap child. -/
theorem _root_.Splay.Lazy.State.Complete.attachedTopDown_eq_topDown
    {n : ℕ} {state : Lazy.State n} (complete : state.Complete)
    (owner : External n) (childSide : Side) :
    state.view.attachedTopDown state.allElements owner childSide =
      state.view.topDown owner childSide := by
  unfold HeapView.attachedTopDown
  apply List.filter_eq_self.mpr
  intro child member
  simp only [decide_eq_true_eq]
  apply (complete child).2
  have parent := (state.view.mem_topDown_iff.mp member).1
  rw [parent]
  simp

end Splay.Accounting
