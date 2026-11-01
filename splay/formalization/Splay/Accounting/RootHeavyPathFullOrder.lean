import Splay.Accounting.RootHeavyPathCells
import Splay.Accounting.CanonicalCrossSideUnbroken

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST
open Splay.Lazy.Canonical

namespace RootHeavyPathCell

/--
The manuscript's full top-down order inside one two-child ancestor cell.

On the left of the accessed value the canonical branch list already has the
outer child before the middle child.  On the right it has the reverse order,
so that cell is reversed.  Both children have the same side, hence this
choice does not affect either side-restricted `HeapView.topDown` list.
-/
def fullTopDownEdges {n : ℕ} (cell : RootHeavyPathCell n) : List (Edge n) :=
  match cell.side with
  | .left => cell.edges
  | .right => cell.edges.reverse

@[simp]
theorem length_fullTopDownEdges {n : ℕ} (cell : RootHeavyPathCell n) :
    cell.fullTopDownEdges.length = cell.edges.length := by
  cases sideEq : cell.side <;> simp [fullTopDownEdges, sideEq]

theorem fullTopDownEdges_perm_edges {n : ℕ}
    (cell : RootHeavyPathCell n) :
    cell.fullTopDownEdges.Perm cell.edges := by
  cases sideEq : cell.side with
  | left => simp [fullTopDownEdges, sideEq]
  | right => simp [fullTopDownEdges, sideEq]

/-- The same local pair as encountered by the bottom-up splay. -/
def fullBottomUpEdges {n : ℕ} (cell : RootHeavyPathCell n) : List (Edge n) :=
  cell.fullTopDownEdges.reverse

@[simp]
theorem length_fullBottomUpEdges {n : ℕ} (cell : RootHeavyPathCell n) :
    cell.fullBottomUpEdges.length = cell.edges.length := by
  simp [fullBottomUpEdges, length_fullTopDownEdges]

end RootHeavyPathCell

/-- Dropping whole fixed-size cells commutes with flattening. -/
theorem flatMap_drop_mul_of_length
    {α β : Type*} (emit : α → List β) (cells : List α) (width count : ℕ)
    (lengthEq : ∀ cell ∈ cells, (emit cell).length = width) :
    (cells.flatMap emit).drop (width * count) =
      (cells.drop count).flatMap emit := by
  induction count generalizing cells with
  | zero => simp
  | succ count ih =>
      cases cells with
      | nil => simp
      | cons cell cells =>
          have headLength := lengthEq cell (by simp)
          have tailLength :
              ∀ other ∈ cells, (emit other).length = width := by
            intro other member
            exact lengthEq other (by simp [member])
          simp [List.drop_append, headLength, Nat.mul_succ,
            ih cells tailLength]

/-- Taking whole fixed-size cells commutes with flattening. -/
theorem flatMap_take_mul_of_length
    {α β : Type*} (emit : α → List β) (cells : List α) (width count : ℕ)
    (lengthEq : ∀ cell ∈ cells, (emit cell).length = width) :
    (cells.flatMap emit).take (width * count) =
      (cells.take count).flatMap emit := by
  induction count generalizing cells with
  | zero => simp
  | succ count ih =>
      cases cells with
      | nil => simp
      | cons cell cells =>
          have headLength := lengthEq cell (by simp)
          have tailLength :
              ∀ other ∈ cells, (emit other).length = width := by
            intro other member
            exact lengthEq other (by simp [member])
          simp [List.take_append, headLength, Nat.mul_succ,
            ih cells tailLength]

/--
An item whose persistent key belongs to a selected cell slice belongs to the
flattening of that same slice.  Uniqueness of cell keys is the only incidence
fact needed here; this is the list-level bridge used below for splay endpoint
supports.
-/
theorem mem_flatMap_slice_of_key
    {α β κ : Type*} (emit : α → List β) (cellKey : α → κ)
    (itemKey : β → κ) (cells : List α) (start count : ℕ)
    (keysNodup : (cells.map cellKey).Nodup)
    (keyEq : ∀ cell ∈ cells, ∀ item ∈ emit cell,
      itemKey item = cellKey cell)
    {item : β} (allMember : item ∈ cells.flatMap emit)
    (selectedKey :
      itemKey item ∈ ((cells.drop start).take count).map cellKey) :
    item ∈ ((cells.drop start).take count).flatMap emit := by
  obtain ⟨source, sourceMember, itemMember⟩ :=
    List.mem_flatMap.mp allMember
  obtain ⟨target, targetSliceMember, targetKeyEq⟩ :=
    List.mem_map.mp selectedKey
  have targetMember : target ∈ cells :=
    (List.take_sublist count (cells.drop start)).trans
      (List.drop_sublist start cells) |>.mem targetSliceMember
  have sourceKeyEq := keyEq source sourceMember item itemMember
  have sourceEqTarget : source = target :=
    List.inj_on_of_nodup_map keysNodup sourceMember targetMember
      (sourceKeyEq.symm.trans targetKeyEq.symm)
  subst target
  exact List.mem_flatMap.mpr ⟨source, targetSliceMember, itemMember⟩

/-- The rank-zero accessed value selects the search branch as heavy. -/
theorem heavyBranch_eq_searchBranch {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n) (key : ℕ)
    (insideLower : node.lower ≤ key) (insideUpper : key < node.upper)
    (notRoot : key ≠ node.root) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    node.heavyBranch snapshot =
      if key < node.root then .left else .right := by
  let accessed : External n := valuePos ⟨key, key_lt_n⟩
  have insideWhole :
      node.wholeLower ≤ accessed ∧ accessed ≤ node.wholeUpper := by
    change 2 * node.lower ≤ 2 * key + 1 ∧
      2 * key + 1 ≤ 2 * node.upper
    omega
  by_cases inLeft : key < node.root
  · rw [if_pos inLeft]
    apply node.heavyBranch_eq_of_rank_eq_zero
      snapshot .left accessed (by simpa only [accessed] using rankZero)
      insideWhole
    change 2 * key + 1 ≤ 2 * node.root
    omega
  · have rootLtKey : node.root < key := by omega
    rw [if_neg inLeft]
    apply node.heavyBranch_eq_of_rank_eq_zero
      snapshot .right accessed (by simpa only [accessed] using rankZero)
      insideWhole
    change 2 * node.root + 2 ≤ 2 * key + 1
    omega

/-- The two locally ordered edges are strictly top-down ordered. -/
theorem rootHeavyPathCellAt_fullTopDownEdges_pairwise
    {n : ℕ} (snapshot : Snapshot n) (node : AtNode n)
    (depth key : ℕ)
    (insideLower : node.lower ≤ key) (insideUpper : key < node.upper)
    (notRoot : key ≠ node.root) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    (rootHeavyPathCellAt snapshot node depth key).fullTopDownEdges.Pairwise
      edgeStrictlyAbove := by
  have heavy := heavyBranch_eq_searchBranch snapshot node key
    insideLower insideUpper notRoot key_lt_n rankZero
  by_cases inLeft : key < node.root
  · rw [if_pos inLeft] at heavy
    simp [RootHeavyPathCell.fullTopDownEdges, rootHeavyPathCellAt,
      hitSide, show ¬node.root < key by omega, edgesAtNode,
      lightBranches, allBranches, heavy,
      edgeStrictlyAbove, edgeFor]
  · have rootLtKey : node.root < key := by omega
    rw [if_neg inLeft] at heavy
    simp [RootHeavyPathCell.fullTopDownEdges, rootHeavyPathCellAt,
      hitSide, rootLtKey, edgesAtNode, lightBranches, allBranches, heavy,
      edgeStrictlyAbove, edgeFor]

/-- Every edge in the local cell records the local structural depth. -/
theorem rootHeavyPathCellAt_fullTopDownEdges_attachmentDepth
    {n : ℕ} (snapshot : Snapshot n) (node : AtNode n)
    (depth key : ℕ) {edge : Edge n}
    (member :
      edge ∈
        (rootHeavyPathCellAt snapshot node depth key).fullTopDownEdges) :
    edge.attachmentDepth = depth := by
  have rawMember :
      edge ∈ (rootHeavyPathCellAt snapshot node depth key).edges :=
    (rootHeavyPathCellAt snapshot node depth key).fullTopDownEdges_perm_edges
      |>.mem_iff.mp member
  exact
    (mem_edgesAtNode_valid snapshot node depth (by
      simpa only [rootHeavyPathCellAt] using rawMember)).2.2.2.2.2.1

/-- All proper-ancestor light edges in manuscript full top-down order. -/
noncomputable def rootHeavyPathEdgesTopDown {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (key : ℕ) (depth : ℕ := 0) :
    List (Edge n) :=
  (rootHeavyPathCellsTopDown snapshot tree upper_le_n key depth).flatMap
    RootHeavyPathCell.fullTopDownEdges

/-- The same hit heap children in chronological bottom-up splay order. -/
noncomputable def rootHeavyPathEdgesBottomUp {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (key : ℕ) (depth : ℕ := 0) :
    List (Edge n) :=
  (rootHeavyPathEdgesTopDown snapshot tree upper_le_n key depth).reverse

noncomputable def rootHeavyPathChildrenTopDown {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (key : ℕ) (depth : ℕ := 0) :
    List (External n) :=
  (rootHeavyPathEdgesTopDown snapshot tree upper_le_n key depth).map Edge.child

noncomputable def rootHeavyPathChildrenBottomUp {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (key : ℕ) (depth : ℕ := 0) :
    List (External n) :=
  (rootHeavyPathEdgesBottomUp snapshot tree upper_le_n key depth).map Edge.child

/-- Descending left appends the current cell after the child's bottom-up list. -/
theorem rootHeavyPathChildrenBottomUp_leftContext
    {n lower root upper key : ℕ} (snapshot : Snapshot n)
    (left : BST lower root) (right : BST (root + 1) upper)
    (upper_le_n : upper ≤ n) (keyLt : key < root) (depth : ℕ) :
    rootHeavyPathChildrenBottomUp snapshot (.node left right) upper_le_n
        key depth =
      rootHeavyPathChildrenBottomUp snapshot left (by
        have := right.lower_le_upper
        omega) key (depth + 1) ++
      (rootHeavyPathCellAt snapshot {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      } depth key).fullBottomUpEdges.map Edge.child := by
  have notRoot : key ≠ root := by omega
  simp [rootHeavyPathChildrenBottomUp, rootHeavyPathEdgesBottomUp,
    rootHeavyPathEdgesTopDown, rootHeavyPathCellsTopDown, notRoot, keyLt,
    RootHeavyPathCell.fullBottomUpEdges, List.reverse_append,
    List.map_append]

/-- Descending right appends the current cell after the child's bottom-up list. -/
theorem rootHeavyPathChildrenBottomUp_rightContext
    {n lower root upper key : ℕ} (snapshot : Snapshot n)
    (left : BST lower root) (right : BST (root + 1) upper)
    (upper_le_n : upper ≤ n) (rootLt : root < key) (depth : ℕ) :
    rootHeavyPathChildrenBottomUp snapshot (.node left right) upper_le_n
        key depth =
      rootHeavyPathChildrenBottomUp snapshot right upper_le_n key
          (depth + 1) ++
      (rootHeavyPathCellAt snapshot {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      } depth key).fullBottomUpEdges.map Edge.child := by
  have notRoot : key ≠ root := by omega
  have notLeft : ¬ key < root := by omega
  simp [rootHeavyPathChildrenBottomUp, rootHeavyPathEdgesBottomUp,
    rootHeavyPathEdgesTopDown, rootHeavyPathCellsTopDown, notRoot, notLeft,
    RootHeavyPathCell.fullBottomUpEdges, List.reverse_append,
    List.map_append]

/-- Rotating farther down the searched left branch does not change the two
light children emitted by the enclosing cell. -/
theorem rootHeavyPathCellAt_children_eq_of_left_change
    {n lower root upper key : ℕ} (snapshot : Snapshot n)
    (before after : BST lower root) (right : BST (root + 1) upper)
    (upper_le_n : upper ≤ n) (keyLower : lower ≤ key)
    (keyLt : key < root) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (depth : ℕ) :
    (rootHeavyPathCellAt snapshot {
      lower := lower
      root := root
      upper := upper
      left := before
      right := right
      upper_le_n := upper_le_n
    } depth key).fullBottomUpEdges.map Edge.child =
    (rootHeavyPathCellAt snapshot {
      lower := lower
      root := root
      upper := upper
      left := after
      right := right
      upper_le_n := upper_le_n
    } depth key).fullBottomUpEdges.map Edge.child := by
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
  have insideUpper : key < upper := by
    have := right.lower_le_upper
    omega
  have notRoot : key ≠ root := by omega
  have notRootLt : ¬ root < key := by omega
  have beforeHeavy := heavyBranch_eq_searchBranch snapshot beforeNode key
    keyLower insideUpper notRoot key_lt_n rankZero
  have afterHeavy := heavyBranch_eq_searchBranch snapshot afterNode key
    keyLower insideUpper notRoot key_lt_n rankZero
  have middleEq : beforeNode.branchMin snapshot .middle =
      afterNode.branchMin snapshot .middle := by rfl
  have rightEq : beforeNode.branchMin snapshot .right =
      afterNode.branchMin snapshot .right := by rfl
  simp [RootHeavyPathCell.fullBottomUpEdges,
    RootHeavyPathCell.fullTopDownEdges, rootHeavyPathCellAt, edgesAtNode,
    lightBranches, allBranches, hitSide, beforeNode, afterNode,
    beforeHeavy, afterHeavy, middleEq, rightEq, keyLt, notRootLt, edgeFor]

/-- The mirror image: changing the searched right branch leaves the enclosing
cell's two emitted light children unchanged. -/
theorem rootHeavyPathCellAt_children_eq_of_right_change
    {n lower root upper key : ℕ} (snapshot : Snapshot n)
    (left : BST lower root) (before after : BST (root + 1) upper)
    (upper_le_n : upper ≤ n) (rootLt : root < key)
    (keyUpper : key < upper) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (depth : ℕ) :
    (rootHeavyPathCellAt snapshot {
      lower := lower
      root := root
      upper := upper
      left := left
      right := before
      upper_le_n := upper_le_n
    } depth key).fullBottomUpEdges.map Edge.child =
    (rootHeavyPathCellAt snapshot {
      lower := lower
      root := root
      upper := upper
      left := left
      right := after
      upper_le_n := upper_le_n
    } depth key).fullBottomUpEdges.map Edge.child := by
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
  have insideLower : lower ≤ key := by
    have := left.lower_le_upper
    omega
  have notRoot : key ≠ root := by omega
  have notKeyLt : ¬ key < root := by omega
  have beforeHeavy := heavyBranch_eq_searchBranch snapshot beforeNode key
    insideLower keyUpper notRoot key_lt_n rankZero
  have afterHeavy := heavyBranch_eq_searchBranch snapshot afterNode key
    insideLower keyUpper notRoot key_lt_n rankZero
  have leftEq : beforeNode.branchMin snapshot .left =
      afterNode.branchMin snapshot .left := by rfl
  have middleEq : beforeNode.branchMin snapshot .middle =
      afterNode.branchMin snapshot .middle := by rfl
  simp [RootHeavyPathCell.fullBottomUpEdges,
    RootHeavyPathCell.fullTopDownEdges, rootHeavyPathCellAt, edgesAtNode,
    lightBranches, allBranches, hitSide, beforeNode, afterNode,
    beforeHeavy, afterHeavy, leftEq, middleEq, rootLt, notKeyLt, edgeFor]

/-- Once the accessed key is at the root there are no proper-ancestor cells. -/
theorem rootHeavyPathChildrenBottomUp_eq_nil_of_hasRoot
    {n lower upper key : ℕ} (snapshot : Snapshot n)
    {tree : BST lower upper} (upper_le_n : upper ≤ n)
    (root : tree.HasRoot key) (depth : ℕ) :
    rootHeavyPathChildrenBottomUp snapshot tree upper_le_n key depth = [] := by
  obtain ⟨left, right, rfl⟩ := root
  simp [rootHeavyPathChildrenBottomUp, rootHeavyPathEdgesBottomUp,
    rootHeavyPathEdgesTopDown, rootHeavyPathCellsTopDown]

/-- Bottom-up edges are the reversed local cells in bottom-up cell order. -/
theorem rootHeavyPathEdgesBottomUp_eq_flatMap_fullBottomUpEdges
    {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (key depth : ℕ) :
    rootHeavyPathEdgesBottomUp snapshot tree upper_le_n key depth =
      (rootHeavyPathCellsBottomUp snapshot tree upper_le_n key depth).flatMap
        RootHeavyPathCell.fullBottomUpEdges := by
  unfold rootHeavyPathEdgesBottomUp rootHeavyPathEdgesTopDown
    rootHeavyPathCellsBottomUp RootHeavyPathCell.fullBottomUpEdges
  rw [List.reverse_flatMap]
  rfl

/-- The analogous cell decomposition of the bottom-up child list. -/
theorem rootHeavyPathChildrenBottomUp_eq_flatMap_fullBottomUpEdges
    {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (key depth : ℕ) :
    rootHeavyPathChildrenBottomUp snapshot tree upper_le_n key depth =
      (rootHeavyPathCellsBottomUp snapshot tree upper_le_n key depth).flatMap
        (fun cell => cell.fullBottomUpEdges.map Edge.child) := by
  rw [rootHeavyPathChildrenBottomUp]
  rw [rootHeavyPathEdgesBottomUp_eq_flatMap_fullBottomUpEdges]
  exact List.map_flatMap

/-- The bottom-up list contains two heap children per proper search ancestor. -/
theorem rootHeavyPathChildrenBottomUp_length_eq_two_mul_depth
    {n lower upper key : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (insideLower : lower ≤ key) (insideUpper : key < upper)
    (depth : ℕ) :
    (rootHeavyPathChildrenBottomUp snapshot tree upper_le_n key depth).length =
      2 * tree.depth key := by
  let cells := rootHeavyPathCellsBottomUp snapshot tree upper_le_n key depth
  let emit : RootHeavyPathCell n → List (External n) :=
    fun cell => cell.fullBottomUpEdges.map Edge.child
  have emitLength : ∀ cell ∈ cells, (emit cell).length = 2 := by
    intro cell member
    have raw := rootHeavyPathCellsBottomUp_forall_children_length_two
      snapshot tree upper_le_n key depth cell member
    simpa [emit, RootHeavyPathCell.children] using raw
  have flatLength : (cells.flatMap emit).length = 2 * cells.length := by
    rw [List.length_flatMap]
    have mapEq : cells.map (fun cell => (emit cell).length) =
        cells.map (fun _ => 2) := by
      exact List.map_congr_left fun cell member => emitLength cell member
    rw [mapEq]
    simp [Nat.mul_comm]
  rw [rootHeavyPathChildrenBottomUp_eq_flatMap_fullBottomUpEdges]
  change (cells.flatMap emit).length = _
  rw [flatLength]
  have keys := map_attachmentKey_rootHeavyPathCellsBottomUp
    snapshot tree upper_le_n insideLower insideUpper depth
  have cellsLength : cells.length = tree.depth key := by
    have lengths := congrArg List.length keys
    rw [List.length_reverse, List.length_dropLast,
      _root_.Splay.Tree.BST.searchPath.length_eq_depth_add_one tree
        insideLower insideUpper] at lengths
    simpa [cells] using lengths
  rw [cellsLength]

namespace DoubleRotationAt

/-- A double splay step removes exactly the first four children from the
chronological root-heavy-path list; all enclosing light-child cells retain
their exact order. -/
theorem rootHeavyPathChildrenBottomUp_decompose
    {n depth key lower upper : ℕ} (snapshot : Snapshot n)
    {before after : BST lower upper}
    (step : DoubleRotationAt depth key before after)
    (upper_le_n : upper ≤ n) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (startDepth : ℕ) :
    ∃ chunk : List (External n),
      chunk.length = 4 ∧
        rootHeavyPathChildrenBottomUp snapshot before upper_le_n key
            startDepth =
          chunk ++ rootHeavyPathChildrenBottomUp snapshot after upper_le_n key
            startDepth := by
  induction step generalizing startDepth with
  | @root key lower upper before after localStep =>
      let chunk := rootHeavyPathChildrenBottomUp snapshot before upper_le_n key
        startDepth
      refine ⟨chunk, ?_, ?_⟩
      · rw [rootHeavyPathChildrenBottomUp_length_eq_two_mul_depth
          snapshot _ upper_le_n localStep.key_bounds.1
            localStep.key_bounds.2 startDepth,
          localStep.depth_before_eq_two]
      · rw [rootHeavyPathChildrenBottomUp_eq_nil_of_hasRoot
          snapshot upper_le_n localStep.hasRoot_after startDepth]
        simp [chunk]
  | @leftContext depth key lower root upper before after step right ih =>
      have childUpper : root ≤ n := by
        have := right.lower_le_upper
        omega
      obtain ⟨chunk, chunkLength, childEq⟩ :=
        ih childUpper key_lt_n rankZero (startDepth + 1)
      refine ⟨chunk, chunkLength, ?_⟩
      rw [rootHeavyPathChildrenBottomUp_leftContext snapshot before right
          upper_le_n step.key_bounds.2 startDepth,
        rootHeavyPathChildrenBottomUp_leftContext snapshot after right
          upper_le_n step.key_bounds.2 startDepth,
        childEq]
      rw [rootHeavyPathCellAt_children_eq_of_left_change snapshot before after
        right upper_le_n step.key_bounds.1 step.key_bounds.2 key_lt_n
        rankZero startDepth]
      simp [List.append_assoc]
  | @rightContext depth key lower root upper left before after step ih =>
      obtain ⟨chunk, chunkLength, childEq⟩ :=
        ih upper_le_n key_lt_n rankZero (startDepth + 1)
      have rootLt : root < key := by
        have bounds := step.key_bounds
        omega
      refine ⟨chunk, chunkLength, ?_⟩
      rw [rootHeavyPathChildrenBottomUp_rightContext snapshot left before
          upper_le_n rootLt startDepth,
        rootHeavyPathChildrenBottomUp_rightContext snapshot left after
          upper_le_n rootLt startDepth,
        childEq]
      rw [rootHeavyPathCellAt_children_eq_of_right_change snapshot left before
        after upper_le_n rootLt step.key_bounds.2 key_lt_n rankZero
        startDepth]
      simp [List.append_assoc]

end DoubleRotationAt

/--
Two consecutive hit cells are exactly the corresponding four-child group in
the chronological bottom-up child list.
-/
theorem rootHeavyPathChildrenBottomUp_groupChunk
    {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (key depth group : ℕ) :
    ((rootHeavyPathChildrenBottomUp snapshot tree upper_le_n key depth).drop
        (4 * group)).take 4 =
      (((rootHeavyPathCellsBottomUp snapshot tree upper_le_n key depth).drop
        (2 * group)).take 2).flatMap
          (fun cell => cell.fullBottomUpEdges.map Edge.child) := by
  let cells :=
    rootHeavyPathCellsBottomUp snapshot tree upper_le_n key depth
  let emit : RootHeavyPathCell n → List (External n) :=
    fun cell => cell.fullBottomUpEdges.map Edge.child
  have emitLength : ∀ cell ∈ cells, (emit cell).length = 2 := by
    intro cell cellMember
    have childrenLength :=
      rootHeavyPathCellsBottomUp_forall_children_length_two
        snapshot tree upper_le_n key depth cell cellMember
    simpa [emit, RootHeavyPathCell.children] using childrenLength
  have droppedLength :
      ∀ cell ∈ cells.drop (2 * group), (emit cell).length = 2 := by
    intro cell cellMember
    exact emitLength cell
      ((List.drop_sublist (2 * group) cells).mem cellMember)
  rw [rootHeavyPathChildrenBottomUp_eq_flatMap_fullBottomUpEdges]
  change ((cells.flatMap emit).drop (4 * group)).take 4 = _
  rw [show 4 * group = 2 * (2 * group) by omega,
    flatMap_drop_mul_of_length emit cells 2 (2 * group) emitLength]
  rw [show 4 = 2 * 2 by omega,
    flatMap_take_mul_of_length emit (cells.drop (2 * group)) 2 2
      droppedLength]

/-- Every later proper-ancestor cell is attached at least at the current depth. -/
theorem rootHeavyPathEdgesTopDown_attachmentDepth_ge
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key depth : ℕ) :
    ∀ edge ∈ rootHeavyPathEdgesTopDown snapshot tree upper_le_n key depth,
      depth ≤ edge.attachmentDepth := by
  induction tree generalizing depth with
  | empty =>
      simp [rootHeavyPathEdgesTopDown, rootHeavyPathCellsTopDown]
  | @node lower root upper left right ihLeft ihRight =>
      by_cases atRoot : key = root
      · simp [rootHeavyPathEdgesTopDown, rootHeavyPathCellsTopDown, atRoot]
      · by_cases inLeft : key < root
        · intro edge member
          have listEq :
              rootHeavyPathEdgesTopDown snapshot (.node left right)
                  upper_le_n key depth =
                (rootHeavyPathCellAt snapshot {
              lower := lower
              root := root
              upper := upper
              left := left
              right := right
              upper_le_n := upper_le_n
            } depth key).fullTopDownEdges ++
              rootHeavyPathEdgesTopDown snapshot left (by
                have := right.lower_le_upper
                omega) key (depth + 1) := by
            simp [rootHeavyPathEdgesTopDown, rootHeavyPathCellsTopDown,
              atRoot, inLeft]
          rw [listEq] at member
          rcases List.mem_append.mp member with localMember | childMember
          · rw [rootHeavyPathCellAt_fullTopDownEdges_attachmentDepth
                snapshot _ depth key localMember]
          · have childDepth := ihLeft (by
                have := right.lower_le_upper
                omega) (depth + 1) edge childMember
            omega
        · intro edge member
          have listEq :
              rootHeavyPathEdgesTopDown snapshot (.node left right)
                  upper_le_n key depth =
                (rootHeavyPathCellAt snapshot {
              lower := lower
              root := root
              upper := upper
              left := left
              right := right
              upper_le_n := upper_le_n
            } depth key).fullTopDownEdges ++
              rootHeavyPathEdgesTopDown snapshot right upper_le_n key
                (depth + 1) := by
            simp [rootHeavyPathEdgesTopDown, rootHeavyPathCellsTopDown,
              atRoot, inLeft]
          rw [listEq] at member
          rcases List.mem_append.mp member with localMember | childMember
          · rw [rootHeavyPathCellAt_fullTopDownEdges_attachmentDepth
                snapshot _ depth key localMember]
          · have childDepth :=
              ihRight upper_le_n (depth + 1) edge childMember
            omega

/--
The proper-ancestor edges are pairwise ordered by the manuscript's strict
full top-down attachment order.  The cross-cell case follows solely from
structural depth; the only same-depth comparison is the local outer-before-
middle convention.
-/
theorem rootHeavyPathEdgesTopDown_pairwise
    {n lower upper key : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (insideLower : lower ≤ key) (insideUpper : key < upper)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (depth : ℕ) :
    (rootHeavyPathEdgesTopDown snapshot tree upper_le_n key depth).Pairwise
      edgeStrictlyAbove := by
  induction tree generalizing depth with
  | empty boundary =>
      omega
  | @node lower root upper left right ihLeft ihRight =>
      by_cases atRoot : key = root
      · simp [rootHeavyPathEdgesTopDown, rootHeavyPathCellsTopDown, atRoot]
      · let node : AtNode n := {
          lower := lower
          root := root
          upper := upper
          left := left
          right := right
          upper_le_n := upper_le_n
        }
        have localPairwise :
            (rootHeavyPathCellAt snapshot node depth key).fullTopDownEdges.Pairwise
              edgeStrictlyAbove :=
          rootHeavyPathCellAt_fullTopDownEdges_pairwise snapshot node depth key
            insideLower insideUpper atRoot key_lt_n rankZero
        by_cases inLeft : key < root
        · have childUpper : root ≤ n := by
            have := right.lower_le_upper
            omega
          have childPairwise := ihLeft childUpper insideLower inLeft
            (depth + 1)
          have across :
              ∀ first ∈
                  (rootHeavyPathCellAt snapshot node depth key).fullTopDownEdges,
                ∀ second ∈
                  rootHeavyPathEdgesTopDown snapshot left childUpper key
                    (depth + 1),
                  edgeStrictlyAbove first second := by
            intro first firstMember second secondMember
            have firstDepth :=
              rootHeavyPathCellAt_fullTopDownEdges_attachmentDepth
                snapshot node depth key firstMember
            have secondDepth :=
              rootHeavyPathEdgesTopDown_attachmentDepth_ge
                snapshot left childUpper key (depth + 1) second secondMember
            unfold edgeStrictlyAbove
            left
            omega
          have combined := List.pairwise_append.mpr
            ⟨localPairwise, childPairwise, across⟩
          simpa [rootHeavyPathEdgesTopDown, rootHeavyPathCellsTopDown,
            atRoot, inLeft, node] using combined
        · have rootLtKey : root < key := by omega
          have childPairwise := ihRight upper_le_n (by omega) insideUpper
            (depth + 1)
          have across :
              ∀ first ∈
                  (rootHeavyPathCellAt snapshot node depth key).fullTopDownEdges,
                ∀ second ∈
                  rootHeavyPathEdgesTopDown snapshot right upper_le_n key
                    (depth + 1),
                  edgeStrictlyAbove first second := by
            intro first firstMember second secondMember
            have firstDepth :=
              rootHeavyPathCellAt_fullTopDownEdges_attachmentDepth
                snapshot node depth key firstMember
            have secondDepth :=
              rootHeavyPathEdgesTopDown_attachmentDepth_ge
                snapshot right upper_le_n key (depth + 1) second secondMember
            unfold edgeStrictlyAbove
            left
            omega
          have combined := List.pairwise_append.mpr
            ⟨localPairwise, childPairwise, across⟩
          simpa [rootHeavyPathEdgesTopDown, rootHeavyPathCellsTopDown,
            atRoot, inLeft, node] using combined

/-- Reordering each two-edge cell preserves the raw canonical edge multiset. -/
theorem rootHeavyPathEdgesTopDown_perm_rawCells
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key depth : ℕ) :
    (rootHeavyPathEdgesTopDown snapshot tree upper_le_n key depth).Perm
      ((rootHeavyPathCellsTopDown snapshot tree upper_le_n key depth).flatMap
        RootHeavyPathCell.edges) := by
  exact List.Perm.flatMap_left _ fun cell _ =>
    cell.fullTopDownEdges_perm_edges

/-- Raw proper-search-path cells form a sublist of all canonical tree edges. -/
theorem rawRootHeavyPathEdgesTopDown_sublist_treeEdges
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key depth : ℕ) :
    ((rootHeavyPathCellsTopDown snapshot tree upper_le_n key depth).flatMap
        RootHeavyPathCell.edges).Sublist
      (treeEdges snapshot tree upper_le_n depth) := by
  induction tree generalizing depth with
  | empty =>
      simp [rootHeavyPathCellsTopDown, treeEdges]
  | @node lower root upper left right ihLeft ihRight =>
      by_cases atRoot : key = root
      · simp [rootHeavyPathCellsTopDown, treeEdges, atRoot]
      · by_cases inLeft : key < root
        · let localEdges := edgesAtNode snapshot {
            lower := lower
            root := root
            upper := upper
            left := left
            right := right
            upper_le_n := upper_le_n
          } depth
          let leftEdges := treeEdges snapshot left (by
            have := right.lower_le_upper
            omega) (depth + 1)
          let rightEdges := treeEdges snapshot right upper_le_n (depth + 1)
          have child := ihLeft (by
            have := right.lower_le_upper
            omega) (depth + 1)
          have prefixProof :
              (localEdges ++
                (rootHeavyPathCellsTopDown snapshot left (by
                  have := right.lower_le_upper
                  omega) key (depth + 1)).flatMap
                    RootHeavyPathCell.edges).Sublist
                (localEdges ++ leftEdges) :=
            (List.Sublist.refl localEdges).append child
          have withRight :
              (localEdges ++ leftEdges).Sublist
                (localEdges ++ leftEdges ++ rightEdges) :=
            List.sublist_append_left _ _
          simpa [treeEdges, rootHeavyPathCellAt, localEdges, leftEdges,
            rightEdges, rootHeavyPathCellsTopDown, atRoot, inLeft,
            List.flatMap_cons] using
            prefixProof.trans withRight
        · let localEdges := edgesAtNode snapshot {
            lower := lower
            root := root
            upper := upper
            left := left
            right := right
            upper_le_n := upper_le_n
          } depth
          let leftEdges := treeEdges snapshot left (by
            have := right.lower_le_upper
            omega) (depth + 1)
          let rightEdges := treeEdges snapshot right upper_le_n (depth + 1)
          have child := ihRight upper_le_n (depth + 1)
          have childWithLeft :
              ((rootHeavyPathCellsTopDown snapshot right upper_le_n key
                    (depth + 1)).flatMap RootHeavyPathCell.edges).Sublist
                (leftEdges ++ rightEdges) :=
            child.trans (List.sublist_append_right leftEdges rightEdges)
          have full :
              (localEdges ++
                (rootHeavyPathCellsTopDown snapshot right upper_le_n key
                    (depth + 1)).flatMap RootHeavyPathCell.edges).Sublist
                (localEdges ++ (leftEdges ++ rightEdges)) :=
            (List.Sublist.refl localEdges).append childWithLeft
          simpa [treeEdges, rootHeavyPathCellAt, localEdges, leftEdges,
            rightEdges, List.append_assoc, rootHeavyPathCellsTopDown, atRoot,
            inLeft, List.flatMap_cons] using full

/--
Conversely, every canonical edge attached at a proper search ancestor occurs
in the corresponding root-heavy-path cell.  Together with the preceding
sublist theorem this characterizes exactly the edge universe hit by a splay.
-/
theorem mem_rawRootHeavyPathEdgesTopDown_of_attachment_properAncestor
    {n lower upper key : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (insideLower : lower ≤ key) (insideUpper : key < upper)
    (depth : ℕ) {edge : Edge n}
    (treeMember : edge ∈ treeEdges snapshot tree upper_le_n depth)
    (attachment :
      edge.attachmentKey ∈ (tree.searchPath key).dropLast.reverse) :
    edge ∈
      (rootHeavyPathCellsTopDown snapshot tree upper_le_n key depth).flatMap
        RootHeavyPathCell.edges := by
  induction tree generalizing depth with
  | empty boundary =>
      omega
  | @node lower root upper left right ihLeft ihRight =>
      by_cases atRoot : key = root
      · subst key
        simp [_root_.Splay.Tree.BST.searchPath] at attachment
      · by_cases inLeft : key < root
        · have childUpper : root ≤ n := by
            have := right.lower_le_upper
            omega
          have properEq :=
            searchPath.properAncestors_leftContext left right
              insideLower inLeft
          rw [properEq] at attachment
          simp only [List.mem_append, List.mem_singleton] at attachment
          simp only [treeEdges, List.mem_append] at treeMember
          have result :
              edge ∈ edgesAtNode snapshot {
                  lower := lower
                  root := root
                  upper := upper
                  left := left
                  right := right
                  upper_le_n := upper_le_n
                } depth ∨
                edge ∈
                  (rootHeavyPathCellsTopDown snapshot left childUpper key
                    (depth + 1)).flatMap RootHeavyPathCell.edges := by
            rcases attachment with childAttachment | rootAttachment
            · have childBounds :=
                searchPath.mem_bounds_of_mem_properAncestors left
                  insideLower inLeft childAttachment
              rcases treeMember with (localMember | leftMember) | rightMember
              · have localKey :=
                  mem_edgesAtNode_attachmentKey snapshot _ depth localMember
                change edge.attachmentKey = root at localKey
                right
                omega
              · exact Or.inr
                  (ihLeft childUpper insideLower inLeft (depth + 1)
                    leftMember childAttachment)
              · have rightBounds :=
                  mem_treeEdges_attachmentKey_bounds snapshot right upper_le_n
                    rightMember
                omega
            · rcases treeMember with (localMember | leftMember) | rightMember
              · exact Or.inl localMember
              · have leftBounds :=
                  mem_treeEdges_attachmentKey_bounds snapshot left childUpper
                    leftMember
                omega
              · have rightBounds :=
                  mem_treeEdges_attachmentKey_bounds snapshot right upper_le_n
                    rightMember
                omega
          simpa [rootHeavyPathCellsTopDown, atRoot, inLeft,
            rootHeavyPathCellAt] using result
        · have rootLtKey : root < key := by omega
          have properEq :=
            searchPath.properAncestors_rightContext left right
              rootLtKey insideUpper
          rw [properEq] at attachment
          simp only [List.mem_append, List.mem_singleton] at attachment
          simp only [treeEdges, List.mem_append] at treeMember
          have result :
              edge ∈ edgesAtNode snapshot {
                  lower := lower
                  root := root
                  upper := upper
                  left := left
                  right := right
                  upper_le_n := upper_le_n
                } depth ∨
                edge ∈
                  (rootHeavyPathCellsTopDown snapshot right upper_le_n key
                    (depth + 1)).flatMap RootHeavyPathCell.edges := by
            rcases attachment with childAttachment | rootAttachment
            · have childBounds :=
                searchPath.mem_bounds_of_mem_properAncestors right
                  (by omega) insideUpper childAttachment
              rcases treeMember with (localMember | leftMember) | rightMember
              · have localKey :=
                  mem_edgesAtNode_attachmentKey snapshot _ depth localMember
                change edge.attachmentKey = root at localKey
                right
                omega
              · have leftBounds :=
                  mem_treeEdges_attachmentKey_bounds snapshot left (by omega)
                    leftMember
                omega
              · exact Or.inr
                  (ihRight upper_le_n (by omega) insideUpper (depth + 1)
                    rightMember childAttachment)
            · rcases treeMember with (localMember | leftMember) | rightMember
              · exact Or.inl localMember
              · have leftBounds :=
                  mem_treeEdges_attachmentKey_bounds snapshot left (by omega)
                    leftMember
                omega
              · have rightBounds :=
                  mem_treeEdges_attachmentKey_bounds snapshot right upper_le_n
                    rightMember
                omega
          simpa [rootHeavyPathCellsTopDown, atRoot, inLeft,
            rootHeavyPathCellAt] using result

/-- The manuscript-ordered hit-child list has no repetitions. -/
theorem rootHeavyPathChildrenTopDown_nodup
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key depth : ℕ) :
    (rootHeavyPathChildrenTopDown snapshot tree upper_le_n key depth).Nodup := by
  have rawSublist :=
    (rawRootHeavyPathEdgesTopDown_sublist_treeEdges
      snapshot tree upper_le_n key depth).map Edge.child
  have rawNodup :
      (((rootHeavyPathCellsTopDown snapshot tree upper_le_n key depth).flatMap
        RootHeavyPathCell.edges).map Edge.child).Nodup := by
    apply rawSublist.nodup
    simpa only [treeChildren] using
      treeChildren_nodup snapshot tree upper_le_n depth
  have childPerm :=
    (rootHeavyPathEdgesTopDown_perm_rawCells
      snapshot tree upper_le_n key depth).map Edge.child
  exact childPerm.symm.nodup (by
    simpa only [rootHeavyPathChildrenTopDown] using rawNodup)

/-- Reversing to chronological splay order preserves uniqueness. -/
theorem rootHeavyPathChildrenBottomUp_nodup
    {n key : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) :
    (rootHeavyPathChildrenBottomUp snapshot tree (Nat.le_refl n) key 0).Nodup := by
  have top := rootHeavyPathChildrenTopDown_nodup snapshot tree
    (Nat.le_refl n) key 0
  simpa [rootHeavyPathChildrenBottomUp, rootHeavyPathEdgesBottomUp,
    rootHeavyPathChildrenTopDown, List.map_reverse] using
      (List.nodup_reverse.mpr top)

/-- Every ordered proper-ancestor edge is an edge of the full canonical tree. -/
theorem rootHeavyPathEdgesTopDown_mem_fullEdges
    {n key : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    {edge : Edge n}
    (member :
      edge ∈ rootHeavyPathEdgesTopDown snapshot tree (Nat.le_refl n) key 0) :
    edge ∈ fullEdges snapshot tree := by
  have rawMember :
      edge ∈
        (rootHeavyPathCellsTopDown snapshot tree (Nat.le_refl n) key 0).flatMap
          RootHeavyPathCell.edges :=
    (rootHeavyPathEdgesTopDown_perm_rawCells
      snapshot tree (Nat.le_refl n) key 0).mem_iff.mp member
  have treeMember :=
    (rawRootHeavyPathEdgesTopDown_sublist_treeEdges
      snapshot tree (Nat.le_refl n) key 0).mem rawMember
  simpa only [fullEdges] using treeMember

/-- A listed full edge is exactly the result of its child's incoming lookup. -/
theorem incomingEdge?_eq_edge_of_mem_fullEdges
    {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    {edge : Edge n} (member : edge ∈ fullEdges snapshot tree) :
    incomingEdge? snapshot tree edge.child = some edge := by
  have rankLt : snapshot.rank edge.owner < snapshot.rank edge.child :=
    mem_treeEdges_rank_lt snapshot tree (Nat.le_refl n)
      (by simpa only [fullEdges] using member)
  have notRoot : edge.child ≠ canonicalRoot snapshot tree := by
    intro childEq
    rw [childEq, rank_canonicalRoot_eq_zero] at rankLt
    omega
  obtain ⟨incoming, lookup, incomingMember, incomingChild⟩ :=
    exists_incomingEdge?_eq_some_of_ne_root snapshot tree notRoot
  obtain ⟨selected, _, selectedUnique⟩ :=
    existsUnique_fullEdge_child_of_ne_root
      snapshot tree edge.child notRoot
  have incomingEq : incoming = selected :=
    selectedUnique incoming ⟨incomingMember, incomingChild⟩
  have edgeEq : edge = selected :=
    selectedUnique edge ⟨member, rfl⟩
  simpa only [incomingEq, edgeEq] using lookup

/-- Every proper-ancestor cell edge is owned by the accessed rank-zero value. -/
theorem rootHeavyPathEdgesTopDown_owner_eq_accessed
    {n lower upper key : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (insideLower : lower ≤ key) (insideUpper : key < upper)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (depth : ℕ) :
    ∀ edge ∈ rootHeavyPathEdgesTopDown snapshot tree upper_le_n key depth,
      edge.owner = valuePos ⟨key, key_lt_n⟩ := by
  intro edge member
  change edge ∈
    (rootHeavyPathCellsTopDown snapshot tree upper_le_n key depth).flatMap
      RootHeavyPathCell.fullTopDownEdges at member
  obtain ⟨cell, cellMember, edgeMember⟩ := List.mem_flatMap.mp member
  have rawMember : edge ∈ cell.edges :=
    cell.fullTopDownEdges_perm_edges.mem_iff.mp edgeMember
  exact
    (rootHeavyPathCellsTopDown_edge_geometry snapshot tree upper_le_n
      insideLower insideUpper key_lt_n rankZero depth cell cellMember
      edge rawMember).1

/-- The child list inherits the strict canonical attachment order. -/
theorem rootHeavyPathChildrenTopDown_pairwise
    {n key : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    (rootHeavyPathChildrenTopDown snapshot tree (Nat.le_refl n) key 0).Pairwise
      (ChildStrictlyAbove snapshot tree) := by
  rw [rootHeavyPathChildrenTopDown, List.pairwise_map]
  apply
    (rootHeavyPathEdgesTopDown_pairwise snapshot tree (Nat.le_refl n)
      (Nat.zero_le key) key_lt_n key_lt_n rankZero 0).imp_of_mem
  intro first second firstMember secondMember above
  refine ⟨first, second, ?_, ?_, above⟩
  · exact incomingEdge?_eq_edge_of_mem_fullEdges snapshot tree
      (rootHeavyPathEdgesTopDown_mem_fullEdges snapshot tree firstMember)
  · exact incomingEdge?_eq_edge_of_mem_fullEdges snapshot tree
      (rootHeavyPathEdgesTopDown_mem_fullEdges snapshot tree secondMember)

/--
The manuscript's proper-ancestor hit children form a certified canonical
child order after the two accessed-node boundary children have been split
off.
-/
noncomputable def rootHeavyPathCanonicalChildOrder
    {n key : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    CanonicalChildOrder snapshot tree (valuePos ⟨key, key_lt_n⟩) where
  elements :=
    rootHeavyPathChildrenTopDown snapshot tree (Nat.le_refl n) key 0
  nodup :=
    rootHeavyPathChildrenTopDown_nodup snapshot tree (Nat.le_refl n) key 0
  parent := by
    intro child childMember
    obtain ⟨edge, edgeMember, childEq⟩ := List.mem_map.mp childMember
    have fullMember :=
      rootHeavyPathEdgesTopDown_mem_fullEdges snapshot tree edgeMember
    have lookup :=
      incomingEdge?_eq_edge_of_mem_fullEdges snapshot tree fullMember
    have ownerEq :=
      rootHeavyPathEdgesTopDown_owner_eq_accessed snapshot tree
        (Nat.le_refl n) (Nat.zero_le key) key_lt_n key_lt_n rankZero 0
        edge edgeMember
    subst child
    simp [canonicalParent, lookup, ownerEq]
  between := by
    intro first middle last between
    have pairwise :=
      rootHeavyPathChildrenTopDown_pairwise snapshot tree key_lt_n rankZero
    exact Or.inl
      ⟨between.first_before_middle.rel_of_pairwise pairwise,
        between.middle_before_last.rel_of_pairwise pairwise⟩

/-- Every emitted cell remembers the side selected by its attachment key. -/
theorem rootHeavyPathCellsTopDown_side_eq_hitSide
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key depth : ℕ) :
    ∀ cell ∈ rootHeavyPathCellsTopDown snapshot tree upper_le_n key depth,
      cell.side = hitSide key cell.attachmentKey := by
  induction tree generalizing depth with
  | empty =>
      simp [rootHeavyPathCellsTopDown]
  | @node lower root upper left right ihLeft ihRight =>
      by_cases atRoot : key = root
      · simp [rootHeavyPathCellsTopDown, atRoot]
      · by_cases inLeft : key < root
        · intro cell member
          have cases :
              cell = rootHeavyPathCellAt snapshot {
                  lower := lower
                  root := root
                  upper := upper
                  left := left
                  right := right
                  upper_le_n := upper_le_n
                } depth key ∨
                cell ∈ rootHeavyPathCellsTopDown snapshot left (by
                  have := right.lower_le_upper
                  omega) key (depth + 1) := by
            simpa [rootHeavyPathCellsTopDown, atRoot, inLeft] using member
          rcases cases with headEq | tailMember
          · subst cell
            rfl
          · exact ihLeft (by
              have := right.lower_le_upper
              omega) (depth + 1) cell tailMember
        · intro cell member
          have cases :
              cell = rootHeavyPathCellAt snapshot {
                  lower := lower
                  root := root
                  upper := upper
                  left := left
                  right := right
                  upper_le_n := upper_le_n
                } depth key ∨
                cell ∈ rootHeavyPathCellsTopDown snapshot right upper_le_n
                  key (depth + 1) := by
            simpa [rootHeavyPathCellsTopDown, atRoot, inLeft] using member
          rcases cases with headEq | tailMember
          · subst cell
            rfl
          · exact ihRight upper_le_n (depth + 1) cell tailMember

/-- Cell sides in top-down order are the proper search-ancestor sides. -/
theorem map_side_rootHeavyPathCellsTopDown
    {n lower upper key : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (insideLower : lower ≤ key) (insideUpper : key < upper)
    (depth : ℕ) :
    (rootHeavyPathCellsTopDown snapshot tree upper_le_n key depth).map
        RootHeavyPathCell.side =
      (tree.searchPath key).dropLast.map (hitSide key) := by
  rw [← map_attachmentKey_rootHeavyPathCellsTopDown snapshot tree upper_le_n
    insideLower insideUpper depth]
  rw [List.map_map]
  exact List.map_congr_left fun cell member =>
    rootHeavyPathCellsTopDown_side_eq_hitSide snapshot tree upper_le_n
      key depth cell member

/-- A two-edge cell contributes its side exactly twice. -/
theorem map_side_fullTopDownEdges_eq_pair
    {n lower upper key : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (insideLower : lower ≤ key) (insideUpper : key < upper)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (depth : ℕ) {cell : RootHeavyPathCell n}
    (member :
      cell ∈ rootHeavyPathCellsTopDown snapshot tree upper_le_n key depth) :
    cell.fullTopDownEdges.map Edge.side = [cell.side, cell.side] := by
  have edgeLength : cell.edges.length = 2 := by
    simpa [RootHeavyPathCell.children] using
      rootHeavyPathCellsTopDown_forall_children_length_two
        snapshot tree upper_le_n key depth cell member
  have fullLength : cell.fullTopDownEdges.length = 2 := by
    rw [cell.length_fullTopDownEdges, edgeLength]
  have everySide :
      ∀ edge ∈ cell.fullTopDownEdges, edge.side = cell.side := by
    intro edge edgeMember
    have rawMember : edge ∈ cell.edges :=
      cell.fullTopDownEdges_perm_edges.mem_iff.mp edgeMember
    exact
      (rootHeavyPathCellsTopDown_edge_geometry snapshot tree upper_le_n
        insideLower insideUpper key_lt_n rankZero depth cell member
        edge rawMember).2.1
  cases fullEq : cell.fullTopDownEdges with
  | nil =>
      simp [fullEq] at fullLength
  | cons first rest =>
      cases rest with
      | nil =>
          simp [fullEq] at fullLength
      | cons second tail =>
          cases tail with
          | nil =>
              simp only [List.map_cons, List.map_nil]
              rw [everySide first (by simp [fullEq]),
                everySide second (by simp [fullEq])]
          | cons third tail =>
              simp [fullEq] at fullLength

/-- Generic cell-list form of side duplication. -/
theorem map_side_flatMap_fullTopDownEdges_eq_duplicate
    {n : ℕ} (cells : List (RootHeavyPathCell n))
    (cellSides :
      ∀ cell ∈ cells,
        cell.fullTopDownEdges.map Edge.side = [cell.side, cell.side]) :
    (cells.flatMap RootHeavyPathCell.fullTopDownEdges).map Edge.side =
      duplicateHitSides (cells.map RootHeavyPathCell.side) := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
      have head := cellSides cell (by simp)
      have tail :
          ∀ other ∈ cells,
            other.fullTopDownEdges.map Edge.side =
              [other.side, other.side] := by
        intro other member
        exact cellSides other (by simp [member])
      simp [duplicateHitSides, head, ih tail]

/-- Mapping sides through all cells is exactly `duplicateHitSides`. -/
theorem map_side_rootHeavyPathEdgesTopDown
    {n lower upper key : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (insideLower : lower ≤ key) (insideUpper : key < upper)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (depth : ℕ) :
    (rootHeavyPathEdgesTopDown snapshot tree upper_le_n key depth).map
        Edge.side =
      duplicateHitSides
        ((tree.searchPath key).dropLast.map (hitSide key)) := by
  let cells := rootHeavyPathCellsTopDown snapshot tree upper_le_n key depth
  have cellSides :
      ∀ cell ∈ cells,
        cell.fullTopDownEdges.map Edge.side = [cell.side, cell.side] :=
    fun cell member =>
      map_side_fullTopDownEdges_eq_pair snapshot tree upper_le_n
        insideLower insideUpper key_lt_n rankZero depth member
  change
    (cells.flatMap RootHeavyPathCell.fullTopDownEdges).map Edge.side = _
  have duplicated :=
    map_side_flatMap_fullTopDownEdges_eq_duplicate cells cellSides
  rw [duplicated,
    map_side_rootHeavyPathCellsTopDown snapshot tree upper_le_n
      insideLower insideUpper depth]

/--
The actual chronological bottom-up child-side word is the exact duplicated
hit-side schedule used by `InternalPairingFractionWitness`.
-/
theorem map_side_rootHeavyPathEdgesBottomUp
    {n lower upper key : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (insideLower : lower ≤ key) (insideUpper : key < upper)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (depth : ℕ) :
    (rootHeavyPathEdgesBottomUp snapshot tree upper_le_n key depth).map
        Edge.side = duplicateHitSides (hitSides tree key) := by
  rw [rootHeavyPathEdgesBottomUp, List.map_reverse,
    map_side_rootHeavyPathEdgesTopDown snapshot tree upper_le_n
      insideLower insideUpper key_lt_n rankZero depth,
    reverse_duplicateHitSides]
  simp [hitSides]

/--
The concrete canonical sides of chronological proper-ancestor children are
the duplicated hit-side word used by the splay transcript.
-/
theorem map_canonicalSide_rootHeavyPathChildrenBottomUp
    {n key : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    (rootHeavyPathChildrenBottomUp snapshot tree (Nat.le_refl n) key 0).map
        (canonicalSide snapshot tree) =
      duplicateHitSides (hitSides tree key) := by
  rw [rootHeavyPathChildrenBottomUp, List.map_map]
  calc
    (rootHeavyPathEdgesBottomUp snapshot tree (Nat.le_refl n) key 0).map
          (canonicalSide snapshot tree ∘ Edge.child) =
        (rootHeavyPathEdgesBottomUp snapshot tree (Nat.le_refl n) key 0).map
          Edge.side := by
      apply List.map_congr_left
      intro edge bottomMember
      have topMember :
          edge ∈
            rootHeavyPathEdgesTopDown snapshot tree (Nat.le_refl n) key 0 := by
        simpa only [rootHeavyPathEdgesBottomUp, List.mem_reverse] using
          bottomMember
      have lookup := incomingEdge?_eq_edge_of_mem_fullEdges snapshot tree
        (rootHeavyPathEdgesTopDown_mem_fullEdges snapshot tree topMember)
      simp [canonicalSide, lookup]
    _ = duplicateHitSides (hitSides tree key) :=
      map_side_rootHeavyPathEdgesBottomUp snapshot tree (Nat.le_refl n)
        (Nat.zero_le key) key_lt_n key_lt_n rankZero 0

end Splay.Accounting
