import Splay.Accounting.RootHeavyPathPairingGeometry
import Splay.Lazy.Canonical

namespace Splay.Accounting

open Splay.Rank
open Splay.Tree.BST
open Splay.Lazy.Canonical

/--
The two canonical light edges contributed by one proper search ancestor.
The attachment key gives the persistent identity of the ancestor and `side`
is the common side of the accessed root-heavy path on which its children
occur.
-/
structure RootHeavyPathCell (n : ℕ) where
  attachmentKey : ℕ
  side : Splay.Lazy.Side
  edges : List (Edge n)
  deriving Repr

namespace RootHeavyPathCell

/-- Heap children carried by a root-heavy-path cell. -/
def children {n : ℕ} (cell : RootHeavyPathCell n) : List (External n) :=
  cell.edges.map Edge.child

@[simp]
theorem length_children {n : ℕ} (cell : RootHeavyPathCell n) :
    cell.children.length = cell.edges.length := by
  simp [children]

end RootHeavyPathCell

/-- The cell emitted at one concrete ancestor on the search path. -/
noncomputable def rootHeavyPathCellAt {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n) (depth key : ℕ) :
    RootHeavyPathCell n where
  attachmentKey := node.root
  side := hitSide key node.root
  edges := edgesAtNode snapshot node depth

@[simp]
theorem rootHeavyPathCellAt_attachmentKey {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n) (depth key : ℕ) :
    (rootHeavyPathCellAt snapshot node depth key).attachmentKey = node.root :=
  rfl

@[simp]
theorem rootHeavyPathCellAt_edges_length {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n) (depth key : ℕ) :
    (rootHeavyPathCellAt snapshot node depth key).edges.length = 2 := by
  simp [rootHeavyPathCellAt]

@[simp]
theorem rootHeavyPathCellAt_children_length {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n) (depth key : ℕ) :
    (rootHeavyPathCellAt snapshot node depth key).children.length = 2 := by
  simp [RootHeavyPathCell.children, rootHeavyPathCellAt]

/--
At a proper search ancestor, rank zero forces the accessed value to own the
whole heavy path.  Both emitted light edges therefore have that owner and
the common side recorded by `hitSide`.
-/
theorem rootHeavyPathCellAt_edge_geometry {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n) (depth key : ℕ)
    (insideLower : node.lower ≤ key) (insideUpper : key < node.upper)
    (notRoot : key ≠ node.root) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    {edge : Edge n}
    (member : edge ∈ (rootHeavyPathCellAt snapshot node depth key).edges) :
    edge.owner = valuePos ⟨key, key_lt_n⟩ ∧
      edge.side = (rootHeavyPathCellAt snapshot node depth key).side ∧
      edge.attachmentKey =
        (rootHeavyPathCellAt snapshot node depth key).attachmentKey := by
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
  have ownerEq : node.owner snapshot = accessed := by
    exact
      (snapshot.intervalMin_unique
        node.wholeLower node.wholeUpper node.whole_nonempty
        accessedIsMin).symm
  have edgeMember : edge ∈ edgesAtNode snapshot node depth := by
    simpa only [rootHeavyPathCellAt] using member
  have valid := mem_edgesAtNode_valid snapshot node depth edgeMember
  have edgeOwner : edge.owner = accessed := valid.2.1.trans ownerEq
  have attachment : edge.attachmentKey = node.root := valid.attachmentKey_eq
  constructor
  · exact edgeOwner
  constructor
  · by_cases keyLtRoot : key < node.root
    · have heavyEq : node.heavyBranch snapshot = .left := by
        apply node.heavyBranch_eq_of_rank_eq_zero
          snapshot .left accessed
          (by simpa only [accessed] using rankZero) insideWhole
        change 2 * key + 1 ≤ 2 * node.root
        omega
      have branchContains := node.branchMin_in_branch snapshot edge.branch
      have childGt : accessed.val < edge.child.val := by
        rw [valid.2.2.1]
        cases branchEq : edge.branch with
        | left =>
            exfalso
            exact (valid.1 (branchEq.trans heavyEq.symm)).elim
        | middle =>
            rw [branchEq] at branchContains
            change 2 * key + 1 < (node.branchMin snapshot .middle).val
            change (node.branchMin snapshot .middle).val =
              2 * node.root + 1 at branchContains
            omega
        | right =>
            rw [branchEq] at branchContains
            change 2 * key + 1 < (node.branchMin snapshot .right).val
            change 2 * node.root + 2 ≤
              (node.branchMin snapshot .right).val at branchContains
            omega
      rw [valid.2.2.2.1, edgeOwner]
      change
        (if edge.child.val < accessed.val then Splay.Lazy.Side.left
          else Splay.Lazy.Side.right) =
        (if node.root < key then Splay.Lazy.Side.left
          else Splay.Lazy.Side.right)
      rw [if_neg (by omega), if_neg (by omega)]
    · have rootLtKey : node.root < key := by omega
      have heavyEq : node.heavyBranch snapshot = .right := by
        apply node.heavyBranch_eq_of_rank_eq_zero
          snapshot .right accessed
          (by simpa only [accessed] using rankZero) insideWhole
        change 2 * node.root + 2 ≤ 2 * key + 1
        omega
      have branchContains := node.branchMin_in_branch snapshot edge.branch
      have childLt : edge.child.val < accessed.val := by
        rw [valid.2.2.1]
        cases branchEq : edge.branch with
        | left =>
            rw [branchEq] at branchContains
            change (node.branchMin snapshot .left).val < 2 * key + 1
            change (node.branchMin snapshot .left).val ≤
              2 * node.root at branchContains
            omega
        | middle =>
            rw [branchEq] at branchContains
            change (node.branchMin snapshot .middle).val < 2 * key + 1
            change (node.branchMin snapshot .middle).val =
              2 * node.root + 1 at branchContains
            omega
        | right =>
            exfalso
            exact (valid.1 (branchEq.trans heavyEq.symm)).elim
      rw [valid.2.2.2.1, edgeOwner]
      change
        (if edge.child.val < accessed.val then Splay.Lazy.Side.left
          else Splay.Lazy.Side.right) =
        (if node.root < key then Splay.Lazy.Side.left
          else Splay.Lazy.Side.right)
      rw [if_pos childLt, if_pos rootLtKey]
  · simpa only [rootHeavyPathCellAt] using attachment

/--
Cells of all proper search ancestors, in root-to-access order.  The accessed
node itself is deliberately omitted: its two light children are the
manuscript's isolated `x⁻` and `x⁺` boundary singletons.
-/
noncomputable def rootHeavyPathCellsTopDown {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (key : ℕ) (depth : ℕ := 0) :
    List (RootHeavyPathCell n) :=
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
      if key = root then []
      else if key < root then
        rootHeavyPathCellAt snapshot node depth key ::
          rootHeavyPathCellsTopDown snapshot left (by
            have := right.lower_le_upper
            omega) key (depth + 1)
      else
        rootHeavyPathCellAt snapshot node depth key ::
          rootHeavyPathCellsTopDown snapshot right upper_le_n key (depth + 1)

/-- The same persistent cells in the bottom-up order used by splaying. -/
noncomputable def rootHeavyPathCellsBottomUp {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (key : ℕ) (depth : ℕ := 0) :
    List (RootHeavyPathCell n) :=
  (rootHeavyPathCellsTopDown snapshot tree upper_le_n key depth).reverse

/-- Every emitted root-heavy-path cell contains exactly two children. -/
theorem rootHeavyPathCellsTopDown_forall_children_length_two
    {n lower upper : ℕ} (snapshot : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (key depth : ℕ) :
    ∀ cell ∈ rootHeavyPathCellsTopDown snapshot tree upper_le_n key depth,
      cell.children.length = 2 := by
  induction tree generalizing depth with
  | empty =>
      simp [rootHeavyPathCellsTopDown]
  | @node lower root upper left right ihLeft ihRight =>
      by_cases atRoot : key = root
      · simp [rootHeavyPathCellsTopDown, atRoot]
      · by_cases inLeft : key < root
        · simp only [rootHeavyPathCellsTopDown, atRoot, inLeft]
          simpa using ihLeft (by
            have := right.lower_le_upper
            omega) (depth + 1)
        · simp only [rootHeavyPathCellsTopDown, atRoot, inLeft]
          simpa using ihRight upper_le_n (depth + 1)

theorem rootHeavyPathCellsBottomUp_forall_children_length_two
    {n lower upper : ℕ} (snapshot : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (key depth : ℕ) :
    ∀ cell ∈ rootHeavyPathCellsBottomUp snapshot tree upper_le_n key depth,
      cell.children.length = 2 := by
  intro cell member
  apply rootHeavyPathCellsTopDown_forall_children_length_two
    snapshot tree upper_le_n key depth cell
  simpa [rootHeavyPathCellsBottomUp] using member

/-- Every edge in every top-down cell has the certified common geometry. -/
theorem rootHeavyPathCellsTopDown_edge_geometry
    {n lower upper key : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (insideLower : lower ≤ key) (insideUpper : key < upper)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (depth : ℕ) :
    ∀ cell ∈ rootHeavyPathCellsTopDown snapshot tree upper_le_n key depth,
      ∀ edge ∈ cell.edges,
        edge.owner = valuePos ⟨key, key_lt_n⟩ ∧
          edge.side = cell.side ∧
          edge.attachmentKey = cell.attachmentKey := by
  induction tree generalizing depth with
  | empty boundary =>
      simp [rootHeavyPathCellsTopDown]
  | @node lower root upper left right ihLeft ihRight =>
      by_cases atRoot : key = root
      · simp [rootHeavyPathCellsTopDown, atRoot]
      · by_cases inLeft : key < root
        · intro cell cellMember edge edgeMember
          simp only [rootHeavyPathCellsTopDown, atRoot, inLeft] at cellMember
          have cellCases := List.mem_cons.mp cellMember
          rcases cellCases with headEq | tailMember
          · subst cell
            exact rootHeavyPathCellAt_edge_geometry snapshot _ depth key
              insideLower insideUpper atRoot key_lt_n rankZero edgeMember
          · exact ihLeft (by
              have := right.lower_le_upper
              omega) insideLower inLeft (depth + 1) cell tailMember
                edge edgeMember
        · have rootLtKey : root < key := by omega
          intro cell cellMember edge edgeMember
          simp only [rootHeavyPathCellsTopDown, atRoot, inLeft] at cellMember
          have cellCases := List.mem_cons.mp cellMember
          rcases cellCases with headEq | tailMember
          · subst cell
            exact rootHeavyPathCellAt_edge_geometry snapshot _ depth key
              insideLower insideUpper atRoot key_lt_n rankZero edgeMember
          · exact ihRight upper_le_n (by omega) insideUpper
              (depth + 1) cell tailMember edge edgeMember

/-- Reversing the cell order preserves the same per-edge geometry. -/
theorem rootHeavyPathCellsBottomUp_edge_geometry
    {n lower upper key : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (insideLower : lower ≤ key) (insideUpper : key < upper)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (depth : ℕ) :
    ∀ cell ∈ rootHeavyPathCellsBottomUp snapshot tree upper_le_n key depth,
      ∀ edge ∈ cell.edges,
        edge.owner = valuePos ⟨key, key_lt_n⟩ ∧
          edge.side = cell.side ∧
          edge.attachmentKey = cell.attachmentKey := by
  intro cell cellMember
  apply rootHeavyPathCellsTopDown_edge_geometry snapshot tree upper_le_n
    insideLower insideUpper key_lt_n rankZero depth cell
  simpa [rootHeavyPathCellsBottomUp] using cellMember

/--
Persistent cell identities are exactly the proper search ancestors in
top-down order.
-/
theorem map_attachmentKey_rootHeavyPathCellsTopDown
    {n lower upper key : ℕ} (snapshot : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (insideLower : lower ≤ key)
    (insideUpper : key < upper) (depth : ℕ) :
    (rootHeavyPathCellsTopDown snapshot tree upper_le_n key depth).map
        RootHeavyPathCell.attachmentKey =
      (tree.searchPath key).dropLast := by
  induction tree generalizing depth with
  | empty boundary =>
      omega
  | @node lower root upper left right ihLeft ihRight =>
      by_cases atRoot : key = root
      · subst key
        simp [rootHeavyPathCellsTopDown,
          _root_.Splay.Tree.BST.searchPath]
      · by_cases inLeft : key < root
        · have childPathNonempty :=
            searchPath.ne_nil left insideLower inLeft
          cases pathEq : left.searchPath key with
          | nil => exact (childPathNonempty pathEq).elim
          | cons first rest =>
              simp [rootHeavyPathCellsTopDown, atRoot, inLeft,
                _root_.Splay.Tree.BST.searchPath, pathEq,
                ihLeft (by
                  have := right.lower_le_upper
                  omega) insideLower inLeft (depth + 1)]
        · have rootLtKey : root < key := by omega
          have childPathNonempty :=
            searchPath.ne_nil right (by omega) insideUpper
          cases pathEq : right.searchPath key with
          | nil => exact (childPathNonempty pathEq).elim
          | cons first rest =>
              simp [rootHeavyPathCellsTopDown, atRoot, inLeft,
                _root_.Splay.Tree.BST.searchPath, pathEq,
                ihRight upper_le_n (by omega) insideUpper (depth + 1)]

/-- Bottom-up cell identities are exactly the persistent splay hit list. -/
theorem map_attachmentKey_rootHeavyPathCellsBottomUp
    {n lower upper key : ℕ} (snapshot : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (insideLower : lower ≤ key)
    (insideUpper : key < upper) (depth : ℕ) :
    (rootHeavyPathCellsBottomUp snapshot tree upper_le_n key depth).map
        RootHeavyPathCell.attachmentKey =
      (tree.searchPath key).dropLast.reverse := by
  rw [rootHeavyPathCellsBottomUp, List.map_reverse,
    map_attachmentKey_rootHeavyPathCellsTopDown snapshot tree upper_le_n
      insideLower insideUpper depth]

end Splay.Accounting
