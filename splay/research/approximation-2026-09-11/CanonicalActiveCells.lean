import CanonicalActiveMinimum
import Splay.Accounting.RootHeavyPathFullOrder

/-! The exact two-child cells used by the original full splay ordering.
The first child in bottom-up order is inactive; the other is active or null. -/

namespace Splay.Research.CanonicalActive

open Splay.Rank Splay.Tree Splay.Tree.BST Splay.Lazy.Canonical Splay.Accounting

theorem branch_minimum_key_active {n : ℕ} (snapshot : Snapshot n) (node : AtNode n)
    (branch : TernaryBranch) (notMiddle : branch ≠ .middle) (key : Fin n)
    (minimum : node.branchMin snapshot branch = valuePos key) :
    key ∈ activeFrom snapshot (.node node.left node.right) node.upper_le_n := by
  have minInfo := node.branchMin_isMin snapshot branch
  rw [minimum] at minInfo
  simp only [activeFrom, Finset.mem_union]
  right
  cases branch with
  | middle => contradiction
  | left =>
      left
      have lo : 2*node.lower ≤ 2*key.val+1 := minInfo.1
      have hi : 2*key.val+1 ≤ 2*node.root := minInfo.2.1
      apply minimum_key_mem_activeFrom snapshot node.left _ key (by omega) (by omega)
      exact minInfo.2.2
  | right =>
      right
      have lo : 2*(node.root+1) ≤ 2*key.val+1 := minInfo.1
      have hi : 2*key.val+1 ≤ 2*node.upper := minInfo.2.1
      apply minimum_key_mem_activeFrom snapshot node.right _ key (by omega) (by omega)
      exact minInfo.2.2

theorem external_value_or_null {n : ℕ} (position : External n) :
    (∃ key : Fin n, position = valuePos key) ∨
      ∃ boundary : Fin (n+1), position = nullPos boundary := by
  by_cases even : position.val % 2 = 0
  · right
    refine ⟨⟨position.val/2, by have := position.isLt; omega⟩, ?_⟩
    apply Fin.ext
    change position.val = 2*(position.val/2)
    omega
  · left
    refine ⟨⟨position.val/2, by have := position.isLt; omega⟩, ?_⟩
    apply Fin.ext
    change position.val = 2*(position.val/2)+1
    omega

theorem branch_minimum_active_or_null {n : ℕ} (snapshot : Snapshot n) (node : AtNode n)
    (branch : TernaryBranch) (notMiddle : branch ≠ .middle) :
    (∃ key : Fin n, node.branchMin snapshot branch = valuePos key ∧
      key ∈ activeFrom snapshot (.node node.left node.right) node.upper_le_n) ∨
    ∃ boundary : Fin (n+1), node.branchMin snapshot branch = nullPos boundary := by
  rcases external_value_or_null (node.branchMin snapshot branch) with ⟨key, equal⟩ | null
  · exact Or.inl ⟨key, equal, branch_minimum_key_active snapshot node branch notMiddle key equal⟩
  · exact Or.inr null

theorem branch_middle_eq_value {n : ℕ} (snapshot : Snapshot n) (node : AtNode n) :
    node.branchMin snapshot .middle = valuePos
      ⟨node.root, lt_of_lt_of_le node.root_lt_upper node.upper_le_n⟩ := by
  apply Fin.ext
  exact node.branchMin_in_branch snapshot .middle

theorem bottomUp_cell_children {n : ℕ} (snapshot : Snapshot n) (node : AtNode n)
    (depth : ℕ) (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    (insideLower : node.lower ≤ key.val) (insideUpper : key.val < node.upper)
    (different : node.root ≠ key.val) :
    (rootHeavyPathCellAt snapshot node depth key.val).fullBottomUpEdges.map Edge.child =
      [valuePos ⟨node.root, lt_of_lt_of_le node.root_lt_upper node.upper_le_n⟩,
       node.branchMin snapshot (if key.val < node.root then .right else .left)] := by
  have heavy := heavyBranch_eq_searchBranch snapshot node key.val
    insideLower insideUpper (Ne.symm different) key.isLt rankZero
  have middle := branch_middle_eq_value snapshot node
  by_cases onLeft : key.val < node.root
  · simp [RootHeavyPathCell.fullBottomUpEdges, RootHeavyPathCell.fullTopDownEdges,
      rootHeavyPathCellAt, hitSide, edgesAtNode, lightBranches, allBranches,
      heavy, onLeft, show ¬node.root < key.val by omega, edgeFor, middle]
  · have onRight : node.root < key.val := by omega
    simp [RootHeavyPathCell.fullBottomUpEdges, RootHeavyPathCell.fullTopDownEdges,
      rootHeavyPathCellAt, hitSide, edgesAtNode, lightBranches, allBranches,
      heavy, onLeft, onRight, edgeFor, middle]

def CellActiveClassification {n : ℕ} (activeKeys : Finset (Fin n))
    (cell : RootHeavyPathCell n) : Prop :=
  ∃ middle : Fin n, ∃ endpoint : External n,
    cell.fullBottomUpEdges.map Edge.child = [valuePos middle, endpoint] ∧
    middle ∉ activeKeys ∧
      ((∃ key : Fin n, endpoint = valuePos key ∧ key ∈ activeKeys) ∨
       ∃ boundary : Fin (n+1), endpoint = nullPos boundary)

theorem local_cell_classification {n occurrenceDepth : ℕ} (snapshot : Snapshot n)
    (whole : Splay.Tree.BST 0 n) (node : AtNode n)
    (occurrence : SubtreeAt (.node node.left node.right) occurrenceDepth whole)
    (depth : ℕ) (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    (insideLower : node.lower ≤ key.val) (insideUpper : key.val < node.upper)
    (different : node.root ≠ key.val) :
    CellActiveClassification (active snapshot whole) (rootHeavyPathCellAt snapshot node depth key.val) := by
  let middle : Fin n := ⟨node.root, lt_of_lt_of_le node.root_lt_upper node.upper_le_n⟩
  let branch : TernaryBranch := if key.val < node.root then .right else .left
  refine ⟨middle, node.branchMin snapshot branch,
    bottomUp_cell_children snapshot node depth key rankZero insideLower insideUpper different, ?_, ?_⟩
  · have inactive := proper_query_ancestor_not_active snapshot node key rankZero insideLower insideUpper different
    have same := subtreeAt_active_iff snapshot occurrence (le_refl n) middle
      node.lower_le_root node.root_lt_upper
    exact fun member => inactive (same.mp member)
  · have notMiddle : branch ≠ .middle := by dsimp [branch]; split_ifs <;> decide
    rcases branch_minimum_active_or_null snapshot node branch notMiddle with
      ⟨endpoint, equal, member⟩ | null
    · exact Or.inl ⟨endpoint, equal, subtreeAt_active_subset snapshot occurrence (le_refl n) member⟩
    · exact Or.inr null

theorem all_path_cells_classified {n lower upper occurrenceDepth : ℕ}
    (snapshot : Snapshot n) (whole : Splay.Tree.BST 0 n) (tree : Splay.Tree.BST lower upper)
    (occurrence : SubtreeAt tree occurrenceDepth whole) (upper_le_n : upper ≤ n)
    (depth : ℕ) (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    (insideLower : lower ≤ key.val) (insideUpper : key.val < upper) :
    ∀ cell ∈ rootHeavyPathCellsTopDown snapshot tree upper_le_n key.val depth,
      CellActiveClassification (active snapshot whole) cell := by
  induction tree generalizing occurrenceDepth depth with
  | empty boundary => simp [rootHeavyPathCellsTopDown]
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := { lower, root, upper, left, right, upper_le_n }
      by_cases atRoot : key.val = root
      · simp [rootHeavyPathCellsTopDown, atRoot]
      · have head := local_cell_classification snapshot whole node occurrence depth key rankZero
          insideLower insideUpper (Ne.symm atRoot)
        by_cases onLeft : key.val < root
        · have childOccurrence : SubtreeAt left (1+occurrenceDepth) whole :=
            (SubtreeAt.left SubtreeAt.here right).trans occurrence
          have tail := ihLeft childOccurrence (by have := right.lower_le_upper; omega)
            (depth+1) insideLower onLeft
          simpa only [rootHeavyPathCellsTopDown, atRoot, onLeft, ite_false, ite_true,
            List.mem_cons, forall_eq_or_imp] using And.intro head tail
        · have childOccurrence : SubtreeAt right (1+occurrenceDepth) whole :=
            (SubtreeAt.right left SubtreeAt.here).trans occurrence
          have tail := ihRight childOccurrence upper_le_n (depth+1) (by omega) insideUpper
          simpa only [rootHeavyPathCellsTopDown, atRoot, onLeft, ite_false,
            List.mem_cons, forall_eq_or_imp] using And.intro head tail

theorem classified_cells_even_inactive {n : ℕ} (activeKeys : Finset (Fin n))
    (cells : List (RootHeavyPathCell n))
    (classified : ∀ cell ∈ cells, CellActiveClassification activeKeys cell)
    (index : ℕ) (position : External n)
    (found : (cells.flatMap fun cell => cell.fullBottomUpEdges.map Edge.child)[2*index]? = some position) :
    ∃ key : Fin n, position = valuePos key ∧ key ∉ activeKeys := by
  induction cells generalizing index with
  | nil => simp at found
  | cons cell cells ih =>
      obtain ⟨middle, endpoint, children, inactive, endpointKind⟩ := classified cell (by simp)
      rw [List.flatMap_cons, children] at found
      cases index with
      | zero =>
          simp only [Nat.mul_zero, List.cons_append, List.nil_append, List.getElem?_cons_zero] at found
          exact ⟨middle, (Option.some.inj found).symm, inactive⟩
      | succ index =>
          apply ih (fun other member => classified other (List.mem_cons_of_mem _ member)) index
          simpa only [Nat.mul_succ, List.cons_append, List.nil_append,
            Nat.add_succ, Nat.add_zero, List.getElem?_cons_succ] using found

theorem bottomUp_even_hit_inactive {n : ℕ} (snapshot : Snapshot n)
    (tree : Splay.Tree.BST 0 n) (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    (index : ℕ) (position : External n)
    (found : (rootHeavyPathChildrenBottomUp snapshot tree (le_refl n) key.val 0)[2*index]? = some position) :
    ∃ middle : Fin n, position = valuePos middle ∧ middle ∉ active snapshot tree := by
  have all := all_path_cells_classified snapshot tree tree SubtreeAt.here (le_refl n) 0
    key rankZero (Nat.zero_le _) key.isLt
  rw [rootHeavyPathChildrenBottomUp_eq_flatMap_fullBottomUpEdges] at found
  apply classified_cells_even_inactive (active snapshot tree) _ (fun cell member => ?_) index position found
  apply all cell
  simpa only [rootHeavyPathCellsBottomUp, List.mem_reverse] using member

theorem classified_cells_odd_active_or_null {n : ℕ} (activeKeys : Finset (Fin n))
    (cells : List (RootHeavyPathCell n))
    (classified : ∀ cell ∈ cells, CellActiveClassification activeKeys cell)
    (index : ℕ) (position : External n)
    (found : (cells.flatMap fun cell => cell.fullBottomUpEdges.map Edge.child)[2*index+1]? = some position) :
    (∃ key : Fin n, position = valuePos key ∧ key ∈ activeKeys) ∨
      ∃ boundary : Fin (n+1), position = nullPos boundary := by
  induction cells generalizing index with
  | nil => simp at found
  | cons cell cells ih =>
      obtain ⟨middle, endpoint, children, inactive, endpointKind⟩ := classified cell (by simp)
      rw [List.flatMap_cons, children] at found
      cases index with
      | zero =>
          simp only [Nat.mul_zero, Nat.zero_add, List.cons_append, List.nil_append,
            List.getElem?_cons_succ, List.getElem?_cons_zero] at found
          exact (Option.some.inj found) ▸ endpointKind
      | succ index =>
          apply ih (fun other member => classified other (List.mem_cons_of_mem _ member)) index
          simpa only [Nat.mul_succ, List.cons_append, List.nil_append,
            Nat.add_succ, Nat.add_zero, List.getElem?_cons_succ] using found

theorem bottomUp_odd_hit_active_or_null {n : ℕ} (snapshot : Snapshot n)
    (tree : Splay.Tree.BST 0 n) (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    (index : ℕ) (position : External n)
    (found : (rootHeavyPathChildrenBottomUp snapshot tree (le_refl n) key.val 0)[2*index+1]? = some position) :
    (∃ endpoint : Fin n, position = valuePos endpoint ∧ endpoint ∈ active snapshot tree) ∨
      ∃ boundary : Fin (n+1), position = nullPos boundary := by
  have all := all_path_cells_classified snapshot tree tree SubtreeAt.here (le_refl n) 0
    key rankZero (Nat.zero_le _) key.isLt
  rw [rootHeavyPathChildrenBottomUp_eq_flatMap_fullBottomUpEdges] at found
  apply classified_cells_odd_active_or_null (active snapshot tree) _ (fun cell member => ?_) index position found
  apply all cell
  simpa only [rootHeavyPathCellsBottomUp, List.mem_reverse] using member

def QuadActiveClassification {n : ℕ} (activeKeys : Finset (Fin n))
    (extra left middle right : External n) : Prop :=
  (∃ key : Fin n, extra = valuePos key ∧ key ∉ activeKeys) ∧
  ((∃ key : Fin n, left = valuePos key ∧ key ∈ activeKeys) ∨
    ∃ boundary : Fin (n+1), left = nullPos boundary) ∧
  (∃ key : Fin n, middle = valuePos key ∧ key ∉ activeKeys) ∧
  ((∃ key : Fin n, right = valuePos key ∧ key ∈ activeKeys) ∨
    ∃ boundary : Fin (n+1), right = nullPos boundary)

/-- Classification of the exact four-child group used by the original
bottom-up splay order. No filtered-list ordering is assumed. -/
theorem bottomUp_group_classified {n : ℕ} (snapshot : Snapshot n)
    (tree : Splay.Tree.BST 0 n) (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    (group : ℕ) (extra left middle right : External n)
    (chunk : ((rootHeavyPathChildrenBottomUp snapshot tree (le_refl n) key.val 0).drop
      (4*group)).take 4 = [extra, left, middle, right]) :
    QuadActiveClassification (active snapshot tree) extra left middle right := by
  have first := congrArg (fun elements => elements[0]?) chunk
  have second := congrArg (fun elements => elements[1]?) chunk
  have third := congrArg (fun elements => elements[2]?) chunk
  have fourth := congrArg (fun elements => elements[3]?) chunk
  simp only [List.getElem?_take, List.getElem?_drop] at first second third fourth
  simp only [Nat.reduceLT, ↓reduceIte, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Nat.add_zero] at first second third fourth
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply bottomUp_even_hit_inactive snapshot tree key rankZero (2*group) extra
    rw [show 2*(2*group) = 4*group by omega]
    exact first
  · apply bottomUp_odd_hit_active_or_null snapshot tree key rankZero (2*group) left
    rw [show 2*(2*group) = 4*group by omega]
    exact second
  · apply bottomUp_even_hit_inactive snapshot tree key rankZero (2*group+1) middle
    rw [show 2*(2*group+1) = 4*group+2 by omega]
    exact third
  · apply bottomUp_odd_hit_active_or_null snapshot tree key rankZero (2*group+1) right
    rw [show 2*(2*group+1)+1 = 4*group+3 by omega]
    exact fourth

end Splay.Research.CanonicalActive

#print axioms Splay.Research.CanonicalActive.branch_minimum_active_or_null
#print axioms Splay.Research.CanonicalActive.bottomUp_cell_children
#print axioms Splay.Research.CanonicalActive.all_path_cells_classified
#print axioms Splay.Research.CanonicalActive.bottomUp_even_hit_inactive
#print axioms Splay.Research.CanonicalActive.bottomUp_odd_hit_active_or_null
#print axioms Splay.Research.CanonicalActive.bottomUp_group_classified
