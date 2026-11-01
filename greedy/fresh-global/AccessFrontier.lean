import AccessExpansion
import Splay.Lazy.CanonicalView
import Splay.Rank.FromTree
import ValueNullRanks
import Mathlib.Data.List.Sort

/-!
The actual children of the minimum-rank access record are the ordered
search-path frontier: off-path subtree minima alternating with real path
values, with the access record removed. This is a statement about concrete
canonical light edges, independent of any supplied abstract heap trace.
-/
namespace GreedyMerge.AccessFrontier
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.SearchGaps GreedyMerge.PathPlateau

noncomputable def Frontier {n lo hi : ℕ} (snapshot : Snapshot n) (access : ℕ)
    (tree : BST lo hi) (upper : hi ≤ n) : List ℕ :=
  match tree with
  | .empty i => [(subtreeOwner snapshot (.empty i) upper).val]
  | .node (root := root) left right =>
      let leftUpper : root ≤ n := by have := right.lower_le_upper; omega
      if access = root then
        [(subtreeOwner snapshot left leftUpper).val, 2*root+1,
          (subtreeOwner snapshot right upper).val]
      else if access < root then
        Frontier snapshot access left leftUpper ++
          [2*root+1, (subtreeOwner snapshot right upper).val]
      else
        [(subtreeOwner snapshot left leftUpper).val, 2*root+1] ++
          Frontier snapshot access right upper

theorem subtreeOwner_bounds {n lo hi : ℕ} (snapshot : Snapshot n)
    (tree : BST lo hi) (upper : hi ≤ n) :
    2*lo ≤ (subtreeOwner snapshot tree upper).val ∧
      (subtreeOwner snapshot tree upper).val ≤ 2*hi := by
  have spec := subtreeOwner_isMin snapshot tree upper
  exact ⟨spec.1, spec.2.1⟩

theorem frontier_bounds {n lo hi access value : ℕ} (snapshot : Snapshot n)
    (tree : BST lo hi) (upper : hi ≤ n)
    (member : value ∈ Frontier snapshot access tree upper) :
    2*lo ≤ value ∧ value ≤ 2*hi := by
  induction tree with
  | empty =>
      simp only [Frontier, List.mem_singleton] at member
      subst value
      exact subtreeOwner_bounds snapshot _ upper
  | @node lo root hi left right ihLeft ihRight =>
      have hlo := left.lower_le_upper
      have hhi := right.lower_le_upper
      have hleft := subtreeOwner_bounds snapshot left (by omega : root ≤ n)
      have hright := subtreeOwner_bounds snapshot right upper
      simp only [Frontier] at member
      split_ifs at member
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> omega
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with hm | rfl | rfl
        · have h := ihLeft (by omega) hm; omega
        · omega
        · omega
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with (rfl | rfl) | hm
        · omega
        · omega
        · have h := ihRight upper hm; omega

private theorem pairwise_two (a b : ℕ) (order : a < b) :
    [a,b].Pairwise (· < ·) := by simp [order]

private theorem pairwise_three (a b c : ℕ) (first : a < b) (second : b < c) :
    [a,b,c].Pairwise (· < ·) := by simp [first, second, first.trans second]

theorem frontier_pairwise {n lo hi access : ℕ} (snapshot : Snapshot n)
    (tree : BST lo hi) (upper : hi ≤ n) :
    (Frontier snapshot access tree upper).Pairwise (· < ·) := by
  induction tree with
  | empty => simp [Frontier]
  | @node lo root hi left right ihLeft ihRight =>
      have hlo := left.lower_le_upper
      have hhi := right.lower_le_upper
      have hleft := subtreeOwner_bounds snapshot left (by omega : root ≤ n)
      have hright := subtreeOwner_bounds snapshot right upper
      simp only [Frontier]
      split_ifs
      · exact pairwise_three _ _ _ (by omega) (by omega)
      · apply List.pairwise_append.mpr
        refine ⟨ihLeft (by omega), ?_, ?_⟩
        · exact pairwise_two _ _ (by omega)
        · intro first hf second hs
          have hb := frontier_bounds snapshot left (by omega : root ≤ n) hf
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl <;> omega
      · apply List.pairwise_append.mpr
        refine ⟨?_, ihRight upper, ?_⟩
        · exact pairwise_two _ _ (by omega)
        · intro first hf second hs
          have hb := frontier_bounds snapshot right upper hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
          rcases hf with rfl | rfl <;> omega

theorem frontier_length {n lo hi access : ℕ} (snapshot : Snapshot n)
    (tree : BST lo hi) (upper : hi ≤ n) :
    (Frontier snapshot access tree upper).length = 2*(PathKeys access tree).card+1 := by
  induction tree with
  | empty => simp [Frontier, PathKeys]
  | @node lo root hi left right ihLeft ihRight =>
      have hlo := left.lower_le_upper
      have hhi := right.lower_le_upper
      have notLeft : root ∉ PathKeys access left := by
        intro member
        have h := pathKeys_bounds left member
        omega
      have notRight : root ∉ PathKeys access right := by
        intro member
        have h := pathKeys_bounds right member
        omega
      simp only [Frontier, PathKeys]
      split_ifs
      · simp
      · simp only [List.length_append, List.length_cons, List.length_nil,
          Finset.card_insert_of_notMem notLeft, ihLeft]
        omega
      · simp only [List.length_append, List.length_cons, List.length_nil,
          Finset.card_insert_of_notMem notRight, ihRight]
        omega

theorem path_value_mem_frontier {n lo hi access key : ℕ} (snapshot : Snapshot n)
    (tree : BST lo hi) (upper : hi ≤ n) (member : key ∈ PathKeys access tree) :
    2*key+1 ∈ Frontier snapshot access tree upper := by
  induction tree with
  | empty => simp [PathKeys] at member
  | @node lo root hi left right ihLeft ihRight =>
      have hhi := right.lower_le_upper
      simp only [Frontier, PathKeys] at *
      split_ifs at member ⊢ with equal goLeft
      · simp only [Finset.mem_singleton] at member
        subst key
        simp
      · simp only [Finset.mem_insert] at member
        rcases member with rfl | member
        · simp
        · exact List.mem_append.mpr (Or.inl (ihLeft (by omega) member))
      · simp only [Finset.mem_insert] at member
        rcases member with rfl | member
        · simp
        · exact List.mem_append.mpr (Or.inr (ihRight upper member))

theorem searchGap_min_mem_frontier {n access innerLo innerHi lo hi : ℕ}
    (snapshot : Snapshot n) {inner : BST innerLo innerHi} {tree : BST lo hi}
    (gap : SearchGap access inner tree) (upper : hi ≤ n) (innerUpper : innerHi ≤ n) :
    (subtreeOwner snapshot inner innerUpper).val ∈ Frontier snapshot access tree upper := by
  induction gap with
  | leftGap left right outside =>
      simp only [Frontier]
      split_ifs with equal goLeft
      · simp
      · omega
      · simp
  | rightGap left right outside =>
      simp only [Frontier]
      split_ifs with equal goLeft
      · simp
      · simp
      · omega
  | left right direction inside ih =>
      simp only [Frontier, if_neg (ne_of_lt direction), if_pos direction]
      exact List.mem_append.mpr (Or.inl (ih (by have := right.lower_le_upper; omega) innerUpper))
  | right left direction inside ih =>
      simp only [Frontier, if_neg (ne_of_gt direction), if_neg (not_lt_of_gt direction)]
      exact List.mem_append.mpr (Or.inr (ih upper innerUpper))

def HasChild {n lo hi : ℕ} (snapshot : Snapshot n) (tree : BST lo hi)
    (upper : hi ≤ n) (depth : ℕ) (parent : External n) (child : ℕ) : Prop :=
  ∃ edge ∈ treeEdges snapshot tree upper depth,
    edge.owner = parent ∧ edge.child.val = child

theorem owner_eq_of_zero {n lo hi : ℕ} (snapshot : Snapshot n)
    (tree : BST lo hi) (upper : hi ≤ n) (record : External n)
    (zero : snapshot.rank record = 0)
    (inside : 2*lo ≤ record.val ∧ record.val ≤ 2*hi) :
    subtreeOwner snapshot tree upper = record := by
  apply (snapshot.intervalMin_unique _ _ _ _).symm
  refine ⟨inside.1, inside.2, ?_⟩
  intro other _ _
  rw [zero]
  exact Nat.zero_le _

theorem middle_min_value {n : ℕ} (snapshot : Snapshot n) (node : AtNode n) :
    (node.branchMin snapshot .middle).val = 2*node.root+1 :=
  node.branchMin_in_branch snapshot .middle

theorem local_child_iff {n : ℕ} (snapshot : Snapshot n) (node : AtNode n)
    (depth : ℕ) (record : External n) (owner : node.owner snapshot = record)
    (value : ℕ) :
    (∃ edge ∈ edgesAtNode snapshot node depth,
      edge.owner = record ∧ edge.child.val = value) ↔
      value ≠ record.val ∧
        (value = (node.branchMin snapshot .left).val ∨
         value = 2*node.root+1 ∨ value = (node.branchMin snapshot .right).val) := by
  classical
  constructor
  · rintro ⟨edge, member, parent, child⟩
    have valid := mem_edgesAtNode_valid snapshot node depth member
    have different : value ≠ record.val := by
      intro equal
      apply valid.child_ne_owner
      apply Fin.ext
      rw [parent, child, equal]
    refine ⟨different, ?_⟩
    have childEq := congrArg Fin.val valid.2.2.1
    rw [child] at childEq
    cases branchEq : edge.branch with
    | left => exact Or.inl (by simpa only [branchEq] using childEq)
    | middle =>
        rw [branchEq] at childEq
        exact Or.inr (Or.inl (childEq.trans (middle_min_value snapshot node)))
    | right => exact Or.inr (Or.inr (by simpa only [branchEq] using childEq))
  · rintro ⟨different, cases⟩
    have make : ∀ branch, value = (node.branchMin snapshot branch).val →
        ∃ edge ∈ edgesAtNode snapshot node depth,
          edge.owner = record ∧ edge.child.val = value := by
      intro branch valueEq
      have light : branch ≠ node.heavyBranch snapshot := by
        intro equal
        have heavy := node.owner_eq_branchMin_heavy snapshot
        rw [← equal, owner] at heavy
        exact different (valueEq.trans (congrArg Fin.val heavy.symm))
      refine ⟨edgeFor snapshot node depth branch, ?_, owner, valueEq.symm⟩
      exact List.mem_map.mpr ⟨branch,
        (mem_lightBranches_iff snapshot node branch).2 light, rfl⟩
    rcases cases with h | h | h
    · exact make .left h
    · exact make .middle (h.trans (middle_min_value snapshot node).symm)
    · exact make .right h

theorem hasChild_node_iff {n lo root hi : ℕ} (snapshot : Snapshot n)
    (left : BST lo root) (right : BST (root+1) hi) (upper : hi ≤ n)
    (depth : ℕ) (record : External n) (value : ℕ) :
    HasChild snapshot (.node left right) upper depth record value ↔
      (∃ edge ∈ edgesAtNode snapshot ⟨lo,root,hi,left,right,upper⟩ depth,
        edge.owner = record ∧ edge.child.val = value) ∨
      HasChild snapshot left (by have := right.lower_le_upper; omega) (depth+1) record value ∨
      HasChild snapshot right upper (depth+1) record value := by
  unfold HasChild
  change (∃ edge, edge ∈
      (edgesAtNode snapshot ⟨lo,root,hi,left,right,upper⟩ depth ++
       treeEdges snapshot left _ (depth+1) ++ treeEdges snapshot right upper (depth+1)) ∧
      edge.owner = record ∧ edge.child.val = value) ↔ _
  simp only [List.mem_append, or_and_right, exists_or, or_assoc]

theorem no_child_outside {n lo hi : ℕ} (snapshot : Snapshot n) (tree : BST lo hi)
    (upper : hi ≤ n) (depth : ℕ) (record : External n)
    (outside : record.val < 2*lo ∨ 2*hi < record.val) (value : ℕ) :
    ¬HasChild snapshot tree upper depth record value := by
  rintro ⟨edge, member, equal, _⟩
  have inside := mem_treeEdges_inside snapshot tree upper member
  rw [equal] at inside
  change 2*lo ≤ record.val ∧ record.val ≤ 2*hi ∧ _ at inside
  rcases outside with h | h <;> omega

private theorem left_frontier_logic (x y : ℕ) (P Q R : Prop) :
    ((x ≠ y ∧ (x = y ∨ Q ∨ R)) ∨ (P ∧ x ≠ y)) ↔
      (P ∨ Q ∨ R) ∧ x ≠ y := by tauto

private theorem right_frontier_logic (x y : ℕ) (P Q R : Prop) :
    ((x ≠ y ∧ (P ∨ Q ∨ x = y)) ∨ (R ∧ x ≠ y)) ↔
      (P ∨ Q ∨ R) ∧ x ≠ y := by tauto

/-- Exact pointwise frontier identity for an arbitrary refinement tree
and an actual zero-rank real access record. -/
theorem hasChild_iff_frontier {n lo hi access : ℕ} (snapshot : Snapshot n)
    (tree : BST lo hi) (upper : hi ≤ n) (depth : ℕ)
    (record : External n) (real : record.val = 2*access+1)
    (zero : snapshot.rank record = 0) (accessLo : lo ≤ access) (accessHi : access < hi)
    (value : ℕ) :
    HasChild snapshot tree upper depth record value ↔
      value ∈ Frontier snapshot access tree upper ∧ value ≠ record.val := by
  induction tree generalizing depth with
  | empty => omega
  | @node lo root hi left right ihLeft ihRight =>
      have hlo := left.lower_le_upper
      have hhi := right.lower_le_upper
      have rootUpper : root ≤ n := by omega
      let node : AtNode n := ⟨lo,root,hi,left,right,upper⟩
      have owner : node.owner snapshot = record :=
        owner_eq_of_zero snapshot (.node left right) upper record zero (by omega)
      rw [hasChild_node_iff]
      have localFact := local_child_iff snapshot node depth record owner value
      change (∃ edge ∈ edgesAtNode snapshot node depth,
        edge.owner = record ∧ edge.child.val = value) ↔ _ at localFact
      rw [localFact]
      change (value ≠ record.val ∧
        (value = (subtreeOwner snapshot left rootUpper).val ∨
          value = 2*root+1 ∨ value = (subtreeOwner snapshot right upper).val)) ∨
        HasChild snapshot left rootUpper (depth+1) record value ∨
        HasChild snapshot right upper (depth+1) record value ↔ _
      by_cases equal : access = root
      · have noLeft := no_child_outside snapshot left rootUpper (depth+1) record
          (Or.inr (by omega)) value
        have noRight := no_child_outside snapshot right upper (depth+1) record
          (Or.inl (by omega)) value
        simp only [Frontier, if_pos equal, List.mem_cons, List.not_mem_nil,
          noLeft, noRight, or_false]
        exact and_comm
      · by_cases goLeft : access < root
        · have leftOwner := owner_eq_of_zero snapshot left rootUpper record zero (by omega)
          have noRight := no_child_outside snapshot right upper (depth+1) record
            (Or.inl (by omega)) value
          rw [ihLeft rootUpper (depth+1) accessLo goLeft]
          simp only [Frontier, if_neg equal, if_pos goLeft, List.mem_append,
            List.mem_cons, List.not_mem_nil, noRight, or_false, leftOwner]
          exact left_frontier_logic _ _ _ _ _
        · have goRight : root < access := by omega
          have rightOwner := owner_eq_of_zero snapshot right upper record zero (by omega)
          have noLeft := no_child_outside snapshot left rootUpper (depth+1) record
            (Or.inr (by omega)) value
          rw [ihRight upper (depth+1) (by omega) accessHi]
          simp only [Frontier, if_neg equal, if_neg goLeft, List.mem_append,
            List.mem_cons, List.not_mem_nil, noLeft, false_or, or_false, or_assoc, rightOwner]
          exact right_frontier_logic _ _ _ _ _

open GreedyMerge.IntervalRootOracle GreedyMerge.PlateauBridge
open GreedyMerge.OrderedAtoms GreedyMerge.ExpansionRotations

theorem decomposition_path_card {n access : ℕ} {tree : BST 0 n}
    (p : Decomposition tree access) : (PathKeys access tree).card = p.count := by
  classical
  have imageEq : (Finset.range p.count).image p.separator = PathKeys access tree := by
    apply Finset.ext
    intro key
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact p.member i hi
    · intro member
      obtain ⟨i, hi, equal⟩ := p.complete key member
      exact ⟨i, hi, equal.symm⟩
  rw [← imageEq, Finset.card_image_of_injective _ p.increasing.injective, Finset.card_range]

theorem gap_owner_eq {n access i : ℕ} (comparator : BST 0 n) {tree : BST 0 n}
    (p : Decomposition tree access) (gapOwner : ℕ → ℕ) (_hi : i ≤ p.count)
    (minimum : UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (upper : p.separator i ≤ n) :
    (subtreeOwner (Snapshot.ofTree comparator) (p.gaps i) upper).val = gapOwner i := by
  let record : External n := ⟨gapOwner i, by have := minimum.1.2.1; omega⟩
  have spec : Splay.Rank.IsIntervalMin (Snapshot.ofTree comparator).rank
      (subtreeLower (p.gaps i) upper) (subtreeUpper (p.gaps i) upper) record := by
    refine ⟨minimum.1.1, minimum.1.2.1, ?_⟩
    intro other hl hu
    exact minimum.1.2.2 other.val hl hu
  have equal := (Snapshot.ofTree comparator).intervalMin_unique _ _
    (subtree_nonempty (p.gaps i) upper) spec
  exact (congrArg Fin.val equal).symm

theorem atom_owners_strict {rank separator gapOwner : ℕ → ℕ} {count first second : ℕ}
    (gaps : ∀ i, BST (GapLower 0 separator i) (separator i))
    (minima : ∀ i, i ≤ count → UniqueMin rank
      (2*GapLower 0 separator i) (2*separator i) (gapOwner i))
    (order : first < second) (bound : second < 2*count+1) :
    AtomOwner separator gapOwner first < AtomOwner separator gapOwner second := by
  have owners := gap_owners_are_atom_owners minima
  have cutOrder := cut_strictMono 0 separator gaps
  have firstInside := owner_inside_range cutOrder owners
    (lo := first) (hi := first) (Nat.le_refl first) (Nat.le_refl first) (by omega)
  have secondInside := owner_inside_range cutOrder owners
    (lo := second) (hi := second) (Nat.le_refl second) (Nat.le_refl second) bound
  have between := cutOrder.monotone (by omega : first+1 ≤ second)
  omega

/-- The recursive search frontier is exactly the ordered alternating atom
list of any actual search-path decomposition, including all original null gaps. -/
theorem frontier_eq_atoms {n access : ℕ} (comparator : BST 0 n) (tree : BST 0 n)
    (p : Decomposition tree access) (gapOwner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i)) :
    Frontier (Snapshot.ofTree comparator) access tree (Nat.le_refl n) =
      (List.range (2*p.count+1)).map (AtomOwner p.separator gapOwner) := by
  let atoms := (List.range (2*p.count+1)).map (AtomOwner p.separator gapOwner)
  have atomSorted : atoms.Pairwise (· < ·) := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range
    intro first second _ hs order
    exact atom_owners_strict p.gaps minima order (List.mem_range.mp hs)
  have included : atoms ⊆ Frontier (Snapshot.ofTree comparator) access tree (Nat.le_refl n) := by
    intro value member
    obtain ⟨atom, atomMem, rfl⟩ := List.mem_map.mp member
    have bound := List.mem_range.mp atomMem
    by_cases even : atom % 2 = 0
    · have equal : atom = 2*(atom/2) := by omega
      rw [equal, owner_even]
      have hi : atom/2 ≤ p.count := by omega
      have upper : p.separator (atom/2) ≤ n := by
        have h := p.increasing.monotone hi
        rwa [p.endpoint] at h
      rw [← gap_owner_eq comparator p gapOwner hi (minima _ hi) upper]
      exact searchGap_min_mem_frontier (Snapshot.ofTree comparator) (p.actualGap _ hi)
        (Nat.le_refl n) upper
    · have equal : atom = 2*(atom/2)+1 := by omega
      rw [equal, owner_odd]
      exact path_value_mem_frontier (Snapshot.ofTree comparator) tree (Nat.le_refl n)
        (p.member _ (by omega))
  have frontSorted := frontier_pairwise (access := access) (Snapshot.ofTree comparator) tree (Nat.le_refl n)
  have subperm := List.subperm_of_subset atomSorted.nodup included
  have sublist := List.sublist_of_subperm_of_pairwise subperm
    (atomSorted.imp fun h => le_of_lt h) (frontSorted.imp fun h => le_of_lt h)
  apply (List.Sublist.eq_of_length sublist _).symm
  simp only [atoms, List.length_map, List.length_range, frontier_length, decomposition_path_card p]

theorem comparator_zero_of_global {n access : ℕ} (comparator : BST 0 n)
    (global : GreedyMerge.Surface.UniqueGlobalMinimum comparator.depth n access) :
    comparator.externalDepth (2*access+1) = 0 := by
  rw [GreedyMerge.ValueNull.value_depth_eq]
  cases comparator with
  | empty => have h := global.1; omega
  | @node _ root _ left right =>
      by_cases equal : access = root
      · subst access
        exact depth_root left right
      · have bound := right.lower_le_upper
        have strict := global.2 root (by omega) (Ne.symm equal)
        rw [depth_root] at strict
        omega

/-- Actual old heap children are exactly the alternating separator/gap
records, with the requested root record excluded. No abstract frontier or
heap-shape premise is assumed. -/
theorem old_root_children_iff_atoms {n access : ℕ} (comparator tree : BST 0 n)
    (p : Decomposition tree access) (gapOwner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (global : GreedyMerge.Surface.UniqueGlobalMinimum comparator.depth n access)
    (record : External n) (real : record.val = 2*access+1) (value : ℕ) :
    HasChild (Snapshot.ofTree comparator) tree (Nat.le_refl n) 0 record value ↔
      value ∈ (List.range (2*p.count+1)).map (AtomOwner p.separator gapOwner) ∧
        value ≠ 2*access+1 := by
  have zero : (Snapshot.ofTree comparator).rank record = 0 := by
    change comparator.externalDepth record.val = 0
    rw [real]
    exact comparator_zero_of_global comparator global
  rw [hasChild_iff_frontier (Snapshot.ofTree comparator) tree (Nat.le_refl n) 0 record
    real zero (Nat.zero_le access) global.1 value,
    frontier_eq_atoms comparator tree p gapOwner minima, real]

end GreedyMerge.AccessFrontier

#print axioms GreedyMerge.AccessFrontier.hasChild_iff_frontier
#print axioms GreedyMerge.AccessFrontier.frontier_eq_atoms
#print axioms GreedyMerge.AccessFrontier.old_root_children_iff_atoms
