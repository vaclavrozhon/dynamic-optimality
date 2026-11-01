import CanonicalActiveSplay
import Splay.Tree.SubtreeAt

/-! A value-key minimum of a literal subtree is one of its active canonical
representatives. This connects off-path subtree minima to the active set. -/

namespace Splay.Research.CanonicalActive

open Splay.Rank Splay.Tree Splay.Tree.BST Splay.Lazy.Canonical

theorem mem_activeFrom_bounds {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) {key : Fin n}
    (member : key ∈ activeFrom snapshot tree upper_le_n) :
    lower ≤ key.val ∧ key.val < upper := by
  induction tree with
  | empty boundary => simp [activeFrom] at member
  | @node lower root upper left right ihLeft ihRight =>
      have leftBound := left.lower_le_upper
      have rightBound := right.lower_le_upper
      simp only [activeFrom, Finset.mem_union] at member
      rcases member with head | leftMember | rightMember
      · unfold activeAt at head
        split_ifs at head with middle
        · simp only [Finset.mem_singleton] at head
          have equal : key.val = root := congrArg Fin.val head
          omega
        · simp at head
      · have bounds := ihLeft (by omega) leftMember
        omega
      · have bounds := ihRight upper_le_n rightMember
        omega

theorem subtreeAt_active_subset {n innerLower innerUpper lower upper depth : ℕ}
    (snapshot : Snapshot n) {inner : BST innerLower innerUpper} {tree : BST lower upper}
    (occurrence : SubtreeAt inner depth tree) (upper_le_n : upper ≤ n) :
    activeFrom snapshot inner (le_trans occurrence.bounds.2 upper_le_n) ⊆
      activeFrom snapshot tree upper_le_n := by
  induction occurrence with
  | here => exact le_refl _
  | left occurrence right ih =>
      have included := ih (by have := right.lower_le_upper; omega)
      intro key member
      simp only [activeFrom, Finset.mem_union]
      exact Or.inr (Or.inl (included member))
  | right left occurrence ih =>
      intro key member
      simp only [activeFrom, Finset.mem_union]
      exact Or.inr (Or.inr (ih upper_le_n member))

theorem mem_activeAt_eq_key {n : ℕ} {key root : Fin n} {branch : TernaryBranch}
    (member : key ∈ activeAt root branch) : key = root := by
  unfold activeAt at member
  split_ifs at member
  · exact Finset.mem_singleton.mp member
  · simp at member

/-- Activity of keys inside a literal subtree is independent of its context. -/
theorem subtreeAt_active_iff {n innerLower innerUpper lower upper depth : ℕ}
    (snapshot : Snapshot n) {inner : BST innerLower innerUpper} {tree : BST lower upper}
    (occurrence : SubtreeAt inner depth tree) (upper_le_n : upper ≤ n) (key : Fin n)
    (insideLower : innerLower ≤ key.val) (insideUpper : key.val < innerUpper) :
    key ∈ activeFrom snapshot tree upper_le_n ↔
      key ∈ activeFrom snapshot inner (le_trans occurrence.bounds.2 upper_le_n) := by
  induction occurrence with
  | here => rfl
  | @left lower root upper depth leftTree occurrence right ih =>
      have inside := occurrence.bounds
      have keyLeft : key.val < root := by omega
      have headImpossible : key ∉ activeAt ⟨root, by have := right.lower_le_upper; omega⟩
          (({ lower, root, upper, left := leftTree, right, upper_le_n } : AtNode n).heavyBranch snapshot) := by
        intro member
        have equal := congrArg Fin.val (mem_activeAt_eq_key member)
        dsimp only at equal
        omega
      have rightImpossible : key ∉ activeFrom snapshot right upper_le_n := by
        intro member
        have bounds := mem_activeFrom_bounds snapshot right upper_le_n member
        omega
      simpa only [activeFrom, Finset.mem_union, headImpossible, rightImpossible,
        false_or, or_false] using ih (by have := right.lower_le_upper; omega)
  | @right lower root upper depth left rightTree occurrence ih =>
      have inside := occurrence.bounds
      have keyRight : root < key.val := by omega
      have headImpossible : key ∉ activeAt ⟨root, by have := rightTree.lower_le_upper; omega⟩
          (({ lower, root, upper, left, right := rightTree, upper_le_n } : AtNode n).heavyBranch snapshot) := by
        intro member
        have equal := congrArg Fin.val (mem_activeAt_eq_key member)
        dsimp only at equal
        omega
      have leftImpossible : key ∉ activeFrom snapshot left (by have := rightTree.lower_le_upper; omega) := by
        intro member
        have bounds := mem_activeFrom_bounds snapshot left _ member
        omega
      simpa only [activeFrom, Finset.mem_union, headImpossible, leftImpossible,
        false_or] using ih upper_le_n

theorem root_mem_activeFrom_iff {n : ℕ} (snapshot : Snapshot n) (node : AtNode n) :
    (⟨node.root, lt_of_lt_of_le node.root_lt_upper node.upper_le_n⟩ : Fin n) ∈
      activeFrom snapshot (.node node.left node.right) node.upper_le_n ↔
        node.heavyBranch snapshot = .middle := by
  simp only [activeFrom, Finset.mem_union]
  have notLeft : (⟨node.root, lt_of_lt_of_le node.root_lt_upper node.upper_le_n⟩ : Fin n) ∉
      activeFrom snapshot node.left (le_trans (Nat.le_of_lt node.root_lt_upper) node.upper_le_n) := by
    intro member
    have bounds := mem_activeFrom_bounds snapshot node.left _ member
    dsimp only at bounds
    omega
  have notRight : (⟨node.root, lt_of_lt_of_le node.root_lt_upper node.upper_le_n⟩ : Fin n) ∉
      activeFrom snapshot node.right node.upper_le_n := by
    intro member
    have bounds := mem_activeFrom_bounds snapshot node.right _ member
    dsimp only at bounds
    omega
  simp only [notLeft, notRight, or_false]
  change _ ∈ activeAt _ (node.heavyBranch snapshot) ↔ _
  unfold activeAt
  split_ifs <;> simp_all

/-- A proper ancestor of the rank-zero query is not an active key. -/
theorem proper_query_ancestor_not_active {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    (insideLower : node.lower ≤ key.val) (insideUpper : key.val < node.upper)
    (different : node.root ≠ key.val) :
    (⟨node.root, lt_of_lt_of_le node.root_lt_upper node.upper_le_n⟩ : Fin n) ∉
      activeFrom snapshot (.node node.left node.right) node.upper_le_n := by
  rw [root_mem_activeFrom_iff]
  intro middle
  have head := activeAt_of_zero snapshot node key rankZero insideLower insideUpper
  simp [middle, different, activeAt] at head

theorem minimum_key_mem_activeFrom {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) (key : Fin n)
    (insideLower : lower ≤ key.val) (insideUpper : key.val < upper)
    (minimal : ∀ position : External n, 2*lower ≤ position.val → position.val ≤ 2*upper →
      snapshot.rank (valuePos key) ≤ snapshot.rank position) :
    key ∈ activeFrom snapshot tree upper_le_n := by
  induction tree with
  | empty boundary => omega
  | @node lower root upper left right ihLeft ihRight =>
      have leftBound := left.lower_le_upper
      have rightBound := right.lower_le_upper
      let node : AtNode n := { lower, root, upper, left, right, upper_le_n }
      simp only [activeFrom, Finset.mem_union]
      by_cases equal : key.val = root
      · left
        have heavy : node.heavyBranch snapshot = .middle := by
          apply Eq.symm
          apply snapshot.heavyBranch_unique
          refine ⟨valuePos key, ⟨?_, ?_, ?_⟩, ?_⟩
          · change 2*lower ≤ 2*key.val+1
            omega
          · change 2*key.val+1 ≤ 2*upper
            omega
          · intro position lo hi
            exact minimal position lo hi
          · change 2*key.val+1 = 2*root+1
            omega
        change key ∈ activeAt ⟨root, _⟩ (node.heavyBranch snapshot)
        simp only [heavy, activeAt, ite_true, Finset.mem_singleton]
        apply Fin.ext
        exact equal
      · right
        by_cases onLeft : key.val < root
        · left
          apply ihLeft (by omega) insideLower onLeft
          intro position lo hi
          exact minimal position lo (by omega)
        · right
          apply ihRight upper_le_n (by omega) insideUpper
          intro position lo hi
          exact minimal position (by omega) hi

theorem owner_key_mem_activeFrom {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) (key : Fin n) (owner : node.owner snapshot = valuePos key) :
    key ∈ activeFrom snapshot (.node node.left node.right) node.upper_le_n := by
  have minimum := node.owner_isMin snapshot
  rw [owner] at minimum
  have lo : 2*node.lower ≤ 2*key.val+1 := minimum.1
  have hi : 2*key.val+1 ≤ 2*node.upper := minimum.2.1
  apply minimum_key_mem_activeFrom snapshot _ node.upper_le_n key (by omega) (by omega)
  exact minimum.2.2

/-- A nonempty interval of whole keys has a value-key depth minimum; a null
cannot be its representative. The comparison BST is completely arbitrary. -/
theorem exists_key_depth_minimum {treeLower treeUpper : ℕ}
    (comparison : BST treeLower treeUpper) {lower upper : ℕ}
    (insideLower : treeLower ≤ lower) (nonempty : lower < upper)
    (insideUpper : upper ≤ treeUpper) :
    ∃ key, lower ≤ key ∧ key < upper ∧
      ∀ position, 2*lower ≤ position → position ≤ 2*upper →
        comparison.externalDepth (2*key+1) ≤ comparison.externalDepth position := by
  induction comparison with
  | empty boundary => omega
  | @node treeLower root treeUpper left right ihLeft ihRight =>
      by_cases onLeft : upper ≤ root
      · obtain ⟨key, keyLower, keyUpper, minimal⟩ := ihLeft insideLower onLeft
        refine ⟨key, keyLower, keyUpper, ?_⟩
        intro position lo hi
        rw [externalDepth_node_of_lt_root left right (by omega),
          externalDepth_node_of_lt_root left right (by omega)]
        exact Nat.succ_le_succ (minimal position lo hi)
      · by_cases onRight : root < lower
        · obtain ⟨key, keyLower, keyUpper, minimal⟩ := ihRight (by omega) insideUpper
          refine ⟨key, keyLower, keyUpper, ?_⟩
          intro position lo hi
          rw [externalDepth_node_of_root_lt left right (by omega),
            externalDepth_node_of_root_lt left right (by omega)]
          exact Nat.succ_le_succ (minimal position lo hi)
        · refine ⟨root, by omega, by omega, ?_⟩
          intro position lo hi
          simp only [externalDepth_root]
          exact Nat.zero_le _

theorem comparison_owner_is_active {n : ℕ} (comparison : BST 0 n) (node : AtNode n) :
    ∃ key : Fin n, node.owner (Snapshot.ofTree comparison) = valuePos key ∧
      key ∈ activeFrom (Snapshot.ofTree comparison) (.node node.left node.right) node.upper_le_n := by
  obtain ⟨rawKey, lowerBound, upperBound, minimal⟩ := exists_key_depth_minimum comparison
    (Nat.zero_le node.lower) (lt_of_le_of_lt node.lower_le_root node.root_lt_upper) node.upper_le_n
  let key : Fin n := ⟨rawKey, lt_of_lt_of_le upperBound node.upper_le_n⟩
  have candidate : Splay.Rank.IsIntervalMin (Snapshot.ofTree comparison).rank
      node.wholeLower node.wholeUpper (valuePos key) := by
    refine ⟨?_, ?_, ?_⟩
    · change 2*node.lower ≤ 2*rawKey+1
      omega
    · change 2*rawKey+1 ≤ 2*node.upper
      omega
    · intro position lo hi
      exact minimal position.val lo hi
  have owner : node.owner (Snapshot.ofTree comparison) = valuePos key :=
    ((Snapshot.ofTree comparison).intervalMin_unique
      node.wholeLower node.wholeUpper node.whole_nonempty candidate).symm
  exact ⟨key, owner, owner_key_mem_activeFrom _ node key owner⟩

end Splay.Research.CanonicalActive

#print axioms Splay.Research.CanonicalActive.minimum_key_mem_activeFrom
#print axioms Splay.Research.CanonicalActive.owner_key_mem_activeFrom
#print axioms Splay.Research.CanonicalActive.proper_query_ancestor_not_active
#print axioms Splay.Research.CanonicalActive.comparison_owner_is_active
#print axioms Splay.Research.CanonicalActive.subtreeAt_active_iff
