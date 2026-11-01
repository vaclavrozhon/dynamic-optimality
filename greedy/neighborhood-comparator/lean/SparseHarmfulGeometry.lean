import SparseActiveTree

/-!
Below-floor entry edges in the actual sparse retained-record BST.
The stronger induction includes an arbitrary external parent rank.
-/
namespace GreedyForest.ActiveTree.Sparse

def belowEntries (rank : ℕ → ℕ) (first finish base parentRank : ℕ) : Sparse → Finset ℕ
  | .empty => ∅
  | .node key left right =>
      (if first ≤ key ∧ key < finish ∧ parentRank < base then {key} else ∅) ∪
        belowEntries rank first finish base (rank key) left ∪
        belowEntries rank first finish base (rank key) right

theorem belowEntries_empty_of_outside (rank : ℕ → ℕ) (first finish base : ℕ)
    (tree : Sparse) (hoff : ∀ v ∈ tree.keys, ¬(first ≤ v ∧ v < finish))
    (parentRank : ℕ) : belowEntries rank first finish base parentRank tree = ∅ := by
  induction tree generalizing parentRank with
  | empty => rfl
  | node key left right ihLeft ihRight =>
      have hk := hoff key (root_mem _ _ _)
      have hl := ihLeft (by intro v hv; exact hoff v (by simp [keys,hv])) (rank key)
      have hr := ihRight (by intro v hv; exact hoff v (by simp [keys,hv])) (rank key)
      have hn : ¬(first ≤ key ∧ key < finish ∧ parentRank < base) := by
        intro h; exact hk ⟨h.1,h.2.1⟩
      simp only [belowEntries,if_neg hn,hl,hr,Finset.empty_union]

theorem belowEntries_empty_of_floor (rank : ℕ → ℕ) (first finish base : ℕ)
    (tree : Sparse) (hfloor : ∀ v ∈ tree.keys, base ≤ rank v)
    (parentRank : ℕ) (hp : base ≤ parentRank) :
    belowEntries rank first finish base parentRank tree = ∅ := by
  induction tree generalizing parentRank with
  | empty => rfl
  | node key left right ihLeft ihRight =>
      have hk := hfloor key (root_mem _ _ _)
      have hl := ihLeft (by intro v hv; exact hfloor v (by simp [keys,hv])) (rank key) hk
      have hr := ihRight (by intro v hv; exact hfloor v (by simp [keys,hv])) (rank key) hk
      have hn : ¬(first ≤ key ∧ key < finish ∧ parentRank < base) := by omega
      simp only [belowEntries,if_neg hn,hl,hr,Finset.empty_union]

/-- At most one actual active record in a contiguous source interval
can have a parent below the block's frozen rank floor. -/
theorem belowEntries_card_le_one (rank : ℕ → ℕ) (first finish base : ℕ)
    (tree : Sparse) (ho : Ordered tree) (hh : Heap rank tree)
    (hfloor : ∀ v ∈ tree.keys, first ≤ v → v < finish → base ≤ rank v)
    (parentRank : ℕ) : (belowEntries rank first finish base parentRank tree).card ≤ 1 := by
  induction tree generalizing parentRank with
  | empty => simp [belowEntries]
  | node key left right ihLeft ihRight =>
      have hfl : ∀ v ∈ left.keys, first ≤ v → v < finish → base ≤ rank v := by
        intro v hv; exact hfloor v (by simp [keys,hv])
      have hfr : ∀ v ∈ right.keys, first ≤ v → v < finish → base ≤ rank v := by
        intro v hv; exact hfloor v (by simp [keys,hv])
      by_cases hk : base ≤ rank key
      · have hl := belowEntries_empty_of_floor rank first finish base left
          (fun v hv => hk.trans (hh.2.2.1 v hv)) (rank key) hk
        have hr := belowEntries_empty_of_floor rank first finish base right
          (fun v hv => hk.trans (hh.2.2.2 v hv)) (rank key) hk
        simp only [belowEntries,hl,hr,Finset.union_empty]
        split <;> simp
      · have hout : ¬(first ≤ key ∧ key < finish) := by
          intro h; exact hk (hfloor key (root_mem _ _ _) h.1 h.2)
        have hnot : ¬(first ≤ key ∧ key < finish ∧ parentRank < base) := by
          intro h; exact hout ⟨h.1,h.2.1⟩
        by_cases hleft : key < first
        · have hempty := belowEntries_empty_of_outside rank first finish base left
            (by intro v hv; have := ho.2.2.1 v hv; omega) (rank key)
          have hr := ihRight ho.2.1 hh.2.1 hfr (rank key)
          simpa only [belowEntries,if_neg hnot,hempty,Finset.empty_union] using hr
        · have hright : finish ≤ key := by omega
          have hempty := belowEntries_empty_of_outside rank first finish base right
            (by intro v hv; have := ho.2.2.2 v hv; omega) (rank key)
          have hl := ihLeft ho.1 hh.1 hfl (rank key)
          simpa only [belowEntries,if_neg hnot,hempty,Finset.empty_union,
            Finset.union_empty] using hl

theorem belowEntries_of_edgeTo (rank : ℕ → ℕ) (first finish base : ℕ)
    (tree : Sparse) (parent child : ℕ) (he : (parent,child) ∈ tree.edgeTo parent)
    (hc : first ≤ child ∧ child < finish) (hp : rank parent < base) :
    child ∈ belowEntries rank first finish base (rank parent) tree := by
  cases tree with
  | empty => simp [edgeTo] at he
  | node key left right =>
      have heq : child = key := by simpa [edgeTo] using he
      subst child
      simp [belowEntries,hc,hp]

/-- Membership in the below-floor set is obtained from the literal
active-tree edge, with no projection assumption. -/
theorem belowEntries_of_edge (rank : ℕ → ℕ) (first finish base : ℕ)
    (tree : Sparse) (parent child : ℕ) (he : (parent,child) ∈ tree.edges)
    (hc : first ≤ child ∧ child < finish) (hp : rank parent < base)
    (parentRank : ℕ) : child ∈ belowEntries rank first finish base parentRank tree := by
  induction tree generalizing parentRank with
  | empty => simp [edges] at he
  | node key left right ihLeft ihRight =>
      simp only [edges,Finset.mem_union] at he
      rcases he with ((he | he) | he) | he
      · have h := ihLeft he (rank key)
        exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
      · have h := ihRight he (rank key)
        exact Finset.mem_union_right _ h
      · have hparent : parent = key := by
          cases left <;> simp_all [edgeTo]
        subst parent
        have h := belowEntries_of_edgeTo rank first finish base left key child he hc hp
        exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
      · have hparent : parent = key := by
          cases right <;> simp_all [edgeTo]
        subst parent
        have h := belowEntries_of_edgeTo rank first finish base right key child he hc hp
        exact Finset.mem_union_right _ h

end GreedyForest.ActiveTree.Sparse

#print axioms GreedyForest.ActiveTree.Sparse.belowEntries_card_le_one
