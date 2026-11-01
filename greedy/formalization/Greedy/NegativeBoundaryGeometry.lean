import SparseActiveTree

/-!
# Exceptional active entrances into a source interval

An incoming boundary edge enters the source interval from an outside
winner. It is unsafe if that winner's own parent has rank below the
source base. A virtual parent of rank `-1` includes the surviving root.
There is at most one unsafe active entrance: before first reaching the
interval the search stays in one branch; after reaching it, all ancestor
ranks are at least the base. This implies the manuscript's looser
two-endpoint allowance.
-/

namespace Greedy.NegativeBoundaryGeometry

open GreedyForest.ActiveTree

def Inside (first finish key : ℕ) : Prop := first ≤ key ∧ key < finish

instance (first finish key : ℕ) : Decidable (Inside first finish key) :=
  inferInstanceAs (Decidable (_ ∧ _))

def unsafeTo (first finish base parent : ℕ) (parentRank : ℤ) : Sparse → Finset (ℕ × ℕ)
  | .empty => ∅
  | .node child _ _ =>
      if parentRank < (base : ℤ) ∧ ¬ Inside first finish parent ∧ Inside first finish child
        then {(parent, child)} else ∅

def unsafeEdges (rank : ℕ → ℕ) (first finish base : ℕ) (parentRank : ℤ) : Sparse → Finset (ℕ × ℕ)
  | .empty => ∅
  | .node key left right =>
      unsafeEdges rank first finish base (rank key) left ∪
      unsafeEdges rank first finish base (rank key) right ∪
      unsafeTo first finish base key parentRank left ∪
      unsafeTo first finish base key parentRank right

theorem unsafeTo_empty_of_outside (first finish base parent : ℕ) (parentRank : ℤ) (tree : Sparse)
    (outside : ∀ key ∈ tree.keys, ¬ Inside first finish key) :
    unsafeTo first finish base parent parentRank tree = ∅ := by
  cases tree with
  | empty => rfl
  | node key left right =>
      have out := outside key (Sparse.root_mem _ _ _)
      simp [unsafeTo, out]

theorem empty_of_outside (rank : ℕ → ℕ) (first finish base : ℕ) (tree : Sparse)
    (outside : ∀ key ∈ tree.keys, ¬ Inside first finish key) (parentRank : ℤ) :
    unsafeEdges rank first finish base parentRank tree = ∅ := by
  induction tree generalizing parentRank with
  | empty => rfl
  | node key left right il ir =>
      have ol : ∀ v ∈ left.keys, ¬ Inside first finish v := by
        intro v member; exact outside v (by simp [Sparse.keys, member])
      have or : ∀ v ∈ right.keys, ¬ Inside first finish v := by
        intro v member; exact outside v (by simp [Sparse.keys, member])
      rw [unsafeEdges, il ol, ir or, unsafeTo_empty_of_outside _ _ _ _ _ _ ol,
        unsafeTo_empty_of_outside _ _ _ _ _ _ or]
      simp

theorem unsafeTo_empty_of_floor (first finish base parent : ℕ) (parentRank : ℤ) (tree : Sparse)
    (floor : (base : ℤ) ≤ parentRank) : unsafeTo first finish base parent parentRank tree = ∅ := by
  cases tree <;> simp [unsafeTo, not_lt.mpr floor]

theorem empty_of_floor (rank : ℕ → ℕ) (first finish base : ℕ) (tree : Sparse)
    (floor : ∀ key ∈ tree.keys, base ≤ rank key) (parentRank : ℤ)
    (parentFloor : (base : ℤ) ≤ parentRank) :
    unsafeEdges rank first finish base parentRank tree = ∅ := by
  induction tree generalizing parentRank with
  | empty => rfl
  | node key left right il ir =>
      have rootFloor := floor key (Sparse.root_mem _ _ _)
      have leftFloor : ∀ v ∈ left.keys, base ≤ rank v := by
        intro v member; exact floor v (by simp [Sparse.keys, member])
      have rightFloor : ∀ v ∈ right.keys, base ≤ rank v := by
        intro v member; exact floor v (by simp [Sparse.keys, member])
      rw [unsafeEdges, il leftFloor _ (by exact_mod_cast rootFloor),
        ir rightFloor _ (by exact_mod_cast rootFloor),
        unsafeTo_empty_of_floor _ _ _ _ _ _ parentFloor,
        unsafeTo_empty_of_floor _ _ _ _ _ _ parentFloor]
      simp

theorem empty_of_inside (rank : ℕ → ℕ) (first finish base key : ℕ) (left right : Sparse)
    (heap : (Sparse.node key left right).Heap rank) (inside : Inside first finish key)
    (floor : base ≤ rank key) (parentRank : ℤ) :
    unsafeEdges rank first finish base parentRank (.node key left right) = ∅ := by
  have leftZero := empty_of_floor rank first finish base left
    (fun v member => floor.trans (heap.2.2.1 v member)) (rank key) (by exact_mod_cast floor)
  have rightZero := empty_of_floor rank first finish base right
    (fun v member => floor.trans (heap.2.2.2 v member)) (rank key) (by exact_mod_cast floor)
  have toLeft : unsafeTo first finish base key parentRank left = ∅ := by
    cases left <;> simp [unsafeTo, inside]
  have toRight : unsafeTo first finish base key parentRank right = ∅ := by
    cases right <;> simp [unsafeTo, inside]
  simp only [unsafeEdges, leftZero, rightZero, toLeft, toRight, Finset.union_self]

theorem unsafe_card_le_one (rank : ℕ → ℕ) (first finish base : ℕ) (tree : Sparse)
    (ordered : tree.Ordered) (heap : tree.Heap rank)
    (floor : ∀ key ∈ tree.keys, Inside first finish key → base ≤ rank key)
    (parentRank : ℤ) : (unsafeEdges rank first finish base parentRank tree).card ≤ 1 := by
  induction tree generalizing parentRank with
  | empty => simp [unsafeEdges]
  | node key left right il ir =>
      have fl : ∀ v ∈ left.keys, Inside first finish v → base ≤ rank v := by
        intro v member; exact floor v (by simp [Sparse.keys, member])
      have fr : ∀ v ∈ right.keys, Inside first finish v → base ≤ rank v := by
        intro v member; exact floor v (by simp [Sparse.keys, member])
      by_cases inside : Inside first finish key
      · rw [empty_of_inside rank first finish base key left right heap inside
          (floor key (Sparse.root_mem _ _ _) inside) parentRank]
        simp
      · by_cases below : key < first
        · have outside : ∀ v ∈ left.keys, ¬ Inside first finish v := by
            intro v member
            have lt := ordered.2.2.1 v member
            unfold Inside
            omega
          rw [unsafeEdges, empty_of_outside rank first finish base left outside,
            unsafeTo_empty_of_outside first finish base key parentRank left outside]
          simp only [Finset.empty_union, Finset.union_empty]
          cases right with
          | empty => simp [unsafeEdges, unsafeTo]
          | node child l r =>
              by_cases childInside : Inside first finish child
              · rw [empty_of_inside rank first finish base child l r heap.2.1 childInside
                  (fr child (Sparse.root_mem _ _ _) childInside)]
                simp only [Finset.empty_union, unsafeTo]
                split_ifs <;> simp
              · have bound := ir ordered.2.1 heap.2.1 fr (rank key)
                simpa [unsafeTo, childInside] using bound
        · have above : finish ≤ key := by unfold Inside at inside; omega
          have outside : ∀ v ∈ right.keys, ¬ Inside first finish v := by
            intro v member
            have lt := ordered.2.2.2 v member
            unfold Inside
            omega
          rw [unsafeEdges, empty_of_outside rank first finish base right outside,
            unsafeTo_empty_of_outside first finish base key parentRank right outside]
          simp only [Finset.union_empty]
          cases left with
          | empty => simp [unsafeEdges, unsafeTo]
          | node child l r =>
              by_cases childInside : Inside first finish child
              · rw [empty_of_inside rank first finish base child l r heap.1 childInside
                  (fl child (Sparse.root_mem _ _ _) childInside)]
                simp only [Finset.empty_union, unsafeTo]
                split_ifs <;> simp
              · have bound := il ordered.1 heap.1 fl (rank key)
                simpa [unsafeTo, childInside] using bound

end Greedy.NegativeBoundaryGeometry
