import DynamicOptimality.GeometricOnlineSimulation.ClassProperties

/-! # The initial equal-time class on the original key universe -/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR

/-- No old class hangs below the initial skeleton. -/
def ClassFrame.blank (system : SplitTreeSystem) :
    (skeleton : RawTree Nat) → ClassFrame system skeleton
  | .empty => .hole .empty
  | .node left key right => .node (blank system left) key (blank system right)

@[simp] theorem ClassFrame.blank_tree (system : SplitTreeSystem) (skeleton : RawTree Nat) :
    (blank system skeleton).tree = skeleton := by
  induction skeleton with
  | empty => rfl
  | node left key right ihl ihr => simp [blank, tree, ihl, ihr]

@[simp] theorem ClassFrame.blank_credit (system : SplitTreeSystem) (skeleton : RawTree Nat) :
    (blank system skeleton).credit = 0 := by
  induction skeleton with
  | empty => rfl
  | node left key right ihl ihr => simp [blank, credit, ihl, ihr]

theorem ClassFrame.blank_realizes (system : SplitTreeSystem) (time : Int)
    {lower upper : Nat} (skeleton : RawTree Nat) (ordered : skeleton.Ordered)
    (interval : Interval skeleton lower upper) :
    (blank system skeleton).Realizes (fun _ => time) time lower upper := by
  induction skeleton generalizing lower upper with
  | empty =>
      have same : lower = upper := by
        have bound := interval.1
        have notLt : ¬ lower < upper := by
          intro lt
          have member := (interval.2 lower).mpr ⟨Nat.le_refl _, lt⟩
          simpa only [Tree.inorder, List.not_mem_nil] using member
        omega
      subst upper
      exact .hole (.empty lower) (by intro key lo hi; omega)
  | node left root right ihl ihr =>
      have rootBounds := (interval.2 root).mp (by simp [Tree.inorder])
      obtain ⟨leftOrdered, rightOrdered, leftKeys, rightKeys⟩ :=
        SearchRotation.RawDepth.node_parts ordered
      have leftInterval : Interval left lower root := by
        refine ⟨rootBounds.1, ?_⟩
        intro key
        constructor
        · intro member
          have whole := (interval.2 key).mp (by simp [Tree.inorder, member])
          exact ⟨whole.1, leftKeys key member⟩
        · intro ⟨lo, hi⟩
          have member := (interval.2 key).mpr ⟨lo, by omega⟩
          simp only [Tree.inorder, List.mem_append, List.mem_singleton] at member
          rcases member with (first | equal) | last
          · exact first
          · omega
          · have := rightKeys key last
            omega
      have rightInterval : Interval right (root+1) upper := by
        refine ⟨by omega, ?_⟩
        intro key
        constructor
        · intro member
          have whole := (interval.2 key).mp (by simp [Tree.inorder, member])
          have := rightKeys key member
          exact ⟨by omega, whole.2⟩
        · intro ⟨lo, hi⟩
          have member := (interval.2 key).mpr ⟨by omega, hi⟩
          simp only [Tree.inorder, List.mem_append, List.mem_singleton] at member
          rcases member with (first | equal) | last
          · have := leftKeys key first
            omega
          · omega
          · exact last
      exact .node rootBounds.1 rootBounds.2
        (ihl leftOrdered leftInterval) (ihr rightOrdered rightInterval) rfl

/-- Initial representation with at most `K` credits per original key. -/
theorem exists_initial_class (system : SplitTreeSystem) (n : Nat) (time : Int) :
    ∃ tree : ClassTree system, tree.Realizes (fun _ => time) 0 n ∧
      tree.credit ≤ system.K*n := by
  by_cases zero : n = 0
  · subst n
    exact ⟨.empty, .empty 0, by simp [ClassTree.credit]⟩
  · let state := system.setup (List.range n)
    have keys : (system.tree state).inorder = List.range n := system.setup_keys _
    have nonempty : system.tree state ≠ .empty := by
      intro empty
      have sizes := congrArg List.length keys
      simp only [empty, Tree.inorder, List.length_nil, List.length_range] at sizes
      omega
    have ordered : (system.tree state).Ordered := by
      rw [Tree.Ordered, keys]
      exact List.pairwise_lt_range
    have interval : Interval (system.tree state) 0 n := by
      refine ⟨Nat.zero_le _, ?_⟩
      intro key
      simp only [keys, List.mem_range, Nat.zero_le, true_and]
    refine ⟨.node time state nonempty (ClassFrame.blank system _),
      .node (ClassFrame.blank_realizes system time _ ordered interval), ?_⟩
    simpa only [ClassTree.credit, ClassFrame.blank_credit, Nat.add_zero,
      List.length_range] using system.setup_credit (List.range n)

end DynamicOptimality.GeometricOnlineSimulation
