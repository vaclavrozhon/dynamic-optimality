import DynamicOptimality.GeometricOnlineSimulation.ClassIntervals
import DynamicOptimality.SearchRotationDepth
import Mathlib.Data.List.Sort

/-! # Ordering and change of height for represented intervals -/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR

namespace ClassFrame.Property

theorem key_bounds {system : SplitTreeSystem} {keyProperty : Nat → Prop}
    {holeProperty : Nat → Nat → ClassTree system → Prop}
    {lower upper : Nat} {skeleton : RawTree Nat} {frame : ClassFrame system skeleton}
    (valid : frame.Property keyProperty holeProperty lower upper) :
    ∀ key ∈ skeleton.inorder, lower ≤ key ∧ key < upper ∧ keyProperty key := by
  induction skeleton generalizing lower upper with
  | empty => simp [Tree.inorder]
  | node left root right ihl ihr =>
      cases frame with
      | node front _ back =>
          cases valid with
          | node rootLo rootHi first last rootProperty =>
              intro key member
              simp only [Tree.inorder, List.mem_append, List.mem_singleton] at member
              rcases member with (leftMember | rfl) | rightMember
              · obtain ⟨lo, hi, property⟩ := ihl first key leftMember
                exact ⟨lo, by omega, property⟩
              · exact ⟨rootLo, rootHi, rootProperty⟩
              · obtain ⟨lo, hi, property⟩ := ihr last key rightMember
                exact ⟨by omega, hi, property⟩

theorem ordered_skeleton {system : SplitTreeSystem} {keyProperty : Nat → Prop}
    {holeProperty : Nat → Nat → ClassTree system → Prop}
    {lower upper : Nat} {skeleton : RawTree Nat} {frame : ClassFrame system skeleton}
    (valid : frame.Property keyProperty holeProperty lower upper) : skeleton.Ordered := by
  induction skeleton generalizing lower upper with
  | empty => simp [Tree.Ordered, Tree.inorder]
  | node left root right ihl ihr =>
      cases frame with
      | node front _ back =>
          cases valid with
          | node rootLo rootHi first last rootProperty =>
              have firstOrdered := ihl first
              have lastOrdered := ihr last
              simp only [Tree.Ordered, Tree.inorder, List.pairwise_append, List.pairwise_singleton]
              refine ⟨⟨firstOrdered, trivial, ?_⟩, lastOrdered, ?_⟩
              · intro key member pivot pivotMember
                have equal : pivot = root := by simpa using pivotMember
                subst pivot
                exact (first.key_bounds key member).2.1
              · intro key member other otherMember
                have bound := (last.key_bounds other otherMember).1
                simp only [List.mem_append, List.mem_singleton] at member
                rcases member with firstMember | rfl
                · have := (first.key_bounds key firstMember).2.1
                  omega
                · omega

end ClassFrame.Property

mutual
  theorem ClassTree.Realizes.congr {system : SplitTreeSystem} {height changed : Nat → Int}
      {lower upper : Nat} {tree : ClassTree system}
      (valid : tree.Realizes height lower upper)
      (same : ∀ key, lower ≤ key → key < upper → changed key = height key) :
      tree.Realizes changed lower upper := by
    cases valid with
    | empty boundary => exact .empty _
    | node frameValid => exact .node (frameValid.congr same)
  termination_by structural tree

  theorem ClassFrame.Realizes.congr {system : SplitTreeSystem} {height changed : Nat → Int}
      {time : Int} {lower upper : Nat} {skeleton : RawTree Nat}
      {frame : ClassFrame system skeleton}
      (valid : frame.Realizes height time lower upper)
      (same : ∀ key, lower ≤ key → key < upper → changed key = height key) :
      frame.Realizes changed time lower upper := by
    cases valid with
    | hole treeValid older =>
        exact .hole (treeValid.congr same)
          (fun key lo hi => by rw [same key lo hi]; exact older key lo hi)
    | node lo hi first last atRoot =>
        refine .node lo hi (first.congr ?_) (last.congr ?_) ?_
        · intro key low high
          exact same key low (by omega)
        · intro key low high
          exact same key (by omega) high
        · exact (same _ lo hi).trans atRoot
  termination_by structural frame
end

mutual
  theorem ClassTree.Realizes.ordered {system : SplitTreeSystem} {height : Nat → Int}
      {lower upper : Nat} {tree : ClassTree system}
      (valid : tree.Realizes height lower upper) : tree.tree.Ordered := by
    cases valid with
    | empty boundary => simp [ClassTree.tree, Tree.Ordered, Tree.inorder]
    | node frameValid => exact frameValid.ordered
  termination_by structural tree

  theorem ClassFrame.Realizes.ordered {system : SplitTreeSystem} {height : Nat → Int}
      {time : Int} {lower upper : Nat} {skeleton : RawTree Nat}
      {frame : ClassFrame system skeleton}
      (valid : frame.Realizes height time lower upper) : frame.tree.Ordered := by
    cases valid with
    | hole treeValid older => exact treeValid.ordered
    | node lo hi first last atRoot =>
        have firstOrdered := first.ordered
        have lastOrdered := last.ordered
        simp only [ClassFrame.tree, Tree.Ordered, Tree.inorder,
          List.pairwise_append, List.pairwise_singleton]
        refine ⟨⟨firstOrdered, trivial, ?_⟩, lastOrdered, ?_⟩
        · intro key member pivot pivotMember
          simp only [List.mem_singleton] at pivotMember
          subst pivot
          exact ((first.interval.2 key).mp member).2
        · intro key member other otherMember
          have bound := ((last.interval.2 other).mp otherMember).1
          simp only [List.mem_append, List.mem_singleton] at member
          rcases member with firstMember | rfl
          · have := ((first.interval.2 key).mp firstMember).2
            omega
          · omega
  termination_by structural frame
end

/-- The physical BST uses exactly the original ranked keys. -/
theorem ClassTree.Realizes.full_inorder {system : SplitTreeSystem} {height : Nat → Int}
    {n : Nat} {tree : ClassTree system} (valid : tree.Realizes height 0 n) :
    tree.tree.inorder = List.range n := by
  apply valid.ordered.eq_of_mem_iff (List.pairwise_lt_range (n := n))
  intro key
  simpa only [List.mem_range, Nat.zero_le, true_and] using valid.interval.2 key

end DynamicOptimality.GeometricOnlineSimulation
