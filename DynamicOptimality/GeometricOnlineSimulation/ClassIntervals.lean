import DynamicOptimality.GeometricOnlineSimulation.ClassFrameProperty
import GeometricGreedy

/-! # Complete intervals and the visible keys of a highest class -/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR

/-- Every key of an interval occurs, and no key outside it occurs. -/
def Interval (tree : RawTree Nat) (lower upper : Nat) : Prop :=
  lower ≤ upper ∧ ∀ key, key ∈ tree.inorder ↔ lower ≤ key ∧ key < upper

mutual
  theorem ClassTree.Realizes.interval {system : SplitTreeSystem} {height : Nat → Int}
      {lower upper : Nat} {tree : ClassTree system}
      (valid : tree.Realizes height lower upper) : Interval tree.tree lower upper := by
    cases valid with
    | empty boundary => simp [ClassTree.tree, Interval, Tree.inorder]
    | node frameValid => exact frameValid.interval
  termination_by structural tree

  theorem ClassFrame.Realizes.interval {system : SplitTreeSystem} {height : Nat → Int}
      {time : Int} {lower upper : Nat} {skeleton : RawTree Nat}
      {frame : ClassFrame system skeleton}
      (valid : frame.Realizes height time lower upper) : Interval frame.tree lower upper := by
    cases valid with
    | hole treeValid older => exact treeValid.interval
    | node lowerBound upperBound first last sameTime =>
        obtain ⟨firstBounds, firstKeys⟩ := first.interval
        obtain ⟨lastBounds, lastKeys⟩ := last.interval
        refine ⟨by omega, ?_⟩
        intro key
        simp only [ClassFrame.tree, Tree.inorder, List.mem_append, List.mem_singleton,
          firstKeys, lastKeys]
        omega
  termination_by structural frame
end

namespace ClassFrame.Realizes

theorem key_height {system : SplitTreeSystem} {height : Nat → Int} {time : Int}
    {lower upper : Nat} {skeleton : RawTree Nat} {frame : ClassFrame system skeleton}
    (valid : frame.Realizes height time lower upper) :
    ∀ key ∈ skeleton.inorder, lower ≤ key ∧ key < upper ∧ height key = time := by
  induction skeleton generalizing lower upper with
  | empty => simp [Tree.inorder]
  | node left root right ihl ihr =>
      cases frame with
      | node front _ back =>
          cases valid with
          | node rootLo rootHi first last sameTime =>
              intro key member
              simp only [Tree.inorder, List.mem_append, List.mem_singleton] at member
              rcases member with (leftMember | rfl) | rightMember
              · obtain ⟨lo, hi, same⟩ := ihl first key leftMember
                exact ⟨lo, by omega, same⟩
              · exact ⟨rootLo, rootHi, sameTime⟩
              · obtain ⟨lo, hi, same⟩ := ihr last key rightMember
                exact ⟨by omega, hi, same⟩

theorem height_le {system : SplitTreeSystem} {height : Nat → Int} {time : Int}
    {lower upper : Nat} {skeleton : RawTree Nat} {frame : ClassFrame system skeleton}
    (valid : frame.Realizes height time lower upper) :
    ∀ key, lower ≤ key → key < upper → height key ≤ time := by
  induction skeleton generalizing lower upper with
  | empty =>
      cases frame with
      | hole child => cases valid with
        | hole childValid older => exact fun key lo hi => le_of_lt (older key lo hi)
  | node left root right ihl ihr =>
      cases frame with
      | node front _ back =>
          cases valid with
          | node rootLo rootHi first last sameTime =>
              intro key lo hi
              rcases lt_trichotomy key root with before | rfl | after
              · exact ihl first key lo before
              · exact le_of_eq sameTime
              · exact ihr last key (by omega) hi

theorem maximal_mem {system : SplitTreeSystem} {height : Nat → Int} {time : Int}
    {lower upper : Nat} {skeleton : RawTree Nat} {frame : ClassFrame system skeleton}
    (valid : frame.Realizes height time lower upper)
    {key : Nat} (lo : lower ≤ key) (hi : key < upper) (same : height key = time) :
    key ∈ skeleton.inorder := by
  induction skeleton generalizing lower upper with
  | empty =>
      cases frame with
      | hole child => cases valid with
        | hole childValid older => have := older key lo hi; omega
  | node left root right ihl ihr =>
      cases frame with
      | node front _ back =>
          cases valid with
          | node rootLo rootHi first last sameTime =>
              simp only [Tree.inorder, List.mem_append, List.mem_singleton]
              rcases lt_trichotomy key root with before | rfl | after
              · exact Or.inl (Or.inl (ihl first lo before))
              · exact Or.inl (Or.inr rfl)
              · exact Or.inr (ihr last (by omega) hi)

/-- If a satisfying row touches the represented interval, it touches a
key of its highest class. This is the causal geometric closure property. -/
theorem row_hits_class {system : SplitTreeSystem} {height : Nat → Int} {time : Int}
    {n lower upper : Nat} {skeleton : RawTree Nat} {frame : ClassFrame system skeleton}
    (valid : frame.Realizes height time lower upper) (nonempty : skeleton ≠ .empty)
    (inside : upper ≤ n) {row : Finset Nat}
    (satisfies : GreedyMerge.Geometry.RowSatisfies height n row)
    {access : Nat} (requested : access ∈ row) (lo : lower ≤ access) (hi : access < upper) :
    ∃ key ∈ skeleton.inorder, key ∈ row := by
  have rootExists : ∃ root, root ∈ skeleton.inorder := by
    cases skeleton with
    | empty => exact False.elim (nonempty rfl)
    | node left root right => exact ⟨root, by simp [Tree.inorder]⟩
  obtain ⟨root, rootMember⟩ := rootExists
  obtain ⟨rootLo, rootHi, rootTime⟩ := valid.key_height root rootMember
  obtain ⟨key, keyLo, keyHi, sameHeight, visible⟩ :=
    GreedyMerge.Surface.covered_by_maximum height inside rootLo rootHi lo hi
      (fun z zlo zhi => by simpa only [rootTime] using valid.height_le z zlo zhi)
  have member := valid.maximal_mem keyLo keyHi (sameHeight.trans rootTime)
  have inRow := GreedyMerge.Geometry.greedyRow_subset_of_satisfies requested satisfies
    (GreedyMerge.Geometry.mem_greedyRow.mpr visible)
  exact ⟨key, member, inRow⟩

end ClassFrame.Realizes

end DynamicOptimality.GeometricOnlineSimulation
