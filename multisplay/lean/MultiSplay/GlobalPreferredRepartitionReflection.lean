import MultiSplay.GlobalPreferredRepartition

/-! # Exact hole repartition in both classical switch orientations -/

namespace MultiSplay.Global

open DynamicOptimality DynamicOptimality.SearchRotation
open TangoSquared.MTR
open TangoSquared.MTR.Tree (graft size inorder)
open Pointer (MarkedTree)
open ClassicalSwitch
open Auxiliary (mirror)

variable {α : Type*}

theorem leftExecution_mirrored_repartition {pivot : α}
    {incoming whole after parkedTree : RawTree α} {lower upper : Boundary α} {rotations : Nat}
    (run : LeftExecution pivot incoming lower upper whole after parkedTree rotations)
    (gaps : Nat → RawTree α) (start : Nat) (foreign : MarkedTree α)
    (foreignSkeleton : foreign.skeleton = mirror incoming)
    (attached : foreign.erase = gaps (start + upper.upperKeys.length)) :
    ∃ main old : MarkedTree α,
      main.skeleton = mirror after ∧ old.skeleton = mirror parkedTree ∧
      Rotations (graft (mirror whole) gaps start) main.erase rotations ∧ old.erase ∈ main.holes ∧
      Repartition true upper.reflect (markedGraft (mirror whole) gaps start) foreign main old := by
  cases run with
  | @neither whole old work pivotSplay =>
    let parked := markedGraft (mirror parkedTree) gaps (start + 1)
    let main := MarkedTree.node foreign pivot (.hole parked.erase)
    have incomingGap : foreign.erase = gaps start := by
      simpa [Boundary.upperKeys] using attached
    refine ⟨main, parked, ?_, ?_, ?_, ?_, ?_⟩
    · simp [main, MarkedTree.skeleton, foreignSkeleton, mirror]
    · exact markedGraft_skeleton _ gaps _
    · have actual := rotations_graft (splay_rotations pivotSplay.mirror) gaps start
      simpa [main, parked, MarkedTree.erase, graft, mirror, incomingGap, size] using actual
    · simp [main, MarkedTree.holes]
    · refine ⟨[], [], by simp [Boundary.upperKeys], ?_, ?_⟩
      · rw [rotations_holes (splay_rotations pivotSplay.mirror) gaps start]
        simp [markedGraft, MarkedTree.holes, parked, incomingGap, mirror, size]
      · simp [main, MarkedTree.holes]

  | @lower whole left a old lo pivotWork lowerWork pivotSplay lowerSplay =>
    let parked := markedGraft (mirror parkedTree) gaps (start + 1)
    let main := MarkedTree.node foreign pivot
      (.node (.hole parked.erase) lo (markedGraft (mirror a) gaps (start + parkedTree.size + 2)))
    have incomingGap : foreign.erase = gaps start := by
      simpa [Boundary.upperKeys] using attached
    refine ⟨main, parked, ?_, ?_, ?_, ?_, ?_⟩
    · simp [main, MarkedTree.skeleton, foreignSkeleton, mirror]
    · exact markedGraft_skeleton _ gaps _
    · have actual := rotations_graft
        (pivot_then_right_left pivotSplay.mirror (splay_rotations lowerSplay.mirror) (.refl .empty)) gaps start
      convert actual using 1 <;>
        simp [main, parked, MarkedTree.erase, graft, mirror, size, incomingGap]
      all_goals first | omega | (congr 1 <;> omega) | (constructor <;> congr 1 <;> omega)
    · simp [main, MarkedTree.holes]
    · refine ⟨[], (markedGraft (mirror a) gaps (start + parkedTree.size + 2)).holes,
        by simp [Boundary.upperKeys], ?_, ?_⟩
      · rw [rotations_holes
          (pivot_then_right_left pivotSplay.mirror (splay_rotations lowerSplay.mirror) (.refl .empty)) gaps start]
        simp [markedGraft, MarkedTree.holes, parked, incomingGap, mirror, size, List.append_assoc]
        apply congrArg (fun index => (markedGraft (mirror a) gaps index).holes)
        omega
      · simp [main, MarkedTree.holes, List.append_assoc]

  | @upper whole old right b hi pivotWork upperWork pivotSplay upperSplay =>
    let parked := markedGraft (mirror parkedTree) gaps (start + b.size + 2)
    let main := MarkedTree.node
      (.node (markedGraft (mirror b) gaps start) hi foreign) pivot (.hole parked.erase)
    have incomingGap : foreign.erase = gaps (start + b.size + 1) := by
      simpa [Boundary.upperKeys, Tree.length_inorder, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using attached
    refine ⟨main, parked, ?_, ?_, ?_, ?_, ?_⟩
    · simp [main, MarkedTree.skeleton, foreignSkeleton, mirror]
    · exact markedGraft_skeleton _ gaps _
    · have actual := rotations_graft
        (pivot_then_right_left pivotSplay.mirror (.refl (mirror parkedTree))
          (splay_rotations upperSplay.mirror)) gaps start
      convert actual using 1 <;>
        simp [main, parked, MarkedTree.erase, graft, mirror, size, incomingGap]
      all_goals first | omega | (congr 1 <;> omega) | (constructor <;> congr 1 <;> omega)
    · simp [main, MarkedTree.holes]
    · refine ⟨(markedGraft (mirror b) gaps start).holes, [], ?_, ?_, ?_⟩
      · simp [MarkedTree.holes_length, Boundary.upperKeys, Tree.length_inorder]
      · rw [rotations_holes
          (pivot_then_right_left pivotSplay.mirror (.refl (mirror parkedTree))
            (splay_rotations upperSplay.mirror)) gaps start]
        simp [markedGraft, MarkedTree.holes, parked, incomingGap, mirror, size, List.append_assoc]
        apply congrArg (fun index => (markedGraft (mirror parkedTree) gaps index).holes)
        omega
      · simp [main, MarkedTree.holes, List.append_assoc]

  | @both whole left right a old b lo hi pivotWork lowerWork upperWork pivotSplay lowerSplay upperSplay =>
    let parked := markedGraft (mirror parkedTree) gaps (start + b.size + 2)
    let main := MarkedTree.node
      (.node (markedGraft (mirror b) gaps start) hi foreign) pivot
      (.node (.hole parked.erase) lo
        (markedGraft (mirror a) gaps (start + b.size + parkedTree.size + 3)))
    have incomingGap : foreign.erase = gaps (start + b.size + 1) := by
      simpa [Boundary.upperKeys, Tree.length_inorder, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using attached
    refine ⟨main, parked, ?_, ?_, ?_, ?_, ?_⟩
    · simp [main, MarkedTree.skeleton, foreignSkeleton, mirror]
    · exact markedGraft_skeleton _ gaps _
    · have actual := rotations_graft
        (pivot_then_right_left pivotSplay.mirror (splay_rotations lowerSplay.mirror)
          (splay_rotations upperSplay.mirror)) gaps start
      convert actual using 1 <;>
        simp [main, parked, MarkedTree.erase, graft, mirror, size, incomingGap]
      all_goals first | omega | (congr 1 <;> omega) | (constructor <;> congr 1 <;> omega)
    · simp [main, MarkedTree.holes]
    · refine ⟨(markedGraft (mirror b) gaps start).holes,
        (markedGraft (mirror a) gaps (start + b.size + parkedTree.size + 3)).holes, ?_, ?_, ?_⟩
      · simp [MarkedTree.holes_length, Boundary.upperKeys, Tree.length_inorder]
      · rw [rotations_holes
          (pivot_then_right_left pivotSplay.mirror (splay_rotations lowerSplay.mirror)
            (splay_rotations upperSplay.mirror)) gaps start]
        simp [markedGraft, MarkedTree.holes, parked, incomingGap, mirror, size, List.append_assoc]
        congr 1
        apply congrArg (fun index => (markedGraft (mirror a) gaps index).holes)
        omega
      · simp [main, MarkedTree.holes, List.append_assoc]



/-- Physical switches preserve the exact ordered attachment exchange. -/
theorem execution_repartition {pivot : α} {incoming whole after parkedTree : RawTree α}
    {oldSide : Bool} {lower upper : Boundary α} {rotations : Nat}
    (run : ClassicalSwitch.Execution pivot incoming oldSide lower upper whole after parkedTree rotations)
    (before foreign : MarkedTree α) (beforeSkeleton : before.skeleton = whole)
    (foreignSkeleton : foreign.skeleton = incoming)
    (attached : foreign.erase = before.gapArray (incomingGapIndex oldSide lower parkedTree)) :
    ∃ main old : MarkedTree α,
      main.skeleton = after ∧ old.skeleton = parkedTree ∧
      Rotations before.erase main.erase rotations ∧ old.erase ∈ main.holes ∧
      Repartition oldSide lower before foreign main old := by
  have result : ∃ main old : MarkedTree α,
      main.skeleton = after ∧ old.skeleton = parkedTree ∧
      Rotations (graft whole before.gapArray 0) main.erase rotations ∧ old.erase ∈ main.holes ∧
      Repartition oldSide lower (markedGraft whole before.gapArray 0) foreign main old := by
    cases run with
    | left run =>
        exact leftExecution_repartition run before.gapArray 0 foreign foreignSkeleton
          (by simpa [incomingGapIndex, Nat.add_assoc] using attached)
    | right run =>
        have result := leftExecution_mirrored_repartition run before.gapArray 0 foreign
          (by simpa only [Auxiliary.mirror_mirror] using foreignSkeleton)
          (by simpa [incomingGapIndex] using attached)
        simpa only [Auxiliary.mirror_mirror, Boundary.reflect_reflect] using result
  simpa only [← beforeSkeleton, MarkedTree.graft_gapArray, markedGraft_gapArray] using result

end MultiSplay.Global
