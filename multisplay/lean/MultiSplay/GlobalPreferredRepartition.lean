import MultiSplay.GlobalPreferredHoles

/-! # Exact ordered-hole repartition at a physical classical switch -/

namespace MultiSplay.Global

open DynamicOptimality DynamicOptimality.SearchRotation
open TangoSquared.MTR
open TangoSquared.MTR.Tree (graft size inorder)
open Pointer (MarkedTree)
open ClassicalSwitch

variable {α : Type*}

/-- The old component and incoming component exchange their role as a
preferred skeleton and a foreign hole. All remaining holes retain their
order and their literal physical subtrees. -/
def Repartition (oldSide : Bool) (lower : Boundary α)
    (before incoming after old : MarkedTree α) : Prop :=
  ∃ front back : List (RawTree α),
    front.length = lower.lowerKeys.length ∧
    before.holes = front ++
      (if oldSide then [incoming.erase] ++ old.holes else old.holes ++ [incoming.erase]) ++ back ∧
    after.holes = front ++
      (if oldSide then incoming.holes ++ [old.erase] else [old.erase] ++ incoming.holes) ++ back

theorem leftExecution_repartition {pivot : α} {incoming whole after parkedTree : RawTree α}
    {lower upper : Boundary α} {rotations : Nat}
    (run : LeftExecution pivot incoming lower upper whole after parkedTree rotations)
    (gaps : Nat → RawTree α) (start : Nat) (foreign : MarkedTree α)
    (foreignSkeleton : foreign.skeleton = incoming)
    (attached : foreign.erase = gaps (start + lower.lowerKeys.length + parkedTree.size + 1)) :
    ∃ main old : MarkedTree α,
      main.skeleton = after ∧ old.skeleton = parkedTree ∧
      Rotations (graft whole gaps start) main.erase rotations ∧ old.erase ∈ main.holes ∧
      Repartition false lower (markedGraft whole gaps start) foreign main old := by
  cases run with
  | @neither whole old work pivotSplay =>
    let parked := markedGraft parkedTree gaps start
    let main := MarkedTree.node (.hole parked.erase) pivot foreign
    refine ⟨main, parked, ?_, ?_, ?_, ?_, ?_⟩
    · simp [main, MarkedTree.skeleton, foreignSkeleton]
    · exact markedGraft_skeleton parkedTree gaps start
    · have actual := rotations_graft (splay_rotations pivotSplay) gaps start
      simp only [Boundary.lowerKeys, List.length_nil, Nat.add_zero] at attached
      simpa [main, parked, MarkedTree.erase, graft, ← attached] using actual
    · simp [main, MarkedTree.holes]
    · refine ⟨[], [], by simp [Boundary.lowerKeys], ?_, ?_⟩
      · rw [rotations_holes (splay_rotations pivotSplay) gaps start]
        simp only [Boundary.lowerKeys, List.length_nil, Nat.add_zero] at attached
        simp [markedGraft, MarkedTree.holes, parked, ← attached, Repartition]
      · simp [main, MarkedTree.holes]

  | @lower whole left a old lo pivotWork lowerWork pivotSplay lowerSplay =>
    let parked := markedGraft parkedTree gaps (start + a.size + 1)
    let main := MarkedTree.node
      (.node (markedGraft a gaps start) lo (.hole parked.erase)) pivot foreign
    have incomingGap : foreign.erase = gaps (start + a.size + parkedTree.size + 2) := by
      convert attached using 1 <;> simp [Boundary.lowerKeys, Tree.length_inorder]
      congr 1 <;> omega
    refine ⟨main, parked, ?_, ?_, ?_, ?_, ?_⟩
    · simp [main, MarkedTree.skeleton, foreignSkeleton]
    · exact markedGraft_skeleton parkedTree gaps _
    · have actual := rotations_graft
        (pivot_then_left_right pivotSplay (splay_rotations lowerSplay) (.refl .empty)) gaps start
      convert actual using 1 <;>
        simp [main, parked, MarkedTree.erase, graft, size, incomingGap]
      all_goals first | omega | (congr 1 <;> omega) | (constructor <;> congr 1 <;> omega)
    · simp [main, MarkedTree.holes]
    · refine ⟨(markedGraft a gaps start).holes, [], ?_, ?_, ?_⟩
      · simp [MarkedTree.holes_length, Boundary.lowerKeys, Tree.length_inorder]
      · rw [rotations_holes
          (pivot_then_left_right pivotSplay (splay_rotations lowerSplay) (.refl .empty)) gaps start]
        simp [markedGraft, MarkedTree.holes, parked, incomingGap, size, List.append_assoc]
        congr 1
        omega
      · simp [main, MarkedTree.holes, List.append_assoc]

  | @upper whole old right b hi pivotWork upperWork pivotSplay upperSplay =>
    let parked := markedGraft parkedTree gaps start
    let main := MarkedTree.node (.hole parked.erase) pivot
      (.node foreign hi (markedGraft b gaps (start + parkedTree.size + 2)))
    have incomingGap : foreign.erase = gaps (start + parkedTree.size + 1) := by
      simpa [Boundary.lowerKeys] using attached
    refine ⟨main, parked, ?_, ?_, ?_, ?_, ?_⟩
    · simp [main, MarkedTree.skeleton, foreignSkeleton]
    · exact markedGraft_skeleton parkedTree gaps start
    · have actual := rotations_graft
        (pivot_then_left_right pivotSplay (.refl parkedTree) (splay_rotations upperSplay)) gaps start
      convert actual using 1 <;>
        simp [main, parked, MarkedTree.erase, graft, size, incomingGap]
      all_goals first | omega | (congr 1 <;> omega) | (constructor <;> congr 1 <;> omega)
    · simp [main, MarkedTree.holes]
    · refine ⟨[], (markedGraft b gaps (start + parkedTree.size + 2)).holes,
        by simp [Boundary.lowerKeys], ?_, ?_⟩
      · rw [rotations_holes
          (pivot_then_left_right pivotSplay (.refl parkedTree) (splay_rotations upperSplay)) gaps start]
        simp [markedGraft, MarkedTree.holes, parked, incomingGap, size, List.append_assoc]
      · simp [main, MarkedTree.holes, List.append_assoc]

  | @both whole left right a old b lo hi pivotWork lowerWork upperWork pivotSplay lowerSplay upperSplay =>
    let parked := markedGraft parkedTree gaps (start + a.size + 1)
    let main := MarkedTree.node
      (.node (markedGraft a gaps start) lo (.hole parked.erase)) pivot
      (.node foreign hi (markedGraft b gaps (start + a.size + parkedTree.size + 3)))
    have incomingGap : foreign.erase = gaps (start + a.size + parkedTree.size + 2) := by
      convert attached using 1 <;> simp [Boundary.lowerKeys, Tree.length_inorder]
      congr 1 <;> omega
    refine ⟨main, parked, ?_, ?_, ?_, ?_, ?_⟩
    · simp [main, MarkedTree.skeleton, foreignSkeleton]
    · exact markedGraft_skeleton parkedTree gaps _
    · have actual := rotations_graft
        (pivot_then_left_right pivotSplay (splay_rotations lowerSplay) (splay_rotations upperSplay)) gaps start
      convert actual using 1 <;>
        simp [main, parked, MarkedTree.erase, graft, size, incomingGap]
      all_goals first | omega | (congr 1 <;> omega) | (constructor <;> congr 1 <;> omega)
    · simp [main, MarkedTree.holes]
    · refine ⟨(markedGraft a gaps start).holes,
        (markedGraft b gaps (start + a.size + parkedTree.size + 3)).holes, ?_, ?_, ?_⟩
      · simp [MarkedTree.holes_length, Boundary.lowerKeys, Tree.length_inorder]
      · rw [rotations_holes
          (pivot_then_left_right pivotSplay (splay_rotations lowerSplay) (splay_rotations upperSplay)) gaps start]
        simp [markedGraft, MarkedTree.holes, parked, incomingGap, size, List.append_assoc]
        constructor
        · congr 1
          omega
        · apply congrArg (fun index => (markedGraft b gaps index).holes)
          omega
      · simp [main, MarkedTree.holes, List.append_assoc]


end MultiSplay.Global
