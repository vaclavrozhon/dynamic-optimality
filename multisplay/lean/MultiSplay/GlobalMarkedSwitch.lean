import MultiSplay.GlobalSwitchPhysical
import MultiSplay.ClassicalSwitchExecution

/-!
# Regrouping the actual marked components at a classical switch

`markedGraft` retains the auxiliary skeleton while treating each foreign
subtree as an opaque hole. After the stopped splays, the old preferred
tail is one hole of the new component and the incoming marked component
is part of its skeleton. This changes only membership marks: the physical
tree is exactly the endpoint of the prescribed splay rotations.
-/

namespace MultiSplay.Global

open DynamicOptimality DynamicOptimality.SearchRotation
open ChaCha.MTR
open ChaCha.MTR.Tree (graft size inorder)
open Pointer (MarkedTree)
open ClassicalSwitch

variable {α : Type*}

def markedGraft : RawTree α → (Nat → RawTree α) → Nat → MarkedTree α
  | .empty, gaps, start => .hole (gaps start)
  | .node left key right, gaps, start =>
      .node (markedGraft left gaps start) key (markedGraft right gaps (start + left.size + 1))

@[simp] theorem markedGraft_skeleton (tree : RawTree α) (gaps : Nat → RawTree α) (start : Nat) :
    (markedGraft tree gaps start).skeleton = tree := by
  induction tree generalizing start <;> simp [markedGraft, MarkedTree.skeleton, *]

@[simp] theorem markedGraft_erase (tree : RawTree α) (gaps : Nat → RawTree α) (start : Nat) :
    (markedGraft tree gaps start).erase = graft tree gaps start := by
  induction tree generalizing start <;> simp [markedGraft, MarkedTree.erase, graft, *]

/-- The exact left-to-right checkpoint, including missing-guard cases.
The incoming component occupies the inorder gap just after the pivot.
The parked component's complete physical subtree is an actual output hole. -/
theorem leftExecution_marked {pivot : α} {incoming whole after parkedTree : RawTree α}
    {lower upper : Boundary α} {rotations : Nat}
    (run : LeftExecution pivot incoming lower upper whole after parkedTree rotations)
    (gaps : Nat → RawTree α) (start : Nat) (foreign : MarkedTree α)
    (foreignSkeleton : foreign.skeleton = incoming)
    (attached : foreign.erase = gaps (start + lower.lowerKeys.length + parkedTree.size + 1)) :
    ∃ main old : MarkedTree α,
      main.skeleton = after ∧ old.skeleton = parkedTree ∧
      Rotations (graft whole gaps start) main.erase rotations ∧ old.erase ∈ main.holes := by
  cases run with
  | @neither whole old work pivotSplay =>
    let parked := markedGraft parkedTree gaps start
    let main := MarkedTree.node (.hole parked.erase) pivot foreign
    refine ⟨main, parked, ?_, ?_, ?_, ?_⟩
    · simp [main, MarkedTree.skeleton, foreignSkeleton]
    · exact markedGraft_skeleton parkedTree gaps start
    · have actual := rotations_graft (splay_rotations pivotSplay) gaps start
      simp only [Boundary.lowerKeys, List.length_nil, Nat.add_zero] at attached
      simpa [main, parked, MarkedTree.erase, graft, ← attached] using actual
    · simp [main, MarkedTree.holes]
  | @lower whole left a old lo pivotWork lowerWork pivotSplay lowerSplay =>
    let parked := markedGraft parkedTree gaps (start + a.size + 1)
    let main := MarkedTree.node
      (.node (markedGraft a gaps start) lo (.hole parked.erase)) pivot foreign
    have incomingGap : foreign.erase = gaps (start + a.size + parkedTree.size + 2) := by
      convert attached using 1 <;> simp [Boundary.lowerKeys, Tree.length_inorder]
      congr 1 <;> omega
    refine ⟨main, parked, ?_, ?_, ?_, ?_⟩
    · simp [main, MarkedTree.skeleton, foreignSkeleton]
    · exact markedGraft_skeleton parkedTree gaps _
    · have actual := rotations_graft
        (pivot_then_left_right pivotSplay (splay_rotations lowerSplay) (.refl .empty)) gaps start
      convert actual using 1 <;>
        simp [main, parked, MarkedTree.erase, graft, size, incomingGap]
      all_goals first | omega | (congr 1 <;> omega) | (constructor <;> congr 1 <;> omega)
    · simp [main, MarkedTree.holes]
  | @upper whole old right b hi pivotWork upperWork pivotSplay upperSplay =>
    let parked := markedGraft parkedTree gaps start
    let main := MarkedTree.node (.hole parked.erase) pivot
      (.node foreign hi (markedGraft b gaps (start + parkedTree.size + 2)))
    have incomingGap : foreign.erase = gaps (start + parkedTree.size + 1) := by
      simpa [Boundary.lowerKeys] using attached
    refine ⟨main, parked, ?_, ?_, ?_, ?_⟩
    · simp [main, MarkedTree.skeleton, foreignSkeleton]
    · exact markedGraft_skeleton parkedTree gaps start
    · have actual := rotations_graft
        (pivot_then_left_right pivotSplay (.refl parkedTree) (splay_rotations upperSplay)) gaps start
      convert actual using 1 <;>
        simp [main, parked, MarkedTree.erase, graft, size, incomingGap]
      all_goals first | omega | (congr 1 <;> omega) | (constructor <;> congr 1 <;> omega)
    · simp [main, MarkedTree.holes]
  | @both whole left right a old b lo hi pivotWork lowerWork upperWork pivotSplay lowerSplay upperSplay =>
    let parked := markedGraft parkedTree gaps (start + a.size + 1)
    let main := MarkedTree.node
      (.node (markedGraft a gaps start) lo (.hole parked.erase)) pivot
      (.node foreign hi (markedGraft b gaps (start + a.size + parkedTree.size + 3)))
    have incomingGap : foreign.erase = gaps (start + a.size + parkedTree.size + 2) := by
      convert attached using 1 <;> simp [Boundary.lowerKeys, Tree.length_inorder]
      congr 1 <;> omega
    refine ⟨main, parked, ?_, ?_, ?_, ?_⟩
    · simp [main, MarkedTree.skeleton, foreignSkeleton]
    · exact markedGraft_skeleton parkedTree gaps _
    · have actual := rotations_graft
        (pivot_then_left_right pivotSplay (splay_rotations lowerSplay) (splay_rotations upperSplay)) gaps start
      convert actual using 1 <;>
        simp [main, parked, MarkedTree.erase, graft, size, incomingGap]
      all_goals first | omega | (congr 1 <;> omega) | (constructor <;> congr 1 <;> omega)
    · simp [main, MarkedTree.holes]

end MultiSplay.Global
