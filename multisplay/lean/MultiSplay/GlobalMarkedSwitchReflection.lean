import MultiSplay.GlobalMarkedSwitch

/-!
# Reflected physical component switch

Reflection changes the physical guard order. The following proof retains
that order, and then packages both orientations using the same incoming-gap
index in the unreflected component.
-/

namespace MultiSplay.Global

open DynamicOptimality DynamicOptimality.SearchRotation
open ChaCha.MTR
open ChaCha.MTR.Tree (graft size inorder)
open Pointer (MarkedTree)
open ClassicalSwitch
open Auxiliary (mirror)

variable {α : Type*}

@[simp] theorem mirror_size (tree : RawTree α) : (mirror tree).size = tree.size := by
  induction tree <;> simp [mirror, size, *] <;> omega

/-- The reflection of a left execution, with gaps indexed in the actual
unreflected physical tree. The incoming component is immediately before
the pivot, after the reflected upper boundary. -/
theorem leftExecution_mirrored_marked {pivot : α}
    {incoming whole after parkedTree : RawTree α} {lower upper : Boundary α} {rotations : Nat}
    (run : LeftExecution pivot incoming lower upper whole after parkedTree rotations)
    (gaps : Nat → RawTree α) (start : Nat) (foreign : MarkedTree α)
    (foreignSkeleton : foreign.skeleton = mirror incoming)
    (attached : foreign.erase = gaps (start + upper.upperKeys.length)) :
    ∃ main old : MarkedTree α,
      main.skeleton = mirror after ∧ old.skeleton = mirror parkedTree ∧
      Rotations (graft (mirror whole) gaps start) main.erase rotations ∧ old.erase ∈ main.holes := by
  cases run with
  | @neither whole old work pivotSplay =>
    let parked := markedGraft (mirror parkedTree) gaps (start + 1)
    let main := MarkedTree.node foreign pivot (.hole parked.erase)
    have incomingGap : foreign.erase = gaps start := by
      simpa [Boundary.upperKeys] using attached
    refine ⟨main, parked, ?_, ?_, ?_, ?_⟩
    · simp [main, MarkedTree.skeleton, foreignSkeleton, mirror]
    · exact markedGraft_skeleton _ gaps _
    · have actual := rotations_graft (splay_rotations pivotSplay.mirror) gaps start
      simpa [main, parked, MarkedTree.erase, graft, mirror, incomingGap, size] using actual
    · simp [main, MarkedTree.holes]
  | @lower whole left a old lo pivotWork lowerWork pivotSplay lowerSplay =>
    let parked := markedGraft (mirror parkedTree) gaps (start + 1)
    let main := MarkedTree.node foreign pivot
      (.node (.hole parked.erase) lo (markedGraft (mirror a) gaps (start + parkedTree.size + 2)))
    have incomingGap : foreign.erase = gaps start := by
      simpa [Boundary.upperKeys] using attached
    refine ⟨main, parked, ?_, ?_, ?_, ?_⟩
    · simp [main, MarkedTree.skeleton, foreignSkeleton, mirror]
    · exact markedGraft_skeleton _ gaps _
    · have actual := rotations_graft
        (pivot_then_right_left pivotSplay.mirror (splay_rotations lowerSplay.mirror) (.refl .empty)) gaps start
      convert actual using 1 <;>
        simp [main, parked, MarkedTree.erase, graft, mirror, size, incomingGap]
      all_goals first | omega | (congr 1 <;> omega) | (constructor <;> congr 1 <;> omega)
    · simp [main, MarkedTree.holes]
  | @upper whole old right b hi pivotWork upperWork pivotSplay upperSplay =>
    let parked := markedGraft (mirror parkedTree) gaps (start + b.size + 2)
    let main := MarkedTree.node
      (.node (markedGraft (mirror b) gaps start) hi foreign) pivot (.hole parked.erase)
    have incomingGap : foreign.erase = gaps (start + b.size + 1) := by
      simpa [Boundary.upperKeys, Tree.length_inorder, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using attached
    refine ⟨main, parked, ?_, ?_, ?_, ?_⟩
    · simp [main, MarkedTree.skeleton, foreignSkeleton, mirror]
    · exact markedGraft_skeleton _ gaps _
    · have actual := rotations_graft
        (pivot_then_right_left pivotSplay.mirror (.refl (mirror parkedTree))
          (splay_rotations upperSplay.mirror)) gaps start
      convert actual using 1 <;>
        simp [main, parked, MarkedTree.erase, graft, mirror, size, incomingGap]
      all_goals first | omega | (congr 1 <;> omega) | (constructor <;> congr 1 <;> omega)
    · simp [main, MarkedTree.holes]
  | @both whole left right a old b lo hi pivotWork lowerWork upperWork pivotSplay lowerSplay upperSplay =>
    let parked := markedGraft (mirror parkedTree) gaps (start + b.size + 2)
    let main := MarkedTree.node
      (.node (markedGraft (mirror b) gaps start) hi foreign) pivot
      (.node (.hole parked.erase) lo
        (markedGraft (mirror a) gaps (start + b.size + parkedTree.size + 3)))
    have incomingGap : foreign.erase = gaps (start + b.size + 1) := by
      simpa [Boundary.upperKeys, Tree.length_inorder, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using attached
    refine ⟨main, parked, ?_, ?_, ?_, ?_⟩
    · simp [main, MarkedTree.skeleton, foreignSkeleton, mirror]
    · exact markedGraft_skeleton _ gaps _
    · have actual := rotations_graft
        (pivot_then_right_left pivotSplay.mirror (splay_rotations lowerSplay.mirror)
          (splay_rotations upperSplay.mirror)) gaps start
      convert actual using 1 <;>
        simp [main, parked, MarkedTree.erase, graft, mirror, size, incomingGap]
      all_goals first | omega | (congr 1 <;> omega) | (constructor <;> congr 1 <;> omega)
    · simp [main, MarkedTree.holes]

/-- Index of the incoming foreign component in the old component's
inorder gap array. For a left old tail it follows the tail and pivot;
for a right old tail it immediately precedes the pivot. -/
def incomingGapIndex (oldSide : Bool) (lower : Boundary α) (old : RawTree α) : Nat :=
  lower.lowerKeys.length + if oldSide then 0 else old.size + 1

/-- Both orientations of the actual classical switch. The old component
becomes an opaque child and the incoming component becomes part of the new
skeleton. Only the prescribed pivot and stopped guard splays rotate. -/
theorem execution_marked {pivot : α} {incoming whole after parkedTree : RawTree α}
    {oldSide : Bool} {lower upper : Boundary α} {rotations : Nat}
    (run : Execution pivot incoming oldSide lower upper whole after parkedTree rotations)
    (gaps : Nat → RawTree α) (start : Nat) (foreign : MarkedTree α)
    (foreignSkeleton : foreign.skeleton = incoming)
    (attached : foreign.erase = gaps (start + incomingGapIndex oldSide lower parkedTree)) :
    ∃ main old : MarkedTree α,
      main.skeleton = after ∧ old.skeleton = parkedTree ∧
      Rotations (graft whole gaps start) main.erase rotations ∧ old.erase ∈ main.holes := by
  cases run with
  | left run =>
    exact leftExecution_marked run gaps start foreign foreignSkeleton
      (by simpa [incomingGapIndex, Nat.add_assoc] using attached)
  | right run =>
    have result := leftExecution_mirrored_marked run gaps start foreign
      (by simpa only [Auxiliary.mirror_mirror] using foreignSkeleton)
      (by simpa [incomingGapIndex] using attached)
    simpa only [Auxiliary.mirror_mirror] using result

/-- The same actual switch below any untouched outer BST context. -/
theorem execution_embedded {pivot : α} {incoming whole after parkedTree : RawTree α}
    {oldSide : Bool} {lower upper : Boundary α} {rotations : Nat}
    (run : Execution pivot incoming oldSide lower upper whole after parkedTree rotations)
    (gaps : Nat → RawTree α) (start : Nat) (foreign : MarkedTree α)
    (foreignSkeleton : foreign.skeleton = incoming)
    (attached : foreign.erase = gaps (start + incomingGapIndex oldSide lower parkedTree))
    (ancestors : List (Pointer.Frame α)) :
    ∃ main old : MarkedTree α,
      main.skeleton = after ∧ old.skeleton = parkedTree ∧
      Rotations (Pointer.plug (graft whole gaps start) ancestors)
        (Pointer.plug main.erase ancestors) rotations ∧ old.erase ∈ main.holes := by
  obtain ⟨main, old, mainSkeleton, oldSkeleton, actual, hole⟩ :=
    execution_marked run gaps start foreign foreignSkeleton attached
  exact ⟨main, old, mainSkeleton, oldSkeleton, actual.plug ancestors, hole⟩

end MultiSplay.Global
