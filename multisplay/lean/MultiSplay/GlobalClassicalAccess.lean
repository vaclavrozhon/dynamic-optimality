import MultiSplay.GlobalMarkedSwitchReflection
import MultiSplay.GlobalPhysicalAccess

/-!
# Actual classical switches and the initial search charge

The marked-component adapter exposes precisely the local attachment
obligation for a global preferred-path representation. The final-access
lemma then charges the initial search and all actual rotations, once the
ancestor switches have placed the query in the global root component.
-/

namespace MultiSplay.Global

open DynamicOptimality DynamicOptimality.SearchRotation
open ChaCha.MTR
open Pointer (MarkedTree)
open ClassicalSwitch

variable {α : Type*}

/-- A nonempty marked skeleton has the same root key as its complete
physical tree, regardless of the foreign subtrees in its holes. -/
theorem marked_erase_root {tree : MarkedTree α} {pivot : α}
    (root : tree.skeleton.rootKey = some pivot) : tree.erase.rootKey = some pivot := by
  cases tree with
  | hole tree => simp [MarkedTree.skeleton, Tree.rootKey] at root
  | node left key right => exact root

/-- A classical switch directly on an existing marked component, below
an arbitrary untouched outer context. The incoming attachment is the only
physical premise beyond the actual classical splay execution. -/
theorem execution_on_marked {pivot : α} {incoming whole after parkedTree : RawTree α}
    {oldSide : Bool} {lower upper : Boundary α} {rotations : Nat}
    (run : ClassicalSwitch.Execution pivot incoming oldSide lower upper whole after parkedTree rotations)
    (before foreign : MarkedTree α) (beforeSkeleton : before.skeleton = whole)
    (foreignSkeleton : foreign.skeleton = incoming)
    (attached : foreign.erase = before.gapArray (incomingGapIndex oldSide lower parkedTree))
    (ancestors : List (Pointer.Frame α)) :
    ∃ main old : MarkedTree α,
      main.skeleton = after ∧ old.skeleton = parkedTree ∧
      Rotations (Pointer.plug before.erase ancestors)
        (Pointer.plug main.erase ancestors) rotations ∧ old.erase ∈ main.holes := by
  obtain ⟨main, old, mainSkeleton, oldSkeleton, actual, hole⟩ :=
    execution_embedded run before.gapArray 0 foreign foreignSkeleton
      (by simpa only [Nat.zero_add] using attached) ancestors
  refine ⟨main, old, mainSkeleton, oldSkeleton, ?_, hole⟩
  simpa only [← beforeSkeleton, MarkedTree.graft_gapArray] using actual

/-- The actual global BST access after the ancestor switches. The last
switch uses the requested key in the root component, so its own proved
root property pays the original search depth. The output retains the
exact classical after/parked component shapes and the entire rotation
transcript. No navigation or bookkeeping operation is charged. -/
theorem final_switch_access {n earlierCount finalCount : Nat}
    (initial : BST 0 n) (key : Fin n) {incoming whole after parkedTree : RawTree Nat}
    {oldSide : Bool} {lower upper : Boundary Nat}
    (run : ClassicalSwitch.Execution key.val incoming oldSide lower upper whole after parkedTree finalCount)
    (before foreign : MarkedTree Nat) (beforeSkeleton : before.skeleton = whole)
    (foreignSkeleton : foreign.skeleton = incoming)
    (attached : foreign.erase = before.gapArray (incomingGapIndex oldSide lower parkedTree))
    (earlier : Rotations initial.toRaw before.erase earlierCount) :
    ∃ main old : MarkedTree Nat,
      main.skeleton = after ∧ old.skeleton = parkedTree ∧ old.erase ∈ main.holes ∧
      Rotations initial.toRaw main.erase (earlierCount + finalCount) ∧
      Access key.val initial.toRaw main.erase
        (initial.depth key.val + 1 + (earlierCount + finalCount)) ∧
      initial.depth key.val + 1 + (earlierCount + finalCount) ≤
        2 * (earlierCount + finalCount) + 1 := by
  obtain ⟨main, old, mainSkeleton, oldSkeleton, actual, hole⟩ :=
    execution_on_marked run before foreign beforeSkeleton foreignSkeleton attached []
  have finalRotations : Rotations before.erase main.erase finalCount := actual
  have allRotations := earlier.append finalRotations
  have root : main.erase.rootKey = some key.val :=
    marked_erase_root (mainSkeleton.symm ▸ run.root)
  obtain ⟨access, bound⟩ := rooted_access initial key allRotations root
  exact ⟨main, old, mainSkeleton, oldSkeleton, hole, allRotations, access, bound⟩

end MultiSplay.Global
