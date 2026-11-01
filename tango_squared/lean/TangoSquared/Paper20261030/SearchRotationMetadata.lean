import TangoSquared.Paper20261030.SearchRotationDepth
import DynamicOptimality.SearchRotationModel

set_option autoImplicit false

/-! Direct compilation of existing actual metadata accesses into the
search-path-plus-rotations model. The rotation sequence is extracted from
the original pointer trace, with exactly the same initial and final key
trees. Reads, writes, and cursor navigation require no rotations. The
initial search path is paid by the tracked connected-prefix bound.
-/

namespace TangoSquared.Paper20261030.SearchRotationBridge

open MTR
open DynamicOptimality.SearchRotation

variable {α : Type*}

theorem rotation_inorder {before after : MTR.Tree α} (step : Rotation before after) :
    after.inorder = before.inorder := by
  induction step with
  | rootRight | rootLeft => simp only [MTR.Tree.inorder,List.append_assoc]
  | leftContext step key right ih => simp only [MTR.Tree.inorder,ih]
  | rightContext left key step ih => simp only [MTR.Tree.inorder,ih]

theorem rotations_inorder {before after : MTR.Tree α} {count : Nat} (trace : Rotations before after count) :
    after.inorder = before.inorder := by
  induction trace with
  | refl => rfl
  | step first rest ih => exact ih.trans (rotation_inorder first)

/-- A navigation step changes no key tree. A pointer rotation contributes
exactly its one actual ordinary rotation through the surrounding context. -/
theorem pointer_step_rotations {before after : Pointer.Cursor α} (move : Pointer.Step before after) :
    ∃ count, Rotations before.tree after.tree count ∧ count ≤ 1 := by
  cases move with
  | left | right | upLeft | upRight => exact ⟨0,.refl _,by decide⟩
  | rotateRight a b c x y ancestors =>
    exact ⟨1,.singleton ((Rotation.rootRight a b c x y).plug ancestors),le_rfl⟩
  | rotateLeft a b c x y ancestors =>
    exact ⟨1,.singleton ((Rotation.rootLeft a b c x y).plug ancestors),le_rfl⟩

/-- The extracted sequence consists only of rotations already executed by
the pointer trace; its length does not include navigation or service. -/
theorem pointer_trace_rotations {before after : Pointer.Cursor α} {requests : List α} {cost : Nat}
    (trace : Pointer.Trace before requests after cost) :
    ∃ count, Rotations before.tree after.tree count ∧ count ≤ cost := by
  induction trace with
  | nil => exact ⟨0,.refl _,le_rfl⟩
  | step first rest ih =>
    obtain ⟨front,frontRun,frontBound⟩ := pointer_step_rotations first
    obtain ⟨back,backRun,backBound⟩ := ih
    exact ⟨front+back,frontRun.append backRun,by omega⟩
  | serve atKey rest ih =>
    obtain ⟨count,run,bound⟩ := ih
    exact ⟨count,run,by omega⟩

variable [LinearOrder α]

/-- Exact same key-tree endpoints, with at most twice the charged original
pointer cost. The new access searches the initial tree before rotating. -/
theorem pointer_access {before after : MTR.Tree α} {key : α} {cost : Nat}
    (ordered : MTR.Tree.Ordered before) (access : Pointer.Access key before after cost) :
    ∃ actualCost, Access key before after actualCost ∧ actualCost ≤ 2*cost := by
  obtain ⟨depth,found,depthBound⟩ := pointer_access_initial_depth ordered access
  obtain ⟨final,finalTree,trace⟩ := access
  obtain ⟨count,rotations,rotationBound⟩ := pointer_trace_rotations trace
  have actual : Rotations before after count := by
    change Rotations before final.tree count at rotations
    rw [finalTree] at rotations
    exact rotations
  exact ⟨depth+1+count,⟨depth,count,found,actual,rfl⟩,by omega⟩

theorem access_inorder {before after : MTR.Tree α} {key : α} {cost : Nat}
    (access : Access key before after cost) : after.inorder = before.inorder := by
  obtain ⟨_,_,_,trace,_⟩ := access
  exact rotations_inorder trace

theorem pointer_execution {before after : MTR.Tree α} {requests : List α} {cost : Nat}
    (ordered : MTR.Tree.Ordered before) (execution : Pointer.Execution before requests after cost) :
    ∃ actualCost, Execution before requests after actualCost ∧ actualCost ≤ 2*cost := by
  induction execution with
  | nil => exact ⟨0,.nil _,by omega⟩
  | @cons before middle after key requests firstCost lastCost first rest ih =>
    obtain ⟨front,frontRun,frontBound⟩ := pointer_access ordered first
    have middleOrdered : MTR.Tree.Ordered middle := by
      unfold MTR.Tree.Ordered
      rw [access_inorder frontRun]
      exact ordered
    obtain ⟨back,backRun,backBound⟩ := ih middleOrdered
    exact ⟨front+back,.cons frontRun backRun,by omega⟩

/-- Existing metadata accesses compile directly to the clarified actual
BST model. Erasure preserves every key; no representation simulator is
assumed and no new key or auxiliary search vertex is introduced. -/
theorem metadata_access {β : α → Type*}
    {before after : MTR.Tree (Auxiliary.NodeRecord α β)} {key : α} {cost : Nat}
    (ordered : MTR.Tree.Ordered (Auxiliary.Metadata.forgetTree before))
    (access : Auxiliary.Metadata.Access key before after cost) :
    ∃ actualCost, Access key (Auxiliary.Metadata.forgetTree before) (Auxiliary.Metadata.forgetTree after) actualCost ∧
      actualCost ≤ 2*cost := by
  obtain ⟨pointerCost,bound,pointer⟩ := access.pointer
  obtain ⟨actualCost,actual,actualBound⟩ := pointer_access ordered pointer
  exact ⟨actualCost,actual,actualBound.trans (Nat.mul_le_mul_left 2 bound)⟩

theorem metadata_execution {β : α → Type*}
    {before after : MTR.Tree (Auxiliary.NodeRecord α β)} {requests : List α} {cost : Nat}
    (ordered : MTR.Tree.Ordered (Auxiliary.Metadata.forgetTree before))
    (execution : Auxiliary.Metadata.Execution before requests after cost) :
    ∃ actualCost, Execution (Auxiliary.Metadata.forgetTree before) requests (Auxiliary.Metadata.forgetTree after) actualCost ∧
      actualCost ≤ 2*cost := by
  obtain ⟨pointerCost,bound,pointer⟩ := execution.pointer
  obtain ⟨actualCost,actual,actualBound⟩ := pointer_execution ordered pointer
  exact ⟨actualCost,actual,actualBound.trans (Nat.mul_le_mul_left 2 bound)⟩

end TangoSquared.Paper20261030.SearchRotationBridge
