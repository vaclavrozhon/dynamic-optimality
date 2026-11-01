import DynamicOptimality.Cost

/-!
# Search paths followed by arbitrary rotations

An access searches the current ordinary BST, paying one for each vertex on
the successful search path, and then performs finitely many ordinary
rotations, paying one for each. Navigation and bookkeeping carry no charge.
Every rotation below changes an actual subtree, at arbitrary depth. The
model reuses the shared raw tree and does not introduce a different OPT.
-/

namespace DynamicOptimality.SearchRotation

open TangoSquared.MTR

/-- One ordinary rotation at any subtree of the current tree. -/
inductive Rotation {α : Type*} : RawTree α → RawTree α → Prop
  | rootRight (a b c : RawTree α) (x y : α) :
      Rotation (.node (.node a x b) y c) (.node a x (.node b y c))
  | rootLeft (a b c : RawTree α) (x y : α) :
      Rotation (.node a x (.node b y c)) (.node (.node a x b) y c)
  | leftContext {before after : RawTree α} (step : Rotation before after)
      (key : α) (right : RawTree α) :
      Rotation (.node before key right) (.node after key right)
  | rightContext (left : RawTree α) (key : α) {before after : RawTree α}
      (step : Rotation before after) :
      Rotation (.node left key before) (.node left key after)

namespace Rotation

theorem symm {α : Type*} {before after : RawTree α}
    (step : Rotation before after) : Rotation after before := by
  induction step with
  | rootRight a b c x y => exact .rootLeft a b c x y
  | rootLeft a b c x y => exact .rootRight a b c x y
  | leftContext step key right ih => exact .leftContext ih key right
  | rightContext left key step ih => exact .rightContext left key ih

/-- Executing a rotation through an explicit zipper context is still one rotation. -/
theorem plug {α : Type*} {before after : RawTree α}
    (step : Rotation before after) (ancestors : List (Pointer.Frame α)) :
    Rotation (Pointer.plug before ancestors) (Pointer.plug after ancestors) := by
  induction ancestors generalizing before after with
  | nil => exact step
  | cons frame ancestors ih =>
    cases frame with
    | left key right => exact ih (.leftContext step key right)
    | right left key => exact ih (.rightContext left key step)

end Rotation

/-- The count is the actual length of the rotation sequence. -/
inductive Rotations {α : Type*} : RawTree α → RawTree α → Nat → Prop
  | refl (tree : RawTree α) : Rotations tree tree 0
  | step {before middle after : RawTree α} {count : Nat}
      (head : Rotation before middle) (tail : Rotations middle after count) :
      Rotations before after (count + 1)

namespace Rotations

theorem singleton {α : Type*} {before after : RawTree α}
    (step : Rotation before after) : Rotations before after 1 :=
  .step step (.refl after)

theorem append {α : Type*} {before middle after : RawTree α} {m n : Nat}
    (first : Rotations before middle m) (second : Rotations middle after n) :
    Rotations before after (m + n) := by
  induction first with
  | refl => simpa using second
  | step head tail ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Rotations.step head (ih second))

theorem symm {α : Type*} {before after : RawTree α} {count : Nat}
    (trace : Rotations before after count) : Rotations after before count := by
  induction trace with
  | refl tree => exact .refl tree
  | step head tail ih => exact ih.append (singleton head.symm)

theorem plug {α : Type*} {before after : RawTree α} {count : Nat}
    (trace : Rotations before after count) (ancestors : List (Pointer.Frame α)) :
    Rotations (Pointer.plug before ancestors) (Pointer.plug after ancestors) count := by
  induction trace with
  | refl tree => exact .refl _
  | step head tail ih => exact .step (head.plug ancestors) ih

end Rotations

/-- The search occurs before the rotations. The initial root contributes one unit. -/
def Access {α : Type*} [LinearOrder α] (key : α)
    (before after : RawTree α) (cost : Nat) : Prop :=
  ∃ depth count, Tree.searchDepth key before = some depth ∧
    Rotations before after count ∧ cost = depth + 1 + count

/-- A sequence of accesses continues from the actual preceding output tree. -/
inductive Execution {α : Type*} [LinearOrder α] :
    RawTree α → List α → RawTree α → Nat → Prop
  | nil (tree : RawTree α) : Execution tree [] tree 0
  | cons {key : α} {requests : List α} {before middle after : RawTree α}
      {headCost tailCost : Nat} (head : Access key before middle headCost)
      (tail : Execution middle requests after tailCost) :
      Execution before (key :: requests) after (headCost + tailCost)

namespace Execution

theorem append {α : Type*} [LinearOrder α]
    {before middle after : RawTree α} {firstRequests secondRequests : List α}
    {firstCost secondCost : Nat}
    (first : Execution before firstRequests middle firstCost)
    (second : Execution middle secondRequests after secondCost) :
    Execution before (firstRequests ++ secondRequests) after (firstCost + secondCost) := by
  induction first with
  | nil => simpa using second
  | cons head tail ih => simpa [Nat.add_assoc] using Execution.cons head (ih second)

theorem length_le_cost {α : Type*} [LinearOrder α]
    {before after : RawTree α} {requests : List α} {cost : Nat}
    (execution : Execution before requests after cost) : requests.length ≤ cost := by
  induction execution with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨depth, count, _, _, rfl⟩ := head
    simp only [List.length_cons]
    omega

end Execution
end DynamicOptimality.SearchRotation
