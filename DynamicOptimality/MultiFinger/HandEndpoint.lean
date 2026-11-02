import DynamicOptimality.MultiFinger.HandChanges

/-! Source-local endpoint edits of the reduced hand.
Each generator either changes the status of a root of an untouched
subtree, or moves one endpoint separator into or out of its adjacent
tendon. An edit never splits an interior tendon. The constructors retain
all original source frames and hanging subtrees literally.

The physical deque implementation proves an amortized constant-size
region update for each generator. This source relation is independent of
that implementation. -/

namespace DynamicOptimality.MultiFinger.Hand

open ChaCha.MTR

variable {α : Type*}

inductive EndpointEdit : Hand α → Hand α → Prop
  | stump (left right : RawTree α) (key : α) :
      EndpointEdit (.stump (.node left key right))
        (.node [] (.stump left) key (.stump right))
  | outer_left (frames : List (Pointer.Frame α)) (left right : Hand α)
      (key parent : α) (sibling : RawTree α) :
      EndpointEdit (.node (frames++[.left parent sibling]) left key right)
        (.node [] (.node frames left key right) parent (.stump sibling))
  | outer_right (frames : List (Pointer.Frame α)) (left right : Hand α)
      (key parent : α) (sibling : RawTree α) :
      EndpointEdit (.node (frames++[.right sibling parent]) left key right)
        (.node [] (.stump sibling) parent (.node frames left key right))
  | inner_left (frames : List (Pointer.Frame α)) (left right : Hand α)
      (key parent : α) (sibling : RawTree α) :
      EndpointEdit (.node (.left parent sibling::frames) left key right)
        (.node frames (.node [] left key right) parent (.stump sibling))
  | inner_right (frames : List (Pointer.Frame α)) (left right : Hand α)
      (key parent : α) (sibling : RawTree α) :
      EndpointEdit (.node (.right sibling parent::frames) left key right)
        (.node frames (.stump sibling) parent (.node [] left key right))
  | reverse {before after : Hand α} (edit : EndpointEdit before after) :
      EndpointEdit after before
  | left {before after : Hand α} (edit : EndpointEdit before after)
      (frames : List (Pointer.Frame α)) (key : α) (right : Hand α) :
      EndpointEdit (.node frames before key right) (.node frames after key right)
  | right {before after : Hand α} (edit : EndpointEdit before after)
      (frames : List (Pointer.Frame α)) (left : Hand α) (key : α) :
      EndpointEdit (.node frames left key before) (.node frames left key after)

/-- The count is the number of endpoint status changes, not source depth. -/
inductive EndpointEdits : Hand α → Hand α → Nat → Prop
  | refl (hand : Hand α) : EndpointEdits hand hand 0
  | step {before middle after : Hand α} {count : Nat}
      (edit : EndpointEdit before middle) (rest : EndpointEdits middle after count) :
      EndpointEdits before after (count+1)

theorem EndpointEdit.source_eq {before after : Hand α} (edit : EndpointEdit before after) :
    before.source = after.source := by
  induction edit with
  | stump => rfl
  | outer_left => exact promote_outer_left ..
  | outer_right => exact promote_outer_right ..
  | inner_left => rfl
  | inner_right => rfl
  | reverse _ ih => exact ih.symm
  | left _ _ _ _ ih => simp only [Hand.source,ih]
  | right _ _ _ _ ih => simp only [Hand.source,ih]

theorem EndpointEdits.source_eq {before after : Hand α} {count : Nat}
    (edits : EndpointEdits before after count) : before.source = after.source := by
  induction edits with
  | refl => rfl
  | step first _ ih => exact first.source_eq.trans ih

theorem EndpointEdit.core_sizes {before after : Hand α} (edit : EndpointEdit before after) :
    after.core.size ≤ before.core.size+1 ∧ before.core.size ≤ after.core.size+1 := by
  induction edit with
  | stump => simp [Hand.core,Tree.size]
  | outer_left => simp only [Hand.core,Tree.size]; omega
  | outer_right => simp only [Hand.core,Tree.size]; omega
  | inner_left => simp only [Hand.core,Tree.size]; omega
  | inner_right => simp only [Hand.core,Tree.size]; omega
  | reverse _ ih => exact ⟨ih.2,ih.1⟩
  | left _ _ _ _ ih => simp only [Hand.core,Tree.size]; omega
  | right _ _ _ _ ih => simp only [Hand.core,Tree.size]; omega

theorem EndpointEdits.core_size {before after : Hand α} {count : Nat}
    (edits : EndpointEdits before after count) : after.core.size ≤ before.core.size+count := by
  induction edits with
  | refl => omega
  | step first _ ih => have size := first.core_sizes; omega

end DynamicOptimality.MultiFinger.Hand
