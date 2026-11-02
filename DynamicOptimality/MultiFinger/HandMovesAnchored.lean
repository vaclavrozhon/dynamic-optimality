import DynamicOptimality.MultiFinger.HandEndpoint

/-! # Endpoint changes which commute with an outer source context

Inner endpoint promotion and edits below a retained core vertex preserve
that vertex's outer tendon. These are exactly the edits needed while
walking upward from an edge between two marked source keys.
-/

namespace DynamicOptimality.MultiFinger.Hand

open ChaCha.MTR

variable {α : Type*}

inductive AnchoredEdit : Hand α → Hand α → Prop
  | inner_left (frames : List (Pointer.Frame α)) (left right : Hand α)
      (key parent : α) (sibling : RawTree α) :
      AnchoredEdit (.node (.left parent sibling::frames) left key right)
        (.node frames (.node [] left key right) parent (.stump sibling))
  | inner_right (frames : List (Pointer.Frame α)) (left right : Hand α)
      (key parent : α) (sibling : RawTree α) :
      AnchoredEdit (.node (.right sibling parent::frames) left key right)
        (.node frames (.stump sibling) parent (.node [] left key right))
  | left {before after : Hand α} (edit : EndpointEdit before after)
      (frames : List (Pointer.Frame α)) (key : α) (right : Hand α) :
      AnchoredEdit (.node frames before key right) (.node frames after key right)
  | right {before after : Hand α} (edit : EndpointEdit before after)
      (frames : List (Pointer.Frame α)) (left : Hand α) (key : α) :
      AnchoredEdit (.node frames left key before) (.node frames left key after)

theorem AnchoredEdit.endpoint {before after : Hand α} (edit : AnchoredEdit before after) :
    EndpointEdit before after := by
  cases edit with
  | inner_left => exact .inner_left ..
  | inner_right => exact .inner_right ..
  | left edit frames key right => exact .left edit frames key right
  | right edit frames left key => exact .right edit frames left key

theorem AnchoredEdit.extend {before after : Hand α} (edit : AnchoredEdit before after)
    (frame : Pointer.Frame α) : AnchoredEdit (before.extend frame) (after.extend frame) := by
  cases edit with
  | inner_left frames left right key parent sibling =>
      exact .inner_left (frames++[frame]) left right key parent sibling
  | inner_right frames left right key parent sibling =>
      exact .inner_right (frames++[frame]) left right key parent sibling
  | left edit frames key right => exact .left edit (frames++[frame]) key right
  | right edit frames left key => exact .right edit (frames++[frame]) left key

def AnchoredChange (before after : Hand α) : Prop := before = after ∨ AnchoredEdit before after

def EndpointChange (before after : Hand α) : Prop := before = after ∨ EndpointEdit before after

theorem AnchoredChange.endpoint {before after : Hand α} (change : AnchoredChange before after) :
    EndpointChange before after := change.imp_right AnchoredEdit.endpoint

theorem AnchoredChange.extend {before after : Hand α} (change : AnchoredChange before after)
    (frame : Pointer.Frame α) : AnchoredChange (before.extend frame) (after.extend frame) := by
  rcases change with rfl | edit
  · exact Or.inl rfl
  · exact Or.inr (edit.extend frame)

theorem EndpointChange.left {before after : Hand α} (change : EndpointChange before after)
    (frames : List (Pointer.Frame α)) (key : α) (right : Hand α) :
    AnchoredChange (.node frames before key right) (.node frames after key right) := by
  rcases change with rfl | edit
  · exact Or.inl rfl
  · exact Or.inr (.left edit frames key right)

theorem EndpointChange.right {before after : Hand α} (change : EndpointChange before after)
    (frames : List (Pointer.Frame α)) (left : Hand α) (key : α) :
    AnchoredChange (.node frames left key before) (.node frames left key after) := by
  rcases change with rfl | edit
  · exact Or.inl rfl
  · exact Or.inr (.right edit frames left key)

theorem EndpointChange.trace {before after : Hand α} (change : EndpointChange before after) :
    ∃ count ≤ 1, EndpointEdits before after count := by
  rcases change with rfl | edit
  · exact ⟨0, by omega, .refl _⟩
  · exact ⟨1, by omega, .step edit (.refl _)⟩

theorem EndpointEdits.append {first middle last : Hand α} {a b : Nat}
    (front : EndpointEdits first middle a) (back : EndpointEdits middle last b) :
    EndpointEdits first last (a+b) := by
  induction front with
  | refl => simpa using back
  | step edit rest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (EndpointEdits.step edit (ih back))

theorem EndpointEdits.symm {before after : Hand α} {count : Nat}
    (trace : EndpointEdits before after count) : EndpointEdits after before count := by
  induction trace with
  | refl => exact .refl _
  | step edit rest ih => exact ih.append (.step (.reverse edit) (.refl _))

end DynamicOptimality.MultiFinger.Hand
