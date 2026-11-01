import MultiSplay.ClassicalSwitchMarkedUpdate

/-! # Opaque child components retain their internal preference states -/

namespace MultiSplay.ClassicalSwitch

open DynamicOptimality (RawTree)
open TangoSquared.Primary (Key)
open EndpointEncoding

variable {α : Type*}

theorem restrict_toggle_of_not_prefix (state : State) (address hole : Key)
    (outside : ¬ hole.IsPrefix address) :
    restrict (toggle state address) hole = restrict state hole := by
  funext owner
  have different : hole ++ owner ≠ address := fun same => outside ⟨owner,same⟩
  simp [restrict_eq, toggle, different]

theorem preferredHoles_address_nonempty (state : State) (left right : RawTree α) (pivot : α)
    {entry : Key × RawTree α} (member : entry ∈ preferredHoles state (.node left pivot right)) :
    entry.1 ≠ [] := by
  cases side : state [] with
  | false =>
      simp only [preferredHoles, side, Bool.false_eq_true, ↓reduceIte, List.mem_append,
        List.mem_singleton] at member
      rcases member with previous | rfl
      · obtain ⟨child,present,rfl⟩ := List.mem_map.mp previous
        simp
      · simp
  | true =>
      simp only [preferredHoles, side, ↓reduceIte, List.mem_cons] at member
      rcases member with rfl | previous
      · simp
      · obtain ⟨child,present,rfl⟩ := List.mem_map.mp previous
        simp

/-- A node on the marked preferred path is outside every opaque subtree. -/
theorem Path.hole_not_ancestor {state : State} {reference focus : RawTree α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine focus)
    (real : focus ≠ .empty) {entry : Key × RawTree α}
    (member : entry ∈ preferredHoles state reference) : ¬ entry.1.IsPrefix address := by
  induction path generalizing entry with
  | here state reference =>
      cases reference with
      | empty => exact False.elim (real rfl)
      | node left pivot right =>
          simpa using preferredHoles_address_nonempty state left right pivot member
  | @left state left right focus key address spine agrees rest ih =>
      simp only [preferredHoles, agrees, Bool.false_eq_true, ↓reduceIte, List.mem_append,
        List.mem_singleton] at member
      rcases member with previous | rfl
      · obtain ⟨child,present,rfl⟩ := List.mem_map.mp previous
        simpa using ih real present
      · simp
  | @right state left right focus key address spine agrees rest ih =>
      simp only [preferredHoles, agrees, ↓reduceIte, List.mem_cons] at member
      rcases member with rfl | previous
      · simp
      · obtain ⟨child,present,rfl⟩ := List.mem_map.mp previous
        simpa using ih real present

/-- Every pre-switch opaque subtree keeps exactly its previous internal
preference function, not merely its root preference. -/
theorem Path.hole_restrict_toggle {state : State} {reference focus : RawTree α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine focus)
    (real : focus ≠ .empty) {entry : Key × RawTree α}
    (member : entry ∈ preferredHoles state reference) :
    restrict (toggle state address) entry.1 = restrict state entry.1 :=
  restrict_toggle_of_not_prefix state address entry.1 (path.hole_not_ancestor real member)

theorem Path.after_hole_restrict_toggle {state : State} {reference focus : RawTree α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine focus)
    (real : focus ≠ .empty) {entry : Key × RawTree α}
    (member : entry ∈ preferredHoles (toggle state address) reference) :
    restrict (toggle state address) entry.1 = restrict state entry.1 :=
  restrict_toggle_of_not_prefix state address entry.1
    (path.toggle_endpoint.hole_not_ancestor real member)

end MultiSplay.ClassicalSwitch
