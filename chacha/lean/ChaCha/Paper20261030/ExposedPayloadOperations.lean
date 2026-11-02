import ChaCha.Paper20261030.EncodingSourceOperations

/-! A boundary child is reached through the constant-size exposed physical
context. Its whole root-to-root operation lifts with at most twenty extra
steps, including removal and restoration of all attachment prefixes. -/

namespace ChaCha.Paper20261030.PackedPrimary

open ColoredStorage ProjectionLocal PreferredProjection PrimaryWings HeadBlocks

variable {α ρ τ : Type*} [DecidableEq α]

local instance exposedPayloadColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem override_active_view (primary childPrimary : PrefRouter α) (distinct : primary.leaves.Nodup)
    (common tail : List (Exit α)) (direction : Bool)
    (word : exits primary = common ++ ⟨direction,childPrimary⟩ :: tail)
    (payload : Exit α → Source α (List (Option τ))) (child : Source α (List (Option τ)))
    (header : List τ) (values : ρ → τ) (headPart rest : Source Nat ρ)
    (headAway : ∀ d ∈ headPart.shape.leaves, d ≠ common.length)
    (restAway : ∀ d ∈ rest.shape.leaves, d ≠ common.length)
    (low high terminal : ρ) :
    let d := common.length
    let base := encoding 0 primary payload header
    let updated := encoding 0 primary (Function.update payload ⟨direction,childPrimary⟩ child) header
    some (updated.tree values (.fork low headPart (.fork high (.leaf d terminal) rest))) =
      activeView (base.wing values true headPart) (base.wing values false headPart)
        (base.wing values true rest) (some (.leaf primary.terminal [])) (base.wing values false rest)
        (some child) direction (activeRecords (color 0 primary) values headPart rest d low high terminal header) := by
  dsimp only
  let updated := encoding 0 primary (Function.update payload ⟨direction,childPrimary⟩ child) header
  have boundary : portAt 0 (exits primary) common.length = some ⟨direction,childPrimary⟩ := by
    rw [word]; exact portAt_boundary _ _ _
  have colorBoundary : updated.color common.length = some direction := by
    change color 0 primary common.length = some direction
    simp [color,boundary]
  have view := updated.active_view values headPart rest common.length low high terminal direction colorBoundary
  have childAt : updated.payload (updated.labels common.length) = child := by
    change Function.update payload ⟨direction,childPrimary⟩ child (label 0 primary common.length) = child
    simp [label,boundary]
  rw [childAt] at view
  have headSame := override_wing primary distinct common tail ⟨direction,childPrimary⟩ word
    payload child header values headPart headAway
  have restSame := override_wing primary distinct common tail ⟨direction,childPrimary⟩ word
    payload child header values rest restAway
  dsimp only [updated] at view
  rw [headSame true,headSame false,restSame true,restSame false] at view
  exact view

theorem exposed_payload_rearranges (primary childPrimary : PrefRouter α) (distinct : primary.leaves.Nodup)
    (common tail : List (Exit α)) (direction : Bool)
    (word : exits primary = common ++ ⟨direction,childPrimary⟩ :: tail)
    (payload : Exit α → Source α (List (Option τ)))
    (header : List τ) (values : ρ → τ) (headPart rest : Source Nat ρ)
    (headAway : ∀ d ∈ headPart.shape.leaves, d ≠ common.length)
    (restAway : ∀ d ∈ rest.shape.leaves, d ≠ common.length)
    (low high terminal : ρ) {oldChild newChild : Source α (List (Option τ))} {budget : Nat}
    (execution : SourcePointer.Rearranges oldChild newChild budget) :
    let d := common.length
    let oldEncoding := encoding 0 primary (Function.update payload ⟨direction,childPrimary⟩ oldChild) header
    let newEncoding := encoding 0 primary (Function.update payload ⟨direction,childPrimary⟩ newChild) header
    SourcePointer.Rearranges (oldEncoding.tree values (.fork low headPart (.fork high (.leaf d terminal) rest)))
      (newEncoding.tree values (.fork low headPart (.fork high (.leaf d terminal) rest))) (budget+20) := by
  have beforeView := override_active_view primary childPrimary distinct common tail direction word
    payload oldChild header values headPart rest headAway restAway low high terminal
  have afterView := override_active_view primary childPrimary distinct common tail direction word
    payload newChild header values headPart rest headAway restAway low high terminal
  have child : ProjectionLocal.Rearranges (some oldChild) (some newChild) budget := execution
  have lifted := activeView_boundary_rearranges
    ((encoding 0 primary payload header).wing values true headPart)
    ((encoding 0 primary payload header).wing values false headPart)
    ((encoding 0 primary payload header).wing values true rest)
    (some (.leaf primary.terminal []))
    ((encoding 0 primary payload header).wing values false rest) direction
    (activeRecords (color 0 primary) values headPart rest common.length low high terminal header) child
  rw [← beforeView,← afterView] at lifted
  exact lifted

end ChaCha.Paper20261030.PackedPrimary
