import TangoSquared.Paper20261030.PhysicalRootHeadExchange
import TangoSquared.Paper20261030.CompletePhysicalHeadExchange

/-! Root-boundary versions of the actual-port exchange and payload kernels. -/

namespace TangoSquared.Paper20261030.PackedPrimary

open ColoredStorage ProjectionLocal PreferredProjection PrimaryWings HeadBlocks

variable {α ρ τ : Type*} [DecidableEq α]

local instance primaryRootKernelColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem decomposed_physical_root_kernel
    (before after old incoming : PrefRouter α) (direction : Bool)
    (beforeDistinct : before.leaves.Nodup) (afterDistinct : after.leaves.Nodup)
    (oldEnd : before.terminal = old.terminal) (newEnd : after.terminal = incoming.terminal)
    (beforeWord : exits before = ⟨direction,incoming⟩ :: exits old)
    (afterWord : exits after = ⟨!direction,old⟩ :: exits incoming)
    (values : ρ → τ) (oldTail newTail : Source Nat ρ)
    (oldDepths : ∀ d ∈ oldTail.shape.leaves, 0 < d)
    (newDepths : ∀ d ∈ newTail.shape.leaves, 0 < d)
    (oldHigh newHigh terminal : ρ)
    (payload : Exit α → Source α (List (Option τ)))
    (beforeHeader afterHeader oldHeader incomingHeader : List τ) :
    let oldDormant := encoding 1 old payload oldHeader
    let incomingDormant := encoding 1 incoming payload incomingHeader
    let oldPayload := Function.update payload ⟨direction,incoming⟩
      (incomingDormant.tree values (.fork newHigh (.leaf 0 terminal) newTail))
    let newPayload := Function.update payload ⟨!direction,old⟩
      (oldDormant.tree values (.fork oldHigh (.leaf 0 terminal) oldTail))
    SourcePointer.Rearranges
      ((encoding 0 before oldPayload beforeHeader).tree values (.fork oldHigh (.leaf 0 terminal) oldTail))
      ((encoding 0 after newPayload afterHeader).tree values (.fork newHigh (.leaf 0 terminal) newTail)) 288 := by
  dsimp only
  let oldDormant := encoding 1 old payload oldHeader
  let incomingDormant := encoding 1 incoming payload incomingHeader
  let oldChild := oldDormant.tree values (.fork oldHigh (.leaf 0 terminal) oldTail)
  let incomingChild := incomingDormant.tree values (.fork newHigh (.leaf 0 terminal) newTail)
  let oldPayload := Function.update payload ⟨direction,incoming⟩ incomingChild
  let newPayload := Function.update payload ⟨!direction,old⟩ oldChild
  let oldActive := encoding 0 before oldPayload beforeHeader
  let newActive := encoding 0 after newPayload afterHeader
  have oldAgreement : ∀ side, oldActive.wing values side oldTail = oldDormant.wing values side oldTail := by
    intro side
    have first := override_wing before beforeDistinct [] (exits old) ⟨direction,incoming⟩ beforeWord
      payload incomingChild beforeHeader values oldTail (fun depth member => Nat.ne_of_gt (oldDepths depth member)) side
    apply first.trans
    apply encoding_wing_congr
    · intro depth member
      rw [beforeWord]
      exact portAt_tail [] (exits old) ⟨direction,incoming⟩ depth (oldDepths depth member)
    · exact fun _ _ _ _ => rfl
  have newAgreement : ∀ side, newActive.wing values side newTail = incomingDormant.wing values side newTail := by
    intro side
    have first := override_wing after afterDistinct [] (exits incoming) ⟨!direction,old⟩ afterWord
      payload oldChild afterHeader values newTail (fun depth member => Nat.ne_of_gt (newDepths depth member)) side
    apply first.trans
    apply encoding_wing_congr
    · intro depth member
      rw [afterWord]
      exact portAt_tail [] (exits incoming) ⟨!direction,old⟩ depth (newDepths depth member)
    · exact fun _ _ _ _ => rfl
  apply physical_root_head_exchange oldActive newActive oldDormant incomingDormant values oldTail newTail
    0 oldHigh newHigh terminal direction
  · change color 0 before 0 = some direction
    simp [color,portAt,beforeWord]
  · change color 0 after 0 = some (!direction)
    simp [color,portAt,afterWord]
  · change color 1 old 0 = none
    simp [color,portAt]
  · change color 1 incoming 0 = none
    simp [color,portAt]
  · exact oldAgreement
  · exact newAgreement
  · exact oldEnd
  · exact newEnd
  · change oldPayload (label 0 before 0) = incomingChild
    simp [oldPayload,label,portAt,beforeWord]
  · change newPayload (label 0 after 0) = oldChild
    simp [newPayload,label,portAt,afterWord]

set_option backward.isDefEq.respectTransparency false in
theorem override_root_view (primary childPrimary : PrefRouter α) (distinct : primary.leaves.Nodup)
    (tail : List (Exit α)) (direction : Bool) (word : exits primary = ⟨direction,childPrimary⟩ :: tail)
    (payload : Exit α → Source α (List (Option τ))) (child : Source α (List (Option τ)))
    (header : List τ) (values : ρ → τ) (rest : Source Nat ρ)
    (restAway : ∀ d ∈ rest.shape.leaves, d ≠ 0) (high terminal : ρ) :
    let base := encoding 0 primary payload header
    let updated := encoding 0 primary (Function.update payload ⟨direction,childPrimary⟩ child) header
    some (updated.tree values (.fork high (.leaf 0 terminal) rest)) =
      activeView none none (base.wing values true rest) (some (.leaf primary.terminal []))
        (base.wing values false rest) (some child) direction
        (rootActiveRecords (color 0 primary) values rest 0 high terminal header) := by
  dsimp only
  let updated := encoding 0 primary (Function.update payload ⟨direction,childPrimary⟩ child) header
  have colorBoundary : updated.color 0 = some direction := by
    change color 0 primary 0 = some direction
    simp [color,portAt,word]
  have view := updated.root_active_view values rest 0 high terminal direction colorBoundary
  have childAt : updated.payload (updated.labels 0) = child := by
    change Function.update payload ⟨direction,childPrimary⟩ child (label 0 primary 0) = child
    simp [label,portAt,word]
  rw [childAt] at view
  have restSame := override_wing primary distinct [] tail ⟨direction,childPrimary⟩ word
    payload child header values rest restAway
  dsimp only [updated] at view
  rw [restSame true,restSame false] at view
  exact view

theorem root_payload_rearranges (primary childPrimary : PrefRouter α) (distinct : primary.leaves.Nodup)
    (tail : List (Exit α)) (direction : Bool) (word : exits primary = ⟨direction,childPrimary⟩ :: tail)
    (payload : Exit α → Source α (List (Option τ))) (header : List τ) (values : ρ → τ) (rest : Source Nat ρ)
    (restAway : ∀ d ∈ rest.shape.leaves, d ≠ 0) (high terminal : ρ)
    {oldChild newChild : Source α (List (Option τ))} {budget : Nat}
    (execution : SourcePointer.Rearranges oldChild newChild budget) :
    let oldEncoding := encoding 0 primary (Function.update payload ⟨direction,childPrimary⟩ oldChild) header
    let newEncoding := encoding 0 primary (Function.update payload ⟨direction,childPrimary⟩ newChild) header
    SourcePointer.Rearranges (oldEncoding.tree values (.fork high (.leaf 0 terminal) rest))
      (newEncoding.tree values (.fork high (.leaf 0 terminal) rest)) (budget+20) := by
  have beforeView := override_root_view primary childPrimary distinct tail direction word
    payload oldChild header values rest restAway high terminal
  have afterView := override_root_view primary childPrimary distinct tail direction word
    payload newChild header values rest restAway high terminal
  have child : ProjectionLocal.Rearranges (some oldChild) (some newChild) budget := execution
  have lifted := activeView_boundary_rearranges none none
    ((encoding 0 primary payload header).wing values true rest) (some (.leaf primary.terminal []))
    ((encoding 0 primary payload header).wing values false rest) direction
    (rootActiveRecords (color 0 primary) values rest 0 high terminal header) child
  rw [← beforeView,← afterView] at lifted
  exact lifted

end TangoSquared.Paper20261030.PackedPrimary
