import ChaCha.Paper20261030.PhysicalEncodingInput
import ChaCha.Paper20261030.PrimaryExitDistinctness

/-!
# The physical head kernel for the actual primary exit decomposition

Boundary payloads are replaced by the two actual dormant components.
Distinct original keys imply distinct exits, so this replacement leaves
all other ports unchanged. The prefix and tail agreements required by the
physical kernel are derived from their depth intervals and the primary
exit words, rather than supplied as simulation assumptions.
-/

namespace ChaCha.Paper20261030.PackedPrimary

open ColoredStorage ProjectionLocal PreferredProjection PrimaryWings HeadBlocks

variable {α ρ τ : Type*} [DecidableEq α]

local instance primaryHeadKernelColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

theorem override_wing (primary : PrefRouter α) (distinct : primary.leaves.Nodup)
    (common tail : List (Exit α)) (boundary : Exit α) (word : exits primary = common ++ boundary :: tail)
    (payload : Exit α → Source α (List (Option τ))) (child : Source α (List (Option τ)))
    (header : List τ) (values : ρ → τ) (source : Source Nat ρ)
    (away : ∀ d ∈ source.shape.leaves, d ≠ common.length) (side : Bool) :
    (encoding 0 primary (Function.update payload boundary child) header).wing values side source =
      (encoding 0 primary payload header).wing values side source := by
  apply encoding_wing_congr
  · exact fun _ _ => rfl
  · intro d member exit present
    have unique := exits_nodup distinct
    rw [word] at unique present
    have different := portAt_ne_boundary common tail boundary unique d (away d member) exit present
    simp [Function.update,different]

set_option backward.isDefEq.respectTransparency false in
theorem decomposed_physical_head_kernel
    (before after old incoming : PrefRouter α) (common : List (Exit α)) (direction : Bool)
    (beforeDistinct : before.leaves.Nodup) (afterDistinct : after.leaves.Nodup)
    (oldEnd : before.terminal = old.terminal) (newEnd : after.terminal = incoming.terminal)
    (beforeWord : exits before = common ++ ⟨direction,incoming⟩ :: exits old)
    (afterWord : exits after = common ++ ⟨!direction,old⟩ :: exits incoming)
    (values : ρ → τ) (headPart oldTail newTail : Source Nat ρ)
    (prefixDepths : ∀ d ∈ headPart.shape.leaves, d < common.length)
    (oldDepths : ∀ d ∈ oldTail.shape.leaves, common.length < d)
    (newDepths : ∀ d ∈ newTail.shape.leaves, common.length < d)
    (low oldHigh newHigh terminal : ρ)
    (payload : Exit α → Source α (List (Option τ)))
    (beforeHeader afterHeader oldHeader incomingHeader : List τ) :
    let d := common.length
    let oldDormant := encoding (d+1) old payload oldHeader
    let incomingDormant := encoding (d+1) incoming payload incomingHeader
    let oldPayload := Function.update payload ⟨direction,incoming⟩
      (incomingDormant.tree values (.fork newHigh (.leaf d terminal) newTail))
    let newPayload := Function.update payload ⟨!direction,old⟩
      (oldDormant.tree values (.fork oldHigh (.leaf d terminal) oldTail))
    SourcePointer.Rearranges
      ((encoding 0 before oldPayload beforeHeader).tree values
        (.fork low headPart (.fork oldHigh (.leaf d terminal) oldTail)))
      ((encoding 0 after newPayload afterHeader).tree values
        (.fork low headPart (.fork newHigh (.leaf d terminal) newTail))) 288 := by
  dsimp only
  let d := common.length
  let oldDormant := encoding (d+1) old payload oldHeader
  let incomingDormant := encoding (d+1) incoming payload incomingHeader
  let oldChild := oldDormant.tree values (.fork oldHigh (.leaf d terminal) oldTail)
  let incomingChild := incomingDormant.tree values (.fork newHigh (.leaf d terminal) newTail)
  let oldPayload := Function.update payload ⟨direction,incoming⟩ incomingChild
  let newPayload := Function.update payload ⟨!direction,old⟩ oldChild
  let oldActive := encoding 0 before oldPayload beforeHeader
  let newActive := encoding 0 after newPayload afterHeader
  have oldPort : portAt 0 (exits before) d = some ⟨direction,incoming⟩ := by
    rw [beforeWord]; exact portAt_boundary _ _ _
  have newPort : portAt 0 (exits after) d = some ⟨!direction,old⟩ := by
    rw [afterWord]; exact portAt_boundary _ _ _
  have prefixPorts : ∀ depth ∈ headPart.shape.leaves,
      portAt 0 (exits before) depth = portAt 0 (exits after) depth := by
    intro depth member
    rw [beforeWord,afterWord,portAt_prefix _ _ _ (prefixDepths depth member),
      portAt_prefix _ _ _ (prefixDepths depth member)]
  have oldPorts : ∀ depth ∈ oldTail.shape.leaves,
      portAt 0 (exits before) depth = portAt (d+1) (exits old) depth := by
    intro depth member
    rw [beforeWord,portAt_tail _ _ _ _ (oldDepths depth member)]
  have newPorts : ∀ depth ∈ newTail.shape.leaves,
      portAt 0 (exits after) depth = portAt (d+1) (exits incoming) depth := by
    intro depth member
    rw [afterWord,portAt_tail _ _ _ _ (newDepths depth member)]
  have prefixAgreement : ∀ side, oldActive.wing values side headPart = newActive.wing values side headPart := by
    intro side
    have first := override_wing before beforeDistinct common (exits old) ⟨direction,incoming⟩ beforeWord
      payload incomingChild beforeHeader values headPart (fun depth member => Nat.ne_of_lt (prefixDepths depth member)) side
    have last := override_wing after afterDistinct common (exits incoming) ⟨!direction,old⟩ afterWord
      payload oldChild afterHeader values headPart (fun depth member => Nat.ne_of_lt (prefixDepths depth member)) side
    exact first.trans ((encoding_wing_congr 0 0 before after payload payload beforeHeader afterHeader values headPart side
      prefixPorts (fun _ _ _ _ => rfl)).trans last.symm)
  have oldAgreement : ∀ side, oldActive.wing values side oldTail = oldDormant.wing values side oldTail := by
    intro side
    have first := override_wing before beforeDistinct common (exits old) ⟨direction,incoming⟩ beforeWord
      payload incomingChild beforeHeader values oldTail (fun depth member => Nat.ne_of_gt (oldDepths depth member)) side
    exact first.trans (encoding_wing_congr 0 (d+1) before old payload payload beforeHeader oldHeader values oldTail side
      oldPorts (fun _ _ _ _ => rfl))
  have newAgreement : ∀ side, newActive.wing values side newTail = incomingDormant.wing values side newTail := by
    intro side
    have first := override_wing after afterDistinct common (exits incoming) ⟨!direction,old⟩ afterWord
      payload oldChild afterHeader values newTail (fun depth member => Nat.ne_of_gt (newDepths depth member)) side
    exact first.trans (encoding_wing_congr 0 (d+1) after incoming payload payload afterHeader incomingHeader values newTail side
      newPorts (fun _ _ _ _ => rfl))
  apply physical_head_exchange oldActive newActive oldDormant incomingDormant values headPart oldTail newTail
    d low oldHigh newHigh terminal direction
  · change color 0 before d = some direction
    simp [color,oldPort]
  · change color 0 after d = some (!direction)
    simp [color,newPort]
  · change color (d+1) old d = none
    simp [color,portAt]
  · change color (d+1) incoming d = none
    simp [color,portAt]
  · exact prefixAgreement
  · exact oldAgreement
  · exact newAgreement
  · exact oldEnd
  · exact newEnd
  · change oldPayload (label 0 before d) = incomingChild
    simp [oldPayload,label,oldPort]
  · change newPayload (label 0 after d) = oldChild
    simp [newPayload,label,newPort]

end ChaCha.Paper20261030.PackedPrimary
