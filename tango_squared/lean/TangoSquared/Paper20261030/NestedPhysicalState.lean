import TangoSquared.Paper20261030.StoredComponentViews

/-! Exact views of a maintained physical state with one boundary component
expanded. The payload hypotheses concern only the other actual exits. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open ColoredStorage AuxiliaryComponent BoundaryObservations
open PreferredProjection PrimaryWings PackedPrimary PrimaryPhysical

variable {α : Type*} [DecidableEq α]

theorem storedTree_as_nested (starts : α → Nat) (components : Components α)
    (outer inner : PrefRouter α) (direction : Bool) (depth : Nat)
    (outerStart : starts outer.terminal = 0) (innerStart : starts inner.terminal = depth+1)
    (outerValid : ValidInput 0 outer (closed (components outer.terminal)))
    (innerValid : ValidInput (depth+1) inner (closed (components inner.terminal)))
    (payload : Exit α → Source α (List (Option (Datum Cached))))
    (outerSame : ∀ exit ∈ exits outer, exit ≠ ⟨direction,inner⟩ →
      storedPayload starts components exit = payload exit)
    (innerSame : ∀ exit ∈ exits inner, storedPayload starts components exit = payload exit) :
    storedTree starts components outer =
      nestedTree Datum.record payload canonicalHeaders outer inner direction depth
        (closed (components outer.terminal)) (closed (components inner.terminal)) := by
  let outerInput : Input outer Cached := ⟨0,closed (components outer.terminal),outerValid⟩
  let innerInput : Input inner Cached := ⟨depth+1,closed (components inner.terminal),innerValid⟩
  have outerView : storedTree starts components outer = outerInput.physical (storedPayload starts components) := by
    simpa only [outerStart] using storedTree_as_input starts components outer (by simpa only [outerStart] using outerValid)
  have innerView : storedTree starts components inner = innerInput.physical payload := by
    have view := storedTree_as_input starts components inner (by simpa only [innerStart] using innerValid)
    have view' : storedTree starts components inner = innerInput.physical (storedPayload starts components) := by
      simpa only [innerStart] using view
    exact view'.trans (innerInput.physical_payload_congr _ _ innerSame)
  rw [nestedTree_canonical outerInput innerInput direction depth rfl rfl,outerView]
  apply outerInput.physical_payload_congr
  intro exit member
  by_cases boundary : exit = ⟨direction,inner⟩
  · subst exit
    rw [Function.update_self]
    exact innerView
  · rw [Function.update_of_ne boundary]
    exact outerSame exit member boundary

theorem storedTree_head_frame {x : α} {depth : Nat} {before after subtree : PrefRouter α}
    (step : PrefRouter.HeadStep x depth before after)
    (beforeComponents afterComponents : Components α)
    (outsideOld : before.terminal ∉ subtree.leaves) (outsideNew : after.terminal ∉ subtree.leaves)
    (same : ∀ key, key ≠ before.terminal → key ≠ after.terminal → beforeComponents key = afterComponents key) :
    storedTree before.componentStart beforeComponents subtree =
      storedTree after.componentStart afterComponents subtree := by
  apply storedTree_congr
  · intro key member
    have oldOther : key ≠ before.terminal := fun h => outsideOld (h ▸ member)
    have newOther : key ≠ after.terminal := fun h => outsideNew (h ▸ member)
    exact (step.componentStart_unchanged key oldOther newOther).symm
  · intro key member
    exact same key (fun h => outsideOld (h ▸ member)) (fun h => outsideNew (h ▸ member))

end TangoSquared.Paper20261030.SecondaryDecomposition

namespace TangoSquared.Paper20261030.PrimaryWings

open PreferredProjection

variable {α : Type*} [DecidableEq α]

theorem head_boundary_terminals {x : α} {depth : Nat} {before after old incoming : PrefRouter α}
    {direction : Bool} (step : PrefRouter.HeadStep x depth before after)
    (oldPort : portAt 0 (exits before) depth = some ⟨direction,incoming⟩)
    (newPort : portAt 0 (exits after) depth = some ⟨!direction,old⟩) :
    before.terminal = old.terminal ∧ after.terminal = incoming.terminal := by
  obtain ⟨common,old',incoming',direction',length,oldEnd,newEnd,beforeWord,afterWord⟩ :=
    head_exit_decomposition step
  rw [beforeWord,← length,portAt_boundary] at oldPort
  rw [afterWord,← length,portAt_boundary] at newPort
  have incomingSame := congrArg (fun value : Option (Exit α) => value.map (fun e => e.subtree.terminal)) oldPort
  have oldSame := congrArg (fun value : Option (Exit α) => value.map (fun e => e.subtree.terminal)) newPort
  simp only [Option.map_some,Option.some.injEq] at incomingSame oldSame
  exact ⟨oldEnd.trans oldSame,newEnd.trans incomingSame⟩

end TangoSquared.Paper20261030.PrimaryWings
