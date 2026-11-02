import ChaCha.Paper20261030.SplayAuxiliaryPhysicalState
import ChaCha.Paper20261030.NestedPhysicalState

/-! Exact local and nested views of the physical ordinary-splay state.
Only the components belonging to the given original-key subtree matter. -/

namespace ChaCha.Paper20261030.SplayAuxiliary.Physical

open ColoredStorage SecondaryDecomposition
open PreferredProjection PrimaryWings PackedPrimary PrimaryPhysical

variable {α : Type*} [DecidableEq α]

theorem storedTree_congr (beforeStarts afterStarts : α → Nat)
    (beforeComponents afterComponents : Global.Table α) (subtree : PrefRouter α)
    (startsSame : ∀ key ∈ subtree.leaves, beforeStarts key = afterStarts key)
    (componentsSame : ∀ key ∈ subtree.leaves, beforeComponents key = afterComponents key) :
    storedTree beforeStarts beforeComponents subtree = storedTree afterStarts afterComponents subtree := by
  have planSame : storedPlan beforeStarts beforeComponents subtree = storedPlan afterStarts afterComponents subtree := by
    simp only [storedPlan,startsSame _ subtree.terminal_mem,componentsSame _ subtree.terminal_mem]
  have headerSame : storedHeader beforeStarts beforeComponents subtree = storedHeader afterStarts afterComponents subtree := by
    simp only [storedHeader,startsSame _ subtree.terminal_mem,componentsSame _ subtree.terminal_mem]
  have payloadSame :
      (fun e => if member : e ∈ exits subtree then storedTree beforeStarts beforeComponents e.subtree
        else Source.leaf subtree.terminal []) =
      (fun e => if member : e ∈ exits subtree then storedTree afterStarts afterComponents e.subtree
        else Source.leaf subtree.terminal []) := by
    funext e
    split_ifs with member
    · exact storedTree_congr beforeStarts afterStarts beforeComponents afterComponents e.subtree
        (fun key h => startsSame key (exit_leaves_subset member key h))
        (fun key h => componentsSame key (exit_leaves_subset member key h))
    · rfl
  change PrimaryPhysical.expand _ _ subtree = PrimaryPhysical.expand _ _ subtree
  rw [PrimaryPhysical.expand,PrimaryPhysical.expand]
  change PrimaryPhysical.component (graftWing _ _) (graftWing _ _) _ _ =
    PrimaryPhysical.component (graftWing _ _) (graftWing _ _) _ _
  dsimp only [storedTree] at payloadSame
  rw [payloadSame,planSame,headerSame]
termination_by subtree.leaves.length
decreasing_by exact exit_smaller (by assumption)

end ChaCha.Paper20261030.SplayAuxiliary.Physical

namespace ChaCha.Paper20261030.SplayAuxiliary.Physical

open ColoredStorage SecondaryDecomposition
open PreferredProjection PrimaryWings PackedPrimary PrimaryPhysical

variable {α : Type*} [DecidableEq α]

def storedPayload (starts : α → Nat) (components : Global.Table α) (exit : Exit α) :
    Source α (List (Option (Datum Nat))) := storedTree starts components exit.subtree

theorem storedTree_as_input (starts : α → Nat) (components : Global.Table α) (primary : PrefRouter α)
    (valid : ValidInput (starts primary.terminal) primary (closed (components primary.terminal))) :
    storedTree starts components primary =
      (Input.mk (starts primary.terminal) (closed (components primary.terminal)) valid).physical
        (storedPayload starts components) := by
  let input : Input primary Nat := ⟨starts primary.terminal,closed (components primary.terminal),valid⟩
  have planSame : storedPlan starts components primary = input.completePlan := rfl
  have headerSame : storedHeader starts components primary = input.completeHeader := canonicalHeaders_input input
  change PrimaryPhysical.expand _ _ primary = input.physical _
  rw [PrimaryPhysical.expand,planSame,headerSame]
  unfold Input.physical
  congr 1
  · apply graftWing_congr
    rw [input.completePlan_words.1]
    intro exit h
    simp only [dif_pos (List.mem_filter.mp h).1]
    rfl
  · apply graftWing_congr
    rw [input.completePlan_words.2]
    intro exit h
    simp only [dif_pos (List.mem_filter.mp (List.mem_reverse.mp h)).1]
    rfl

theorem physicalState_as_input (primary : PrefRouter α) (components : Global.Table α)
    (valid : ValidInput 0 primary (closed (components primary.terminal))) :
    physicalState primary components =
      (Input.mk 0 (closed (components primary.terminal)) valid).physical
        (storedPayload primary.componentStart components) := by
  simpa only [physicalState,PrefRouter.componentStart_terminal] using
    storedTree_as_input primary.componentStart components primary
      (by simpa only [PrefRouter.componentStart_terminal] using valid)

theorem storedPayload_update_active (primary : PrefRouter α) (distinct : primary.leaves.Nodup)
    (components : Global.Table α) (fresh : Global.Component)
    {exit : Exit α} (member : exit ∈ exits primary) :
    storedPayload primary.componentStart (Function.update components primary.terminal fresh) exit =
      storedPayload primary.componentStart components exit := by
  apply storedTree_congr
  · exact fun _ _ => rfl
  · intro key h
    have other : key ≠ primary.terminal := fun same => exit_excludes_terminal distinct member (same ▸ h)
    exact Function.update_of_ne other _ _

end ChaCha.Paper20261030.SplayAuxiliary.Physical

namespace ChaCha.Paper20261030.SplayAuxiliary.Physical

open ColoredStorage SecondaryDecomposition
open PreferredProjection PrimaryWings PackedPrimary PrimaryPhysical

variable {α : Type*} [DecidableEq α]

theorem storedTree_as_nested (starts : α → Nat) (components : Global.Table α)
    (outer inner : PrefRouter α) (direction : Bool) (depth : Nat)
    (outerStart : starts outer.terminal = 0) (innerStart : starts inner.terminal = depth+1)
    (outerValid : ValidInput 0 outer (closed (components outer.terminal)))
    (innerValid : ValidInput (depth+1) inner (closed (components inner.terminal)))
    (payload : Exit α → Source α (List (Option (Datum Nat))))
    (outerSame : ∀ exit ∈ exits outer, exit ≠ ⟨direction,inner⟩ →
      storedPayload starts components exit = payload exit)
    (innerSame : ∀ exit ∈ exits inner, storedPayload starts components exit = payload exit) :
    storedTree starts components outer =
      nestedTree Datum.record payload canonicalHeaders outer inner direction depth
        (closed (components outer.terminal)) (closed (components inner.terminal)) := by
  let outerInput : Input outer Nat := ⟨0,closed (components outer.terminal),outerValid⟩
  let innerInput : Input inner Nat := ⟨depth+1,closed (components inner.terminal),innerValid⟩
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
    (beforeComponents afterComponents : Global.Table α)
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

end ChaCha.Paper20261030.SplayAuxiliary.Physical
