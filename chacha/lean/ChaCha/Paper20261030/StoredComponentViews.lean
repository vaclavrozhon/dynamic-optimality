import ChaCha.Paper20261030.PhysicalStateLocality

/-! Expand one actual component while retaining the complete representations
of its exits as payloads. Only payload values at actual exits matter. -/

namespace ChaCha.Paper20261030.SourcePayloads

open ColoredStorage

variable {α β ρ : Type*}

theorem graft_congr (before after : α → Source β (List (Option ρ))) (source : Source α (List ρ))
    (same : ∀ key ∈ source.shape.leaves, before key = after key) :
    graft before source = graft after source := by
  induction source with
  | leaf key records => simp only [graft,same key (by simp [Source.shape,RouterProjection.Router.leaves])]
  | fork records left right ihl ihr =>
    have leftSame := ihl (fun key h => same key (List.mem_append_left _ h))
    have rightSame := ihr (fun key h => same key (List.mem_append_right _ h))
    simp only [graft,leftSame,rightSame]

end ChaCha.Paper20261030.SourcePayloads

namespace ChaCha.Paper20261030.PrimaryPhysical

open ColoredStorage PrimaryWings

variable {α ρ : Type*}

theorem graftWing_congr (before after : Exit α → Source α (List (Option ρ))) (wing : RoutingWing α ρ)
    (same : ∀ exit ∈ routingWord wing, before exit = after exit) :
    graftWing before wing = graftWing after wing := by
  cases wing with
  | none => rfl
  | some source => exact congrArg some (SourcePayloads.graft_congr before after source same)

end ChaCha.Paper20261030.PrimaryPhysical

namespace ChaCha.Paper20261030.PackedPrimary

open ColoredStorage PreferredProjection PrimaryWings PrimaryPhysical

variable {α ρ : Type*} [DecidableEq α]

theorem Input.physical_payload_congr {primary : PrefRouter α} (input : Input primary ρ)
    (before after : Exit α → Source α (List (Option (Datum ρ))))
    (same : ∀ exit ∈ exits primary, before exit = after exit) :
    input.physical before = input.physical after := by
  unfold Input.physical
  congr 1
  · apply graftWing_congr
    rw [input.completePlan_words.1]
    exact fun exit h => same exit (List.mem_filter.mp h).1
  · apply graftWing_congr
    rw [input.completePlan_words.2]
    exact fun exit h => same exit (List.mem_filter.mp (List.mem_reverse.mp h)).1

end ChaCha.Paper20261030.PackedPrimary

namespace ChaCha.Paper20261030.SecondaryDecomposition

open ColoredStorage AuxiliaryComponent BoundaryObservations
open PreferredProjection PrimaryWings PackedPrimary PrimaryPhysical

variable {α : Type*} [DecidableEq α]

def storedPayload (starts : α → Nat) (components : Components α) (exit : Exit α) :
    Source α (List (Option (Datum Cached))) := storedTree starts components exit.subtree

theorem storedTree_as_input (starts : α → Nat) (components : Components α) (primary : PrefRouter α)
    (valid : ValidInput (starts primary.terminal) primary (closed (components primary.terminal))) :
    storedTree starts components primary =
      (Input.mk (starts primary.terminal) (closed (components primary.terminal)) valid).physical
        (storedPayload starts components) := by
  let input : Input primary Cached := ⟨starts primary.terminal,closed (components primary.terminal),valid⟩
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

theorem physicalState_as_input (primary : PrefRouter α) (components : Components α)
    (valid : ValidInput 0 primary (closed (components primary.terminal))) :
    physicalState primary components =
      (Input.mk 0 (closed (components primary.terminal)) valid).physical
        (storedPayload primary.componentStart components) := by
  simpa only [physicalState,PrefRouter.componentStart_terminal] using
    storedTree_as_input primary.componentStart components primary
      (by simpa only [PrefRouter.componentStart_terminal] using valid)

theorem storedPayload_update_active (primary : PrefRouter α) (distinct : primary.leaves.Nodup)
    (components : Components α) (fresh : AuxiliaryComponent Nat Nat (Tagged Payload))
    {exit : Exit α} (member : exit ∈ exits primary) :
    storedPayload primary.componentStart (Function.update components primary.terminal fresh) exit =
      storedPayload primary.componentStart components exit := by
  apply storedTree_congr
  · exact fun _ _ => rfl
  · intro key h
    have other : key ≠ primary.terminal := fun same => exit_excludes_terminal distinct member (same ▸ h)
    exact Function.update_of_ne other _ _

end ChaCha.Paper20261030.SecondaryDecomposition
