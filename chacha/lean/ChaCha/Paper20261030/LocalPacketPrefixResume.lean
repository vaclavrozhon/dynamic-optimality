import ChaCha.Paper20261030.LocalPacketPrefixTransfer

set_option autoImplicit false

/-! Returning from a component's header register to its physical root,
then restoring the saved enclosing packet. The number of upward moves
is supplied by the fixed connector shape; it is at most two for the
three-piece component. The new immutable root id comes from a read. -/

namespace ChaCha.Paper20261030.PacketPrefixResume

open ColoredStorage SourcePointer SourceLocalProgram PhysicalPacketStaging PacketLayers

variable {α β ρ ι : Type*}

inductive State (α ρ ι : Type*) where
  | ascending (remaining : Nat)
  | reading
  | writing (fresh : Context.Cell α ρ ι)
  | done (newId : ι)

def ascend : Nat → State α ρ ι
  | 0 => .reading
  | n+1 => .ascending n

def program (saved : Packet α ρ ι) : Program (State α ρ ι) (Context.Cell α ρ ι)
  | .ascending remaining => .nav .up (ascend remaining)
  | .reading => .read (fun record _ => .writing
      (record.1,PacketPrefixTransfer.reidentify record.1 saved++record.2))
  | .writing fresh => .write fresh (.done fresh.1)
  | .done _ => .halt

theorem ascend_steps (saved : Packet α ρ ι) (focus : Source β (Context.Cell α ρ ι))
    (inside outside : List (Frame β (Context.Cell α ρ ι))) :
    Steps (program saved) (ascend inside.length) ⟨focus,inside++outside⟩
      .reading ⟨plug focus inside,outside⟩ [] inside.length := by
  induction inside generalizing focus with
  | nil => exact .nil _ _
  | cons frame rest ih => cases frame with
    | left record sibling => exact .next (program := program saved) (.nav rfl rfl) (ih (.fork record focus sibling))
    | right sibling record => exact .next (program := program saved) (.nav rfl rfl) (ih (.fork record sibling focus))

theorem run (saved : Packet α ρ ι) (focus : Source β (Context.Cell α ρ ι))
    (inside outside : List (Frame β (Context.Cell α ρ ι))) :
    Run (program saved) (ascend inside.length) ⟨focus,inside++outside⟩
      (.done (plug focus inside).rootRecord.1)
      ⟨PacketPrefixTransfer.output saved (plug focus inside),outside⟩
      [(plug focus inside).rootRecord] (inside.length+2) := by
  let root := plug focus inside
  have read : Step (program saved) .reading ⟨root,outside⟩
      (.writing (root.rootRecord.1,PacketPrefixTransfer.reidentify root.rootRecord.1 saved++root.rootRecord.2))
      ⟨root,outside⟩ (some root.rootRecord) :=
    .read (next := fun (record : Context.Cell α ρ ι) _ => State.writing
      (record.1,PacketPrefixTransfer.reidentify record.1 saved++record.2)) rfl
  have write : Step (program saved)
      (.writing (root.rootRecord.1,PacketPrefixTransfer.reidentify root.rootRecord.1 saved++root.rootRecord.2))
      ⟨root,outside⟩ (.done root.rootRecord.1)
      ⟨PacketPrefixTransfer.output saved root,outside⟩ none := .write rfl
  exact (ascend_steps saved focus inside outside).then_run (.next read (.next write (.halt rfl)))

end ChaCha.Paper20261030.PacketPrefixResume
