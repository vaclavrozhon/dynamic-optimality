import ChaCha.Paper20261030.LocalPacketParentRepair

set_option autoImplicit false

/-!
# An actual controller for an operation under an enclosing packet prefix

The prefix-transfer read supplies both root ids to the parent repair.
The controller adds at most eleven operations when a physical parent is
present, and four when it is absent. The caller supplies a scalar prefix
length and parent-presence flag from its maintained enclosing layout.
Identifying that layout through the full primary loop remains separate.
-/

namespace ChaCha.Paper20261030.EnclosingPacketOperation

open ColoredStorage SourcePointer SourceLocalProgram PhysicalPacketStaging PacketLayers

variable {α β ρ ι σ : Type*} [DecidableEq ι]

inductive State (σ α ρ ι : Type*) where
  | transferring (state : PacketPrefixTransfer.State σ α ρ ι)
  | repairing (old fresh : ι) (last : σ) (state : PacketParentRepair.State α ρ ι)
  | done (last : σ)

def finishTransfer (hasParent : Bool) : PacketPrefixTransfer.State σ α ρ ι → State σ α ρ ι
  | .done old fresh last => if hasParent then .repairing old fresh last .start else .done last
  | state => .transferring state

def finishParent (old fresh : ι) (last : σ) : PacketParentRepair.State α ρ ι → State σ α ρ ι
  | .done => .done last
  | state => .repairing old fresh last state

def program (count : Nat) (hasParent : Bool) (kernel : Program σ (Context.Cell α ρ ι)) (initial : σ) :
    Program (State σ α ρ ι) (Context.Cell α ρ ι)
  | .transferring state => (PacketPrefixTransfer.program count kernel initial state).mapState (finishTransfer hasParent)
  | .repairing old fresh last state => (PacketParentRepair.program old fresh state).mapState (finishParent old fresh last)
  | .done _ => .halt

theorem transfer_code (count : Nat) (hasParent : Bool) (kernel : Program σ (Context.Cell α ρ ι)) (initial : σ)
    (state : PacketPrefixTransfer.State σ α ρ ι) (active : PacketPrefixTransfer.program count kernel initial state ≠ .halt) :
    program count hasParent kernel initial (finishTransfer hasParent state) =
      (PacketPrefixTransfer.program count kernel initial state).mapState (finishTransfer hasParent) := by
  cases state with
  | done => exact False.elim (active rfl)
  | start | strip | running | restore => rfl

theorem parent_code (count : Nat) (hasParent : Bool) (kernel : Program σ (Context.Cell α ρ ι)) (initial : σ)
    (old fresh : ι) (last : σ) (state : PacketParentRepair.State α ρ ι)
    (active : PacketParentRepair.program old fresh state ≠ .halt) :
    program count hasParent kernel initial (finishParent old fresh last state) =
      (PacketParentRepair.program old fresh state).mapState (finishParent old fresh last) := by
  cases state with
  | done => exact False.elim (active rfl)
  | start | readParent | writeParent | toLeft | inspectLeft | fromLeft | toRight => rfl

theorem root (packet : Packet α ρ ι) (kernel : Program σ (Context.Cell α ρ ι)) (initial last : σ)
    (before after : Source β (Context.Cell α ρ ι)) {reads cost}
    (execution : Run kernel initial ⟨before,[]⟩ last ⟨after,[]⟩ reads cost)
    (halted : kernel last = .halt) :
    ∃ observed, Run (program packet.length false kernel initial) (.transferring .start)
      ⟨PacketPrefixTransfer.attach packet before,[]⟩ (.done last)
      ⟨PacketPrefixTransfer.output packet after,[]⟩ observed (cost+4) := by
  obtain ⟨observed,transfer⟩ := PacketPrefixTransfer.lift packet kernel initial last before after [] [] execution halted
  exact ⟨observed,(transfer.map_prefix (finishTransfer false) (transfer_code packet.length false kernel initial)).run rfl⟩

theorem nested (packet : Packet α ρ ι) (kernel : Program σ (Context.Cell α ρ ι)) (initial last : σ)
    (before after : Source β (Context.Cell α ρ ι))
    (outside : List (Frame β (Context.Cell α ρ ι)))
    (parent : Frame β (Context.Cell α ρ ι)) (rest : List (Frame β (Context.Cell α ρ ι)))
    {reads cost} (execution : Run kernel initial ⟨before,outside⟩ last ⟨after,parent::rest⟩ reads cost)
    (halted : kernel last = .halt)
    (unique : ((plug after (parent::rest)).inventory Prod.fst).Nodup) :
    ∃ observed total, Run (program packet.length true kernel initial) (.transferring .start)
      ⟨PacketPrefixTransfer.attach packet before,outside⟩ (.done last)
      ⟨PacketPrefixTransfer.output packet after,PacketParentRepair.frame before.rootRecord.1 after.rootRecord.1 parent::rest⟩
      observed total ∧ total ≤ cost+11 := by
  obtain ⟨observed,transfer⟩ := PacketPrefixTransfer.lift packet kernel initial last before after outside (parent::rest) execution halted
  have body := transfer.map_prefix (finishTransfer true) (transfer_code packet.length true kernel initial)
  have finalUnique : ((plug (PacketPrefixTransfer.output packet after) (parent::rest)).inventory Prod.fst).Nodup := by
    rw [plug_inventory_congr Prod.fst (PacketPrefixTransfer.identifiers packet after) (parent::rest)]
    exact unique
  obtain ⟨parentReads,parentCost,repaired,bound⟩ :=
    PacketParentRepair.run before.rootRecord.1 (PacketPrefixTransfer.output packet after) parent rest finalUnique
  rw [PacketPrefixTransfer.output_root_id] at repaired
  have ending := repaired.map_prefix (finishParent before.rootRecord.1 after.rootRecord.1 last)
    (parent_code packet.length true kernel initial before.rootRecord.1 after.rootRecord.1 last)
  exact ⟨_,_,(body.append ending).run rfl,by omega⟩

end ChaCha.Paper20261030.EnclosingPacketOperation
