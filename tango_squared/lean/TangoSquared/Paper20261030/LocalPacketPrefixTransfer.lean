import TangoSquared.Paper20261030.PacketLayerMarkerFree
import TangoSquared.Paper20261030.SourceProgramComposition

set_option autoImplicit false

/-!
# Moving an enclosing packet prefix with a changing physical root

The controller reads and removes a prefix of a specified scalar length,
runs its child controller, then reads the new root and reinstalls the
saved prefix. Real datums receive the reached vertex's immutable id;
virtual headers and every other field retain their contents. The four
extra operations are actual reads and writes. Repairing the enclosing
parent's child descriptor is a separate operation.

The prefix length must be supplied by the enclosing layout. The saved
prefix and temporary write record are obtained from actual reads, not
from the ghost source trees in the correctness theorem.
-/

namespace TangoSquared.Paper20261030.PacketPrefixTransfer

open ColoredStorage SourcePointer SourceLocalProgram PhysicalPacketStaging PacketLayers

variable {α β ρ ι σ : Type*}

def reidentifyEntry (vertexId : ι) : Option (Datum α ρ ι) → Option (Datum α ρ ι)
  | some (.real ((_,records),fields)) => some (.real ((vertexId,records),fields))
  | entry => entry

def reidentify (vertexId : ι) (packet : Packet α ρ ι) : Packet α ρ ι :=
  packet.map (reidentifyEntry vertexId)

def attach (packet : Packet α ρ ι) (source : Source β (Context.Cell α ρ ι)) : Source β (Context.Cell α ρ ι) :=
  source.setRoot (source.rootRecord.1,packet++source.rootRecord.2)

def output (packet : Packet α ρ ι) (source : Source β (Context.Cell α ρ ι)) : Source β (Context.Cell α ρ ι) :=
  attach (reidentify source.rootRecord.1 packet) source

private theorem root_set {τ : Type*} (source : Source β τ) (record : τ) :
    (source.setRoot record).rootRecord = record := by cases source <;> rfl

private theorem strip_attach (packet : Packet α ρ ι) (source : Source β (Context.Cell α ρ ι)) :
    (attach packet source).setRoot source.rootRecord = source := by
  cases source <;> rfl

inductive State (σ α ρ ι : Type*) where
  | start
  | strip (saved : Packet α ρ ι) (fresh : Context.Cell α ρ ι)
  | running (saved : Packet α ρ ι) (oldId : ι) (state : σ)
  | restore (fresh : Context.Cell α ρ ι) (oldId : ι) (last : σ)
  | done (oldId newId : ι) (last : σ)

def program (count : Nat) (kernel : Program σ (Context.Cell α ρ ι)) (initial : σ) :
    Program (State σ α ρ ι) (Context.Cell α ρ ι)
  | .start => .read (fun record _ => .strip (record.2.take count) (record.1,record.2.drop count))
  | .strip saved fresh => .write fresh (.running saved fresh.1 initial)
  | .running saved oldId state => match kernel state with
      | .halt => .read (fun record _ => .restore (record.1,reidentify record.1 saved++record.2) oldId state)
      | instruction => instruction.mapState (.running saved oldId)
  | .restore fresh oldId last => .write fresh (.done oldId fresh.1 last)
  | .done _ _ _ => .halt

theorem running_code (count : Nat) (kernel : Program σ (Context.Cell α ρ ι)) (initial : σ)
    (saved : Packet α ρ ι) (oldId : ι) (state : σ) (active : kernel state ≠ .halt) :
    program count kernel initial (.running saved oldId state) = (kernel state).mapState (.running saved oldId) := by
  simp only [program]

theorem lift (packet : Packet α ρ ι) (kernel : Program σ (Context.Cell α ρ ι)) (initial last : σ)
    (before after : Source β (Context.Cell α ρ ι)) (outside finalOutside : List (Frame β (Context.Cell α ρ ι)))
    {reads cost} (execution : Run kernel initial ⟨before,outside⟩ last ⟨after,finalOutside⟩ reads cost)
    (halted : kernel last = .halt) :
    ∃ observed, Run (program packet.length kernel initial) .start ⟨attach packet before,outside⟩
      (.done before.rootRecord.1 after.rootRecord.1 last) ⟨output packet after,finalOutside⟩ observed (cost+4) := by
  let code := program packet.length kernel initial
  have first : Step code .start ⟨attach packet before,outside⟩
      (.strip packet before.rootRecord) ⟨attach packet before,outside⟩
      (some (attach packet before).rootRecord) := by
    have step := Step.read (program := code) (state := .start) (cursor := ⟨attach packet before,outside⟩)
      (next := fun record _ => State.strip (record.2.take packet.length) (record.1,record.2.drop packet.length)) rfl
    simpa only [attach,root_set,List.take_left,List.drop_left,Prod.mk.eta] using step
  have stripped : Step code (.strip packet before.rootRecord) ⟨attach packet before,outside⟩
      (.running packet before.rootRecord.1 initial) ⟨before,outside⟩ none := by
    have step := Step.write (program := code) (state := .strip packet before.rootRecord)
      (cursor := ⟨attach packet before,outside⟩) (fresh := before.rootRecord) rfl
    simpa only [strip_attach] using step
  have body := execution.map_prefix (State.running packet before.rootRecord.1)
    (running_code packet.length kernel initial packet before.rootRecord.1)
  have observed : Step code (.running packet before.rootRecord.1 last) ⟨after,finalOutside⟩
      (.restore (after.rootRecord.1,reidentify after.rootRecord.1 packet++after.rootRecord.2) before.rootRecord.1 last)
      ⟨after,finalOutside⟩ (some after.rootRecord) :=
    Step.read (program := code) (next := fun record _ => State.restore (record.1,reidentify record.1 packet++record.2) before.rootRecord.1 last)
      (by simp only [code,program,halted])
  have restored : Step code
      (.restore (after.rootRecord.1,reidentify after.rootRecord.1 packet++after.rootRecord.2) before.rootRecord.1 last)
      ⟨after,finalOutside⟩ (.done before.rootRecord.1 after.rootRecord.1 last) ⟨output packet after,finalOutside⟩ none := Step.write rfl
  have all := first.prefix.append (stripped.prefix.append (body.append (observed.prefix.append restored.prefix)))
  exact ⟨_,by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all.run rfl⟩

theorem reidentify_length (vertexId : ι) (packet : Packet α ρ ι) :
    (reidentify vertexId packet).length = packet.length := List.length_map _

theorem reidentify_alignment (markerId vertexId : ι) (packet : Packet α ρ ι) :
    PacketAlignment.Aligned markerId vertexId (reidentify vertexId packet) := by
  intro entry member
  obtain ⟨old,_,rfl⟩ := List.mem_map.mp member
  cases old with
  | none => trivial
  | some datum => cases datum with
    | header => trivial
    | real record => exact Or.inr rfl

theorem reidentify_clear (markerId vertexId : ι) (ordinary : vertexId ≠ markerId) (packet : Packet α ρ ι) :
    MarkerFreePackets.Packet markerId (reidentify vertexId packet) := by
  intro entry member
  obtain ⟨old,_,rfl⟩ := List.mem_map.mp member
  cases old with
  | none => trivial
  | some datum => cases datum with
    | header => trivial
    | real record => exact ordinary

theorem identifiers (packet : Packet α ρ ι) (source : Source β (Context.Cell α ρ ι)) :
    (output packet source).inventory Prod.fst = source.inventory Prod.fst :=
  Source.inventory_setRoot Prod.fst source _ rfl

theorem output_root_id (packet : Packet α ρ ι) (source : Source β (Context.Cell α ρ ι)) :
    (output packet source).rootRecord.1 = source.rootRecord.1 := by
  simp only [output,attach,root_set]

theorem output_alignment (markerId : ι) (packet : Packet α ρ ι) (source : Source β (Context.Cell α ρ ι))
    (valid : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) source) :
    SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) (output packet source) := by
  apply SourceRecordPredicate.setRoot _ source _ valid
  exact PacketAlignment.append markerId source.rootRecord.1 _ _
    (reidentify_alignment markerId source.rootRecord.1 packet) (SourceRecordPredicate.root _ _ valid)

theorem output_clear (markerId : ι) (packet : Packet α ρ ι) (source : Source β (Context.Cell α ρ ι))
    (ordinary : source.rootRecord.1 ≠ markerId)
    (valid : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) source) :
    SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) (output packet source) := by
  apply SourceRecordPredicate.setRoot _ source _ valid
  exact (MarkerFreePackets.append_iff markerId _ _).mpr
    ⟨reidentify_clear markerId source.rootRecord.1 ordinary packet,SourceRecordPredicate.root _ _ valid⟩

/-- Header contents are unchanged, even if their local slot ids happen
to coincide with the old physical root id. -/
theorem reidentify_header (vertexId : ι)
    (virtual : VirtualHeaderController.Virtual α (PhysicalForestMetadata.Record ρ ι)) :
    reidentify vertexId [some (.header virtual),none] = [some (.header virtual),none] := rfl

theorem reidentify_leaf (vertexId old : ι) (records : List ρ) (fields : Structural.Fields ι Unit) :
    reidentify (α := α) vertexId [some (.real ((old,records),fields)),none] =
      [some (.real ((vertexId,records),fields)),none] := rfl

end TangoSquared.Paper20261030.PacketPrefixTransfer
