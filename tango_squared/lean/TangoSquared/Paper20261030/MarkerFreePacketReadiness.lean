import TangoSquared.Paper20261030.PacketLayoutConditions

/-!
# Deriving residual-packet readiness from a marker-free stored input

Temporary marker ids occur only during staging and reassembly. At a
maintained endpoint, every real packet has an ordinary physical id.
Together with the canonical real-root shape this proves the `WingRoots`
precondition for both computed layouts. Header-internal virtual slots are
not physical real packets and are correctly exempt from this condition.
-/

namespace TangoSquared.Paper20261030.MarkerFreePackets

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers

variable {κ α β ρ ι η : Type*}

def Entry (markerId : ι) : Option (Datum α ρ ι) → Prop
  | some (.real ((id,_),_)) => id ≠ markerId
  | _ => True

def Packet (markerId : ι) (packet : PhysicalPacketStaging.Packet α ρ ι) : Prop :=
  ∀ entry ∈ packet, Entry markerId entry

def Vertex (markerId : ι) (record : Context.Cell α ρ ι) : Prop := Packet markerId record.2

theorem matches_ordinary (markerId : ι) (base : PhysicalPacketStaging.Packet α ρ ι) (expression : Expression α ρ ι)
    (packet : PhysicalPacketStaging.Packet α ρ ι) (matching : Matches base expression packet)
    (ready : Ready base expression) (clear : Packet markerId packet) : OrdinaryBase markerId base expression := by
  induction expression generalizing packet with
  | base => trivial
  | raw records rest ih =>
    obtain ⟨tail,rfl,matching⟩ := matching
    exact ih tail matching ready (fun entry member => clear entry (List.mem_append_right records member))
  | whole id records fields rest ih =>
    obtain ⟨actualId,actualFields,tail,rfl,matching⟩ := matching
    exact ih tail matching ready (fun entry member => clear entry (List.mem_cons_of_mem _ member))
  | «prefix» records =>
    obtain ⟨id,tail,fields,rest,baseEq⟩ := ready
    have present : Entry (α := α) markerId (some (.real ((id,records++tail),fields))) := by
      apply clear
      rw [matching,baseEq]
      exact List.mem_cons_self
    exact ⟨id,tail,fields,rest,baseEq,present⟩

theorem stored_ordinary (markerId : ι) (blocks : κ → Source β (PhysicalPacketStaging.Packet α ρ ι))
    (context : Source κ (Expression α ρ ι)) (source : Source β (Context.Cell α ρ ι))
    (represented : Reached.Stored blocks context source)
    (ready : PacketConditions.tree (fun base => Ready base (.prefix [])) blocks context)
    (clear : SourceRecordPredicate.Holds (Vertex markerId) source) : Reached.Ordinary markerId blocks context := by
  induction context generalizing source with
  | leaf key expression =>
    exact matches_ordinary markerId _ expression source.rootRecord.2 represented.2
      ((PacketConditions.packet_ready _ expression).mp ready) (SourceRecordPredicate.root _ _ clear)
  | fork expression left right ihl ihr =>
    cases source with
    | leaf => exact False.elim represented
    | fork record leftSource rightSource =>
      obtain ⟨rootClear,leftClear,rightClear⟩ := (SourceRecordPredicate.fork (Vertex markerId) record leftSource rightSource).mp clear
      exact ⟨matches_ordinary markerId [] expression record.2 represented.1
        ((PacketConditions.packet_ready [] expression).mp ready.1) rootClear,
        ihl leftSource represented.2.1 ready.2.1 leftClear,ihr rightSource represented.2.2 ready.2.2 rightClear⟩

theorem wing_roots (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool)
    (records : HeadBoundary.Records ρ η (Option Bool))
    (oldHeader incomingHeader : PhysicalPacketStaging.Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (blocks : Fin 8 → Source β (PhysicalPacketStaging.Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (context : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (found : HeadPacketLayout.before markerId bits direction records oldHeader incomingHeader = some context)
    (source : Source β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (represented : Reached.Stored blocks context source)
    (ready : PacketConditions.wings (fun base => Ready base (.prefix [])) bits blocks)
    (clear : SourceRecordPredicate.Holds (Vertex markerId) source) : HeadPacketLayout.WingRoots markerId bits blocks := by
  have layoutReady := (PacketConditions.before_iff (fun base => Ready base (.prefix [])) blocks markerId bits direction
    records oldHeader incomingHeader).mpr ready
  have ordinary := stored_ordinary markerId blocks context source represented (layoutReady context found) clear
  apply (PacketConditions.before_iff (fun base => OrdinaryBase markerId base (.prefix [])) blocks markerId bits direction
    records oldHeader incomingHeader).mp
  intro target actual
  have same : context = target := Option.some.inj (found.symm.trans actual)
  subst target
  exact (PacketConditions.tree_ordinary markerId blocks context).mpr ordinary

end TangoSquared.Paper20261030.MarkerFreePackets
