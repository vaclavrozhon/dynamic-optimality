import TangoSquared.Paper20261030.MixedPacketRepairCorrectness

set_option autoImplicit false

/-!
# Temporary markers are absent from maintained repacked endpoints

Every retained block is recovered from the actually stored input. Whole
layers acquire the reached immutable id; excluding the reserved marker
from all immutable vertex ids therefore makes those layers ordinary.
Raw headers must themselves contain no temporary real-packet markers.
Virtual identifiers inside header datums are intentionally exempt.
-/

namespace TangoSquared.Paper20261030.MarkerFreePackets

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers

variable {κ α β ρ ι : Type*}

theorem append_iff (markerId : ι) (first last : PhysicalPacketStaging.Packet α ρ ι) :
    Packet markerId (first++last) ↔ Packet markerId first ∧ Packet markerId last := by
  simp only [Packet,List.mem_append,or_imp,forall_and]

theorem cons_iff (markerId : ι) (entry : Option (Datum α ρ ι)) (rest : PhysicalPacketStaging.Packet α ρ ι) :
    Packet markerId (entry::rest) ↔ Entry markerId entry ∧ Packet markerId rest := by
  simp only [Packet,List.mem_cons,or_imp,forall_and,forall_eq]

theorem header (markerId : ι) (virtual : VirtualHeaderController.Virtual α (PhysicalForestMetadata.Record ρ ι)) :
    Packet markerId [some (.header virtual),none] := by
  intro entry member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> trivial

theorem prepend_iff (markerId : ι) (records : List ρ) (packet : PhysicalPacketStaging.Packet α ρ ι) :
    Packet markerId (PhysicalPacketStaging.Context.prependLogical records packet) ↔ Packet markerId packet := by
  cases packet with
  | nil => rfl
  | cons entry rest => cases entry with
    | none => rfl
    | some datum => cases datum with
      | header => rfl
      | real record => simp only [PhysicalPacketStaging.Context.prependLogical,cons_iff,Entry]

theorem matches_base (markerId : ι) (base : PhysicalPacketStaging.Packet α ρ ι)
    (expression : Expression α ρ ι) (packet : PhysicalPacketStaging.Packet α ρ ι)
    (matching : PacketLayers.Matches base expression packet) (clear : Packet markerId packet) : Packet markerId base := by
  induction expression generalizing packet with
  | base => exact matching ▸ clear
  | raw records expression ih =>
    obtain ⟨tail,rfl,matching⟩ := matching
    exact ih tail matching ((append_iff _ _ _).mp clear).2
  | whole id records fields expression ih =>
    obtain ⟨id,fields,tail,rfl,matching⟩ := matching
    exact ih tail matching ((cons_iff _ _ _).mp clear).2
  | «prefix» records => exact (prepend_iff markerId records base).mp (matching ▸ clear)

theorem map_predicate {σ τ : Type*} (predicate : τ → Prop) (f : σ → τ) (source : Source β σ) :
    SourceRecordPredicate.Holds predicate (source.mapRecords f) ↔ SourceRecordPredicate.Holds (fun record => predicate (f record)) source := by
  induction source <;> simp_all only [Source.mapRecords,SourceRecordPredicate.leaf,SourceRecordPredicate.fork]

theorem stored_blocks (markerId : ι) (blocks : κ → Source β (PhysicalPacketStaging.Packet α ρ ι))
    (context : Source κ (Expression α ρ ι)) (source : Source β (Context.Cell α ρ ι))
    (stored : Reached.Stored blocks context source) (clear : SourceRecordPredicate.Holds (Vertex markerId) source) :
    ∀ key ∈ context.shape.leaves, SourceRecordPredicate.Holds (Packet markerId) (blocks key) := by
  induction context generalizing source with
  | leaf key expression =>
    intro other member
    have same : other = key := by simpa only [Source.shape,RouterProjection.Router.leaves,List.mem_singleton] using member
    subst other
    have baseClear := matches_base markerId (blocks key).rootRecord expression source.rootRecord.2 stored.2
      (SourceRecordPredicate.root _ _ clear)
    have sourceClear := (map_predicate (Packet markerId) Prod.snd source).mpr clear
    have result := SourceRecordPredicate.setRoot (Packet markerId) (source.mapRecords Prod.snd) (blocks key).rootRecord sourceClear baseClear
    rw [stored.1] at result
    exact result
  | fork expression left right ihl ihr => cases source with
    | leaf => exact False.elim stored
    | fork record l r =>
      obtain ⟨_,leftClear,rightClear⟩ := (SourceRecordPredicate.fork _ _ _ _).mp clear
      intro key member
      rcases List.mem_append.mp member with member | member
      · exact ihl l stored.2.1 leftClear key member
      · exact ihr r stored.2.2 rightClear key member

def RawClear (markerId : ι) : Expression α ρ ι → Prop
  | .base | .prefix _ => True
  | .whole _ _ _ expression => RawClear markerId expression
  | .raw records expression => Packet markerId records ∧ RawClear markerId expression

def RawTree (markerId : ι) : Source κ (Expression α ρ ι) → Prop
  | .leaf _ expression => RawClear markerId expression
  | .fork expression left right => RawClear markerId expression ∧ RawTree markerId left ∧ RawTree markerId right

theorem rebuilt_clear (markerId vertexId : ι) (ordinary : vertexId ≠ markerId)
    (base : PhysicalPacketStaging.Packet α ρ ι) (expression : Expression α ρ ι)
    (baseClear : Packet markerId base) (raw : RawClear markerId expression) : Packet markerId (rebuilt vertexId base expression) := by
  induction expression with
  | base => exact baseClear
  | raw records expression ih => exact (append_iff _ _ _).mpr ⟨raw.1,ih raw.2⟩
  | whole id records fields expression ih => exact (cons_iff _ _ _).mpr ⟨ordinary,ih raw⟩
  | «prefix» records => exact (prepend_iff _ _ _).mpr baseClear

private theorem root_set {σ : Type*} (source : Source β σ) (record : σ) :
    (source.setRoot record).rootRecord = record := by cases source <;> rfl

theorem repacked_clear (markerId : ι) (blocks : κ → Source β (PhysicalPacketStaging.Packet α ρ ι))
    (context : Source κ (Expression α ρ ι)) (source : Source β (Context.Cell α ρ ι))
    (repacked : Reached.Repacked blocks context source) (raw : RawTree markerId context)
    (blocksClear : ∀ key ∈ context.shape.leaves, SourceRecordPredicate.Holds (Packet markerId) (blocks key))
    (reserved : markerId ∉ source.inventory Prod.fst) : SourceRecordPredicate.Holds (Vertex markerId) source := by
  induction repacked with
  | leaf key expression block erases =>
    have blockClear := blocksClear key (by simp only [Source.shape,RouterProjection.Router.leaves,List.mem_singleton])
    have ordinary : block.rootRecord.1 ≠ markerId := by
      intro equal
      apply reserved
      have member := Structural.root_mem_inventory Prod.fst
        (block.setRoot (block.rootRecord.1,rebuilt block.rootRecord.1 (blocks key).rootRecord expression))
      simpa only [root_set,equal] using member
    have augmentedClear : SourceRecordPredicate.Holds (Vertex markerId) block := by
      apply (map_predicate (Packet markerId) Prod.snd block).mp
      rw [erases]
      exact blockClear
    exact SourceRecordPredicate.setRoot _ _ _ augmentedClear
      (rebuilt_clear markerId block.rootRecord.1 ordinary _ expression (SourceRecordPredicate.root _ _ blockClear) raw)
  | fork expression left right l r id hl hr ihl ihr =>
    simp only [Source.inventory_fork,Multiset.mem_add,Multiset.mem_singleton,not_or,and_assoc] at reserved
    refine (SourceRecordPredicate.fork _ _ _ _).mpr ⟨?_,?_,?_⟩
    · exact rebuilt_clear markerId id (fun equal => reserved.1 equal.symm) [] expression (by intro entry member; cases member) raw.1
    · exact ihl raw.2.1 (fun key member => blocksClear key (List.mem_append_left _ member)) reserved.2.1
    · exact ihr raw.2.2 (fun key member => blocksClear key (List.mem_append_right _ member)) reserved.2.2

end TangoSquared.Paper20261030.MarkerFreePackets
