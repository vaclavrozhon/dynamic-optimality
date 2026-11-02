import ChaCha.Paper20261030.CanonicalMixedHeadInput
import ChaCha.Paper20261030.CanonicalMixedRootInput
import ChaCha.Paper20261030.MarkerFreePacketReadiness
import ChaCha.Paper20261030.LocalMixedHeadExchange

/-!
# Running the mixed head controller from the canonical input witnesses

The input witnesses are supplied by `CanonicalMixedHeadInput.input` and
`CanonicalMixedRootInput.input`. Real-root readiness and a marker-free
maintained endpoint discharge the old separate `WingRoots` assumption.
Both finite layouts exist because they contain a physical virtual bottom.
The unchanged controller still costs at most 692 operations.

This theorem stops at `Repacked`: physical neighbor repair and the full
primary read/prepare/restore schedule are not asserted here.
-/

namespace ChaCha.Paper20261030.HeadPacketLayout

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers

variable {κ α ρ ι η : Type*}

theorem primaryJoin_present (left right : Layout κ α ρ ι) :
    (primaryJoin left right).isSome = (left.isSome || right.isSome) := by cases left <;> cases right <;> rfl

theorem active_present (markerId : ι) (bits : Fin 8 → Bool) (l r tl b tr : Fin 8)
    (child : Layout (Fin 8) α (HeadBoundary.Record ρ η (Option Bool)) ι) (direction : Bool)
    (low high terminal : HeadBoundary.Record ρ η (Option Bool))
    (header : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    (active markerId bits l r tl b tr child direction low high terminal header).isSome = true := by
  simp only [active,primaryJoin_present,bottom,Option.isSome_some,Bool.or_true,Bool.true_or]

theorem after_exists (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool)
    (records : HeadBoundary.Records ρ η (Option Bool))
    (newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    ∃ context, after markerId bits direction records newHeader dormantHeader = some context := by
  have present : (after markerId bits direction records newHeader dormantHeader).isSome = true := active_present _ _ _ _ _ _ _ _ _ _ _ _ _
  cases found : after markerId bits direction records newHeader dormantHeader with
  | none => simp only [found,Option.isSome_none,reduceCtorEq] at present
  | some context => exact ⟨context,rfl⟩

end ChaCha.Paper20261030.HeadPacketLayout

namespace ChaCha.Paper20261030.ReadyMixedHeadExchange

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalPacketStaging PacketLayers HeadBoundary

variable {α β ρ ι η : Type*}

def Input (markerId : ι) (direction : Bool) (records : Records ρ η (Option Bool))
    (oldHeader incomingHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (source : Source β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι)) : Prop :=
  ∃ (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (context : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι)),
    HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits records) direction records oldHeader incomingHeader = some context ∧
    Reached.Stored blocks context source ∧
    PacketConditions.wings (fun base => Ready base (.prefix [])) (ObservedHeadBlueprint.bits records) blocks

theorem run (markerId : ι) (direction : Bool) (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : PacketAlignment.Neutral markerId newHeader) (dormantValid : PacketAlignment.Neutral markerId dormantHeader)
    (current : Cursor β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (input : Input markerId direction old oldHeader incomingHeader current.focus)
    (clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) current.focus)
    (aligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) current.tree) :
    ∃ blocks before after target reads cost,
      HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader = some before ∧
      HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader = some after ∧
      Run (MixedHeadExchange.program markerId
        (MixedHeadExchange.actions markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader)
        (Context.commands (after.mapRecords blueprint)))
        (.inl (.running (Context.commands (before.mapRecords blueprint)))) current
        (.inr (.inr (.running []))) target reads cost ∧
      Reached.Repacked blocks after target.focus ∧
      target.tree.inventory Prod.fst = current.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) target.tree ∧ cost ≤ 692 := by
  obtain ⟨blocks,before,beforeFound,stored,ready⟩ := input
  have ordinary := MarkerFreePackets.wing_roots markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader
    blocks before beforeFound current.focus stored ready clear
  obtain ⟨after,afterFound⟩ := HeadPacketLayout.after_exists markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader
  obtain ⟨target,reads,cost,run,repacked,_,identifiers,alignment,bound⟩ :=
    MixedHeadExchange.run markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader newValid dormantValid
      blocks ordinary before after beforeFound afterFound current stored aligned
  exact ⟨blocks,before,after,target,reads,cost,beforeFound,afterFound,run,repacked,identifiers,alignment,bound⟩

theorem execute {F : Type*} [DecidableEq F] (finger : F)
    (markerId : ι) (direction : Bool) (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : PacketAlignment.Neutral markerId newHeader) (dormantValid : PacketAlignment.Neutral markerId dormantHeader)
    (current : Cursor β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (input : Input markerId direction old oldHeader incomingHeader current.focus)
    (clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) current.focus)
    (aligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) current.tree)
    (config : MultiSourceProgram.Configuration F β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (located : MultiSourceSingleCursor.Represents finger current config) (valid : MultiSourceProgram.WellFormed config) :
    ∃ blocks before after target finalConfig reads cost,
      HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader = some before ∧
      HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader = some after ∧
      MultiSourceProgram.Run (MultiSourceSingleCursor.program (MixedHeadExchange.program markerId
        (MixedHeadExchange.actions markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader)
        (Context.commands (after.mapRecords blueprint))) finger)
        (some (.inl (.running (Context.commands (before.mapRecords blueprint))))) config
        (some (.inr (.inr (.running [])))) finalConfig reads cost ∧
      MultiSourceSingleCursor.Represents finger target finalConfig ∧ Reached.Repacked blocks after target.focus ∧
      finalConfig.tree.inventory Prod.fst = config.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) finalConfig.tree ∧
      MultiSourceProgram.WellFormed finalConfig ∧ cost ≤ 692 := by
  obtain ⟨blocks,before,beforeFound,stored,ready⟩ := input
  have ordinary := MarkerFreePackets.wing_roots markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader
    blocks before beforeFound current.focus stored ready clear
  obtain ⟨after,afterFound⟩ := HeadPacketLayout.after_exists markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader
  have configAligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) config.tree := located.1.symm ▸ aligned
  obtain ⟨finalConfig,target,reads,cost,run,located,repacked,identifiers,alignment,wellFormed,bound⟩ :=
    MixedHeadExchange.execute finger markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader newValid dormantValid
      blocks ordinary before after beforeFound afterFound current stored config located valid configAligned
  exact ⟨blocks,before,after,target,finalConfig,reads,cost,beforeFound,afterFound,run,located,repacked,identifiers,alignment,wellFormed,bound⟩

end ChaCha.Paper20261030.ReadyMixedHeadExchange
