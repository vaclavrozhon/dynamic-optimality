import TangoSquared.Paper20261030.LocalReachedPacketStaging
import TangoSquared.Paper20261030.LocalHeadReassembleRepack

/-!
# A single local program for the mixed-packet head exchange

The program stages the reached boundary, performs the checked immutable-id
reassembly, and repacks its output. Both finite layouts are computed from
observed boundary records and stored headers. The input `Stored` relation
accounts for actual packet layers, including nested attachment delimiters;
the output `Repacked` relation retains opaque blocks and uses reached ids.

The bound is 692 operations. Boundary preparation, acquisition of the
input records and headers, physical neighbor repair, and restoration of
balanced components remain separate obligations of the full algorithm.
-/

namespace TangoSquared.Paper20261030.MixedHeadExchange

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalPacketStaging PacketLayers
open PacketAlignment HeadBoundary

variable {α β ρ ι η : Type*}

abbrev State (α ρ ι : Type*) := Sum
  (RecordEditScript.State Blueprint (PacketLayers.Context.Cell α ρ ι)) (HeadReassembleRepack.State α ρ ι)

def program (markerId : ι) (actions : List (LocalRecordActions.Action (Option (Datum α ρ ι))))
    (repackCommands : List (RecordEditScript.Command Blueprint)) :
    Program (State α ρ ι) (PacketLayers.Context.Cell α ρ ι) :=
  Sequential.program (RecordEditScript.program (PacketLayers.Context.staging markerId))
    (HeadReassembleRepack.program repackCommands) (.inl (.ready (.ready actions)))

def actions (markerId : ι) (direction : Bool) (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :=
  OrderedContext.Local.decoratedActions (ObservedHeadBlueprint.bits old)
    (ObservedHeadBlueprint.beforeContext (markerValue markerId) direction old oldHeader incomingHeader)
    (ObservedHeadBlueprint.afterContext (markerValue markerId) direction fresh newHeader dormantHeader)

theorem run (markerId : ι) (direction : Bool) (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : Neutral markerId newHeader) (dormantValid : Neutral markerId dormantHeader)
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (ordinary : HeadPacketLayout.WingRoots markerId (ObservedHeadBlueprint.bits old) blocks)
    (before after : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (beforeFound : HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader = some before)
    (afterFound : HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader = some after)
    (current : Cursor β (ι × Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (represented : Reached.Stored blocks before current.focus)
    (aligned : SourceRecordPredicate.Holds (Predicate markerId) current.tree) :
    ∃ target reads cost,
      Run (program markerId (actions markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader)
        (PacketLayers.Context.commands (after.mapRecords blueprint)))
        (.inl (.running (PacketLayers.Context.commands (before.mapRecords blueprint)))) current
        (.inr (.inr (.running []))) target reads cost ∧
      Reached.Repacked blocks after target.focus ∧
      target.ancestors.map (Frame.mapRecords Prod.snd) = current.ancestors.map (Frame.mapRecords Prod.snd) ∧
      target.tree.inventory Prod.fst = current.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (Predicate markerId) target.tree ∧ cost ≤ 692 := by
  have initialAligned : SourceRecordPredicate.Holds (Predicate markerId) current.focus := by
    intro record member
    exact aligned record (Multiset.mem_of_le (inventory_le_plug id current.focus current.ancestors) member)
  obtain ⟨staged,stageRun,stagedErases,stagedIds,stagedAligned⟩ := Reached.stage markerId blocks before
    (HeadPacketLayout.before_good markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader blocks ordinary before beforeFound)
    current.focus represented initialAligned
  obtain ⟨stageReads,stageRun⟩ := stageRun current.ancestors
  let middle : Cursor β (ι × Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) := ⟨staged,current.ancestors⟩
  have middleAligned : SourceRecordPredicate.Holds (Predicate markerId) middle.tree :=
    SourceRecordPredicate.context (Predicate markerId) current.focus staged current.ancestors (fun _ => stagedAligned) aligned
  have middleErases : middle.mapRecords Prod.snd =
      ⟨Reached.stagedTree markerId blocks before,current.ancestors.map (Frame.mapRecords Prod.snd)⟩ := by
    simp only [middle,Cursor.mapRecords,stagedErases]
  have stagedView := HeadPacketLayout.before_realizes markerId (ObservedHeadBlueprint.bits old) direction old
    oldHeader incomingHeader rfl rfl before beforeFound blocks
  obtain ⟨target,backReads,backCost,backRun,repacked,backAncestors,backIds,targetAligned,backBound,positive⟩ :=
    HeadReassembleRepack.run markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader
      newValid dormantValid blocks ordinary after afterFound _ stagedView.symm _ middle middleErases middleAligned
  have actual := Sequential.run stageRun (by rfl) backRun positive (by rfl)
  have small := HeadPacketLayout.before_size markerId (ObservedHeadBlueprint.bits old) direction old
    oldHeader incomingHeader rfl rfl before beforeFound
  have budget := PhysicalPacketStaging.Context.budget_leaves before
  refine ⟨target,_,_,actual,repacked,backAncestors,?_,targetAligned,by omega⟩
  have localIds := congrArg (Source.inventory id) stagedIds
  simp only [mapRecords_inventory,Function.comp_def,id_eq] at localIds
  exact backIds.trans (plug_inventory_congr Prod.fst localIds current.ancestors)

theorem execute {F : Type*} [DecidableEq F] (finger : F)
    (markerId : ι) (direction : Bool) (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : Neutral markerId newHeader) (dormantValid : Neutral markerId dormantHeader)
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (ordinary : HeadPacketLayout.WingRoots markerId (ObservedHeadBlueprint.bits old) blocks)
    (before after : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (beforeFound : HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader = some before)
    (afterFound : HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader = some after)
    (current : Cursor β (ι × Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (input : Reached.Stored blocks before current.focus)
    (config : MultiSourceProgram.Configuration F β (ι × Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (represented : MultiSourceSingleCursor.Represents finger current config)
    (valid : MultiSourceProgram.WellFormed config)
    (aligned : SourceRecordPredicate.Holds (Predicate markerId) config.tree) :
    ∃ target cursor reads cost,
      MultiSourceProgram.Run
        (MultiSourceSingleCursor.program
          (program markerId (actions markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader)
            (PacketLayers.Context.commands (after.mapRecords blueprint))) finger)
        (some (.inl (.running (PacketLayers.Context.commands (before.mapRecords blueprint))))) config
        (some (.inr (.inr (.running [])))) target reads cost ∧
      MultiSourceSingleCursor.Represents finger cursor target ∧ Reached.Repacked blocks after cursor.focus ∧
      target.tree.inventory Prod.fst = config.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (Predicate markerId) target.tree ∧ MultiSourceProgram.WellFormed target ∧ cost ≤ 692 := by
  have initialAligned : SourceRecordPredicate.Holds (Predicate markerId) current.tree := represented.1 ▸ aligned
  obtain ⟨cursor,reads,cost,actual,repacked,_,ids,preserved,bound⟩ := run markerId direction old fresh oldHeader incomingHeader
    newHeader dormantHeader newValid dormantValid blocks ordinary before after beforeFound afterFound current input initialAligned
  obtain ⟨target,compiled,positioned⟩ := MultiSourceSingleCursor.compile_run _ finger actual config represented
  refine ⟨target,cursor,_,cost,compiled,positioned,repacked,?_,?_,compiled.wellFormed valid,bound⟩
  · rw [positioned.1,ids,← represented.1]
  · rw [positioned.1]
    exact preserved

end TangoSquared.Paper20261030.MixedHeadExchange
