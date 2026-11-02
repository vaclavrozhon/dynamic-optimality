import ChaCha.Paper20261030.HeadPacketRepairPlan
import ChaCha.Paper20261030.MixedPacketRepairCorrectness
import ChaCha.Paper20261030.LocalReadyMixedHeadExchange

set_option autoImplicit false

/-!
# Staging, head exchange, repacking, and physical-field repair in one program

The fourth phase uses the scalar head repair blueprint computed from the
same presence bits, direction, and bounded header lengths. Its actual
child reads require no guessed connector ids or component-root oracle.
All four phases together cost at most 792 source-pointer operations.

The endpoint is the exact `MixedPacketRepair.output` of the checked
repacked view. The remaining semantic bridge identifies that endpoint
with the canonical forests for the repaired logical sources, including
the metadata of retained opaque blocks and enclosing attachments.
-/

namespace ChaCha.Paper20261030.RepairedHeadExchange

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalPacketStaging PacketLayers HeadBoundary

variable {α β ρ ι η : Type*}

abbrev State (α ρ ι : Type*) := Sum (MixedHeadExchange.State α ρ ι) (MixedPacketRepair.State (Fin 8) α ρ ι)

def program (markerId : ι) (actions : List (LocalRecordActions.Action (Option (Datum α ρ ι))))
    (repackCommands : List (RecordEditScript.Command Blueprint)) (repairPlan : Source (Fin 8) MixedPacketRepair.Layers) :
    Program (State α ρ ι) (Context.Cell α ρ ι) :=
  Sequential.program (MixedHeadExchange.program markerId actions repackCommands) MixedPacketRepair.program
    (.ready [.visit repairPlan none])

theorem run_for (markerId : ι) (direction : Bool) (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : PacketAlignment.Neutral markerId newHeader) (dormantValid : PacketAlignment.Neutral markerId dormantHeader)
    (current : Cursor β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (before : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (beforeFound : HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader = some before)
    (stored : Reached.Stored blocks before current.focus)
    (ready : PacketConditions.wings (fun base => Ready base (.prefix [])) (ObservedHeadBlueprint.bits old) blocks)
    (clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) current.focus)
    (aligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) current.tree) :
    ∃ after repairPlan,
      ∃ (middle target : Cursor β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι)), ∃ reads cost,
      HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader = some after ∧
      HeadPacketRepair.after (ObservedHeadBlueprint.bits old) direction newHeader.length dormantHeader.length = some repairPlan ∧
      Run (program markerId (MixedHeadExchange.actions markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader)
        (Context.commands (after.mapRecords blueprint)) repairPlan)
        (.inl (.inl (.running (Context.commands (before.mapRecords blueprint)))) ) current
        (.inr (.ready [])) target reads cost ∧
      Reached.Repacked blocks after middle.focus ∧
      SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) middle.tree ∧
      middle.tree.inventory Prod.fst = current.tree.inventory Prod.fst ∧
      target = ⟨MixedPacketRepair.output repairPlan none middle.focus,middle.ancestors⟩ ∧
      MixedPacketRepair.TreeCorrect repairPlan none target.focus ∧
      target.ancestors.map (Frame.mapRecords Prod.snd) = current.ancestors.map (Frame.mapRecords Prod.snd) ∧
      target.tree.inventory Prod.fst = current.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) target.tree ∧ cost ≤ 792 := by
  have ordinary := MarkerFreePackets.wing_roots markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader
    blocks before beforeFound current.focus stored ready clear
  obtain ⟨after,afterFound⟩ := HeadPacketLayout.after_exists markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader
  obtain ⟨middle,firstReads,firstCost,first,repacked,ancestors,ids,alignment,firstBound⟩ :=
    MixedHeadExchange.run markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader newValid dormantValid
      blocks ordinary before after beforeFound afterFound current stored aligned
  obtain ⟨repairPlan,planFound,same,fits,small⟩ := HeadPacketRepair.output_fits markerId direction old fresh newHeader dormantHeader
    after afterFound blocks middle.focus repacked
  obtain ⟨lastReads,last⟩ := MixedPacketRepair.run repairPlan none middle.focus fits middle.ancestors
  have positive : 0 < PhysicalContextRepair.cost repairPlan := by
    cases repairPlan <;> simp only [PhysicalContextRepair.cost] <;> omega
  have actual := Sequential.run first (by rfl) last positive (by rfl)
  have correct := MixedPacketRepair.output_correct repairPlan none middle.focus
    (MixedPacketRepair.repacked_recognized markerId blocks same middle.focus repacked
      (HeadPacketLayout.after_good markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader blocks ordinary after afterFound))
  have localIds := congrArg (Source.inventory id) (MixedPacketRepair.identifiers repairPlan none middle.focus)
  simp only [mapRecords_inventory,Function.comp_def,id_eq] at localIds
  have globalIds := plug_inventory_congr Prod.fst localIds middle.ancestors
  have finalAligned := SourceRecordPredicate.context (PacketAlignment.Predicate markerId) middle.focus
    (MixedPacketRepair.output repairPlan none middle.focus) middle.ancestors
    (MixedPacketRepair.alignment markerId repairPlan none middle.focus) alignment
  refine ⟨after,repairPlan,middle,_,_,_,afterFound,planFound,actual,repacked,alignment,ids,rfl,correct,ancestors,
    globalIds.trans ids,finalAligned,?_⟩
  have lastBound := MixedPacketRepair.eight_bound repairPlan small
  omega

/-- The convenient existential input interface is discharged by either
canonical input theorem. `run_for` additionally retains the caller's
particular block witnesses for subsequent semantic reconstruction. -/
theorem run (markerId : ι) (direction : Bool) (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : PacketAlignment.Neutral markerId newHeader) (dormantValid : PacketAlignment.Neutral markerId dormantHeader)
    (current : Cursor β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (input : ReadyMixedHeadExchange.Input markerId direction old oldHeader incomingHeader current.focus)
    (clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) current.focus)
    (aligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) current.tree) :
    ∃ blocks before after repairPlan,
      ∃ (middle target : Cursor β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι)), ∃ reads cost,
      HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader = some before ∧
      HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader = some after ∧
      HeadPacketRepair.after (ObservedHeadBlueprint.bits old) direction newHeader.length dormantHeader.length = some repairPlan ∧
      Run (program markerId (MixedHeadExchange.actions markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader)
        (Context.commands (after.mapRecords blueprint)) repairPlan)
        (.inl (.inl (.running (Context.commands (before.mapRecords blueprint))))) current
        (.inr (.ready [])) target reads cost ∧
      Reached.Repacked blocks after middle.focus ∧
      target = ⟨MixedPacketRepair.output repairPlan none middle.focus,middle.ancestors⟩ ∧
      MixedPacketRepair.TreeCorrect repairPlan none target.focus ∧
      target.tree.inventory Prod.fst = current.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) target.tree ∧ cost ≤ 792 := by
  obtain ⟨blocks,before,beforeFound,stored,ready⟩ := input
  obtain ⟨after,repairPlan,middle,target,reads,cost,afterFound,planFound,actual,repacked,_,_,output,correct,_,ids,alignment,bound⟩ :=
    run_for markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader newValid dormantValid
      current blocks before beforeFound stored ready clear aligned
  exact ⟨blocks,before,after,repairPlan,middle,target,reads,cost,beforeFound,afterFound,planFound,
    actual,repacked,output,correct,ids,alignment,bound⟩

/-- The four phases execute in the shared physical tree, with the same
operation count and valid positions for all retained fingers. -/
theorem execute {F : Type*} [DecidableEq F] (finger : F)
    (markerId : ι) (direction : Bool) (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : PacketAlignment.Neutral markerId newHeader) (dormantValid : PacketAlignment.Neutral markerId dormantHeader)
    (current : Cursor β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (input : ReadyMixedHeadExchange.Input markerId direction old oldHeader incomingHeader current.focus)
    (clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) current.focus)
    (aligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) current.tree)
    (config : MultiSourceProgram.Configuration F β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (located : MultiSourceSingleCursor.Represents finger current config) (valid : MultiSourceProgram.WellFormed config) :
    ∃ blocks before after repairPlan,
      ∃ (middle target : Cursor β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι)), ∃ finalConfig reads cost,
      HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader = some before ∧
      HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader = some after ∧
      HeadPacketRepair.after (ObservedHeadBlueprint.bits old) direction newHeader.length dormantHeader.length = some repairPlan ∧
      MultiSourceProgram.Run (MultiSourceSingleCursor.program
        (program markerId (MixedHeadExchange.actions markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader)
          (Context.commands (after.mapRecords blueprint)) repairPlan) finger)
        (some (.inl (.inl (.running (Context.commands (before.mapRecords blueprint)))))) config
        (some (.inr (.ready []))) finalConfig reads cost ∧
      MultiSourceSingleCursor.Represents finger target finalConfig ∧
      Reached.Repacked blocks after middle.focus ∧
      target = ⟨MixedPacketRepair.output repairPlan none middle.focus,middle.ancestors⟩ ∧
      MixedPacketRepair.TreeCorrect repairPlan none target.focus ∧
      finalConfig.tree.inventory Prod.fst = config.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) finalConfig.tree ∧
      MultiSourceProgram.WellFormed finalConfig ∧ cost ≤ 792 := by
  obtain ⟨blocks,before,after,repairPlan,middle,target,reads,cost,beforeFound,afterFound,planFound,
    actual,repacked,output,correct,ids,alignment,bound⟩ :=
    run markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader newValid dormantValid
      current input clear aligned
  obtain ⟨finalConfig,compiled,positioned⟩ := MultiSourceSingleCursor.compile_run _ finger actual config located
  refine ⟨blocks,before,after,repairPlan,middle,target,finalConfig,_,cost,beforeFound,afterFound,planFound,
    compiled,positioned,repacked,output,correct,?_,?_,compiled.wellFormed valid,bound⟩
  · rw [positioned.1,ids,← located.1]
  · rw [positioned.1]
    exact alignment

end ChaCha.Paper20261030.RepairedHeadExchange
