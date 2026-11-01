import TangoSquared.Paper20261030.LocalSemanticHeadExchange
import TangoSquared.Paper20261030.HeadPacketMarkerFree

set_option autoImplicit false

/-!
# Reusable marker-free endpoints of the actual head exchange

The proof keeps the exact block witnesses, the semantic after-layout,
alignment, and exclusion of the reserved marker from immutable ids.
The external cursor context has unchanged erased packets, so the final
marker-free invariant holds on the whole tree, not just the repaired
component. This does not account for a prefix stored at the focus itself;
that enclosing attachment still needs its separate local lift.
-/

namespace TangoSquared.Paper20261030.MaintainedHeadExchange

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalPacketStaging PacketLayers HeadBoundary

variable {α β ρ ι η : Type*}

theorem clear_context (markerId : ι) (before after : Cursor β (Context.Cell α ρ ι))
    (clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) before.tree)
    (focusClear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) after.focus)
    (outside : after.ancestors.map (Frame.mapRecords Prod.snd) = before.ancestors.map (Frame.mapRecords Prod.snd)) :
    SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) after.tree := by
  have old := (MarkerFreePackets.map_predicate (MarkerFreePackets.Packet markerId) Prod.snd before.tree).mpr clear
  have focused := (MarkerFreePackets.map_predicate (MarkerFreePackets.Packet markerId) Prod.snd after.focus).mpr focusClear
  apply (MarkerFreePackets.map_predicate (MarkerFreePackets.Packet markerId) Prod.snd after.tree).mp
  change SourceRecordPredicate.Holds (MarkerFreePackets.Packet markerId) ((plug after.focus after.ancestors).mapRecords Prod.snd)
  rw [← plug_mapRecords,outside]
  apply SourceRecordPredicate.context (MarkerFreePackets.Packet markerId) (before.focus.mapRecords Prod.snd)
    (after.focus.mapRecords Prod.snd) (before.ancestors.map (Frame.mapRecords Prod.snd)) (fun _ => focused)
  rw [plug_mapRecords]
  exact old

theorem run (markerId : ι) (direction : Bool) (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : PacketAlignment.Neutral markerId newHeader) (dormantValid : PacketAlignment.Neutral markerId dormantHeader)
    (newClear : MarkerFreePackets.Packet markerId newHeader) (dormantClear : MarkerFreePackets.Packet markerId dormantHeader)
    (current : Cursor β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (before : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (beforeFound : HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader = some before)
    (stored : Reached.Stored blocks before current.focus)
    (ready : PacketConditions.wings (fun base => Ready base (.prefix [])) (ObservedHeadBlueprint.bits old) blocks)
    (clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) current.tree)
    (reserved : markerId ∉ current.tree.inventory Prod.fst)
    (aligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) current.tree)
    (predicate : RepairedComponentLayout.View β α (HeadBoundary.Record ρ η (Option Bool)) ι → Prop)
    (semantic : RepairedComponentLayout.Represents markerId blocks
      (HeadPacketRepair.after (ObservedHeadBlueprint.bits old) direction newHeader.length dormantHeader.length)
      (HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader) predicate) :
    ∃ after repairPlan,
      ∃ (target : Cursor β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι)), ∃ reads cost,
      HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader = some after ∧
      HeadPacketRepair.after (ObservedHeadBlueprint.bits old) direction newHeader.length dormantHeader.length = some repairPlan ∧
      Run (RepairedHeadExchange.program markerId
        (MixedHeadExchange.actions markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader)
        (Context.commands (after.mapRecords blueprint)) repairPlan)
        (.inl (.inl (.running (Context.commands (before.mapRecords blueprint))))) current
        (.inr (.ready [])) target reads cost ∧
      target.ancestors.map (Frame.mapRecords Prod.snd) = current.ancestors.map (Frame.mapRecords Prod.snd) ∧
      predicate (some (target.focus.mapRecords Prod.snd)) ∧
      SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) target.tree ∧
      markerId ∉ target.tree.inventory Prod.fst ∧
      target.tree.inventory Prod.fst = current.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) target.tree ∧ cost ≤ 792 := by
  have initialClear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) current.focus := by
    intro record member
    exact clear record (Multiset.mem_of_le (Structural.inventory_le_plug id current.focus current.ancestors) member)
  obtain ⟨after,repairPlan,middle,target,reads,cost,afterFound,planFound,actual,repacked,middleAligned,middleIds,output,correct,outside,ids,alignment,bound⟩ :=
    RepairedHeadExchange.run_for markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader newValid dormantValid
      current blocks before beforeFound stored ready initialClear aligned
  have focusAligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) middle.focus := by
    intro record member
    exact middleAligned record (Multiset.mem_of_le (Structural.inventory_le_plug id middle.focus middle.ancestors) member)
  have middleReserved : markerId ∉ middle.focus.inventory Prod.fst := by
    intro member
    apply reserved
    rw [← middleIds]
    exact Multiset.mem_of_le (Structural.inventory_le_plug Prod.fst middle.focus middle.ancestors) member
  have finalClear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) target.focus := by
    rw [output]
    exact MarkerFreePackets.repaired_endpoint markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader
      newClear dormantClear blocks before after beforeFound afterFound current.focus middle.focus stored initialClear repacked middleReserved repairPlan
  rw [planFound,afterFound] at semantic
  refine ⟨after,repairPlan,target,reads,cost,afterFound,planFound,actual,outside,?_,clear_context markerId current target clear finalClear outside,
    ?_,ids,alignment,bound⟩
  · rw [output]
    exact semantic.2 middle.focus repacked focusAligned
  · rw [ids]
    exact reserved

theorem execute {F : Type*} [DecidableEq F] (finger : F)
    (markerId : ι) (direction : Bool) (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : PacketAlignment.Neutral markerId newHeader) (dormantValid : PacketAlignment.Neutral markerId dormantHeader)
    (newClear : MarkerFreePackets.Packet markerId newHeader) (dormantClear : MarkerFreePackets.Packet markerId dormantHeader)
    (current : Cursor β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (before : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (beforeFound : HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader = some before)
    (stored : Reached.Stored blocks before current.focus)
    (ready : PacketConditions.wings (fun base => Ready base (.prefix [])) (ObservedHeadBlueprint.bits old) blocks)
    (clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) current.tree)
    (reserved : markerId ∉ current.tree.inventory Prod.fst)
    (aligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) current.tree)
    (predicate : RepairedComponentLayout.View β α (HeadBoundary.Record ρ η (Option Bool)) ι → Prop)
    (semantic : RepairedComponentLayout.Represents markerId blocks
      (HeadPacketRepair.after (ObservedHeadBlueprint.bits old) direction newHeader.length dormantHeader.length)
      (HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader) predicate)
    (config : MultiSourceProgram.Configuration F β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (located : MultiSourceSingleCursor.Represents finger current config) (valid : MultiSourceProgram.WellFormed config) :
    ∃ after repairPlan,
      ∃ (target : Cursor β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι)), ∃ finalConfig reads cost,
      HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader = some after ∧
      HeadPacketRepair.after (ObservedHeadBlueprint.bits old) direction newHeader.length dormantHeader.length = some repairPlan ∧
      MultiSourceProgram.Run (MultiSourceSingleCursor.program
        (RepairedHeadExchange.program markerId
          (MixedHeadExchange.actions markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader)
          (Context.commands (after.mapRecords blueprint)) repairPlan) finger)
        (some (.inl (.inl (.running (Context.commands (before.mapRecords blueprint)))))) config
        (some (.inr (.ready []))) finalConfig reads cost ∧
      MultiSourceSingleCursor.Represents finger target finalConfig ∧ predicate (some (target.focus.mapRecords Prod.snd)) ∧
      SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) finalConfig.tree ∧
      markerId ∉ finalConfig.tree.inventory Prod.fst ∧
      finalConfig.tree.inventory Prod.fst = config.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) finalConfig.tree ∧
      MultiSourceProgram.WellFormed finalConfig ∧ cost ≤ 792 := by
  obtain ⟨after,repairPlan,target,reads,cost,afterFound,planFound,actual,_,final,finalClear,finalReserved,ids,alignment,bound⟩ :=
    run markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader newValid dormantValid newClear dormantClear
      current blocks before beforeFound stored ready clear reserved aligned predicate semantic
  obtain ⟨finalConfig,compiled,positioned⟩ := MultiSourceSingleCursor.compile_run _ finger actual config located
  refine ⟨after,repairPlan,target,finalConfig,_,cost,afterFound,planFound,compiled,positioned,final,?_,?_,?_,?_,
    compiled.wellFormed valid,bound⟩
  · rw [positioned.1]
    exact finalClear
  · rw [positioned.1]
    exact finalReserved
  · rw [positioned.1,ids,← located.1]
  · rw [positioned.1]
    exact alignment

end TangoSquared.Paper20261030.MaintainedHeadExchange
