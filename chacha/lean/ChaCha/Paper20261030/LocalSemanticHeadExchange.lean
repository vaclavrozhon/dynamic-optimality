import ChaCha.Paper20261030.CanonicalHeadOutput
import ChaCha.Paper20261030.LocalRepairedHeadExchange

set_option autoImplicit false

/-!
# Carrying a canonical after-layout invariant through the actual exchange

The block witnesses are fixed by the caller and retained throughout the
four-phase execution. `CanonicalHeadOutput.represents` supplies the
after-layout predicate from canonical blocks and disjoint ports. The
endpoint therefore has that semantic invariant, in addition to correct
individual pointer fields, with the same 792-operation bound.

The enclosing attachment prefix and the primary observation/prepare/
restore schedule are outside this local theorem.
-/

namespace ChaCha.Paper20261030.SemanticHeadExchange

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalPacketStaging PacketLayers HeadBoundary

variable {α β ρ ι η : Type*}

theorem run (markerId : ι) (direction : Bool) (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : PacketAlignment.Neutral markerId newHeader) (dormantValid : PacketAlignment.Neutral markerId dormantHeader)
    (current : Cursor β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (before : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (beforeFound : HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader = some before)
    (stored : Reached.Stored blocks before current.focus)
    (ready : PacketConditions.wings (fun base => Ready base (.prefix [])) (ObservedHeadBlueprint.bits old) blocks)
    (clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) current.focus)
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
      predicate (some (target.focus.mapRecords Prod.snd)) ∧
      target.tree.inventory Prod.fst = current.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) target.tree ∧ cost ≤ 792 := by
  obtain ⟨after,repairPlan,middle,target,reads,cost,afterFound,planFound,actual,repacked,middleAligned,_,output,correct,_,ids,alignment,bound⟩ :=
    RepairedHeadExchange.run_for markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader newValid dormantValid
      current blocks before beforeFound stored ready clear aligned
  have focusAligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) middle.focus := by
    intro record member
    exact middleAligned record (Multiset.mem_of_le (Structural.inventory_le_plug id middle.focus middle.ancestors) member)
  rw [planFound,afterFound] at semantic
  have final := semantic.2 middle.focus repacked focusAligned
  refine ⟨after,repairPlan,target,reads,cost,afterFound,planFound,actual,?_,ids,alignment,bound⟩
  rw [output]
  exact final

theorem execute {F : Type*} [DecidableEq F] (finger : F)
    (markerId : ι) (direction : Bool) (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : PacketAlignment.Neutral markerId newHeader) (dormantValid : PacketAlignment.Neutral markerId dormantHeader)
    (current : Cursor β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (before : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (beforeFound : HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader = some before)
    (stored : Reached.Stored blocks before current.focus)
    (ready : PacketConditions.wings (fun base => Ready base (.prefix [])) (ObservedHeadBlueprint.bits old) blocks)
    (clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) current.focus)
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
      finalConfig.tree.inventory Prod.fst = config.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) finalConfig.tree ∧
      MultiSourceProgram.WellFormed finalConfig ∧ cost ≤ 792 := by
  obtain ⟨after,repairPlan,target,reads,cost,afterFound,planFound,actual,final,ids,alignment,bound⟩ :=
    run markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader newValid dormantValid
      current blocks before beforeFound stored ready clear aligned predicate semantic
  obtain ⟨finalConfig,compiled,positioned⟩ := MultiSourceSingleCursor.compile_run _ finger actual config located
  refine ⟨after,repairPlan,target,finalConfig,_,cost,afterFound,planFound,compiled,positioned,final,?_,?_,compiled.wellFormed valid,bound⟩
  · rw [positioned.1,ids,← located.1]
  · rw [positioned.1]
    exact alignment

end ChaCha.Paper20261030.SemanticHeadExchange
