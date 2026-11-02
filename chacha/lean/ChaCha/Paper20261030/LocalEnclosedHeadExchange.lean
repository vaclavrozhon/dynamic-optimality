import ChaCha.Paper20261030.LocalMaintainedHeadExchange
import ChaCha.Paper20261030.CanonicalEnclosingPackets

set_option autoImplicit false

/-!
# The actual head exchange with enclosing packets and parent repair

The shared-tree run removes the caller's enclosing prefix, executes the
four-phase head exchange, transfers every outer layer to the new root,
and repairs its immediate physical parent. Its total cost is at most 803.
The same canonical semantic predicate describes the bare new component;
`CanonicalEnclosingPackets.moved` identifies its restored outer layers.

The caller must still obtain the prefix length and the prepared input
from the maintained primary layout. This local endpoint does not yet
implement the complete observation, preparation, and restoration loop.
-/

namespace ChaCha.Paper20261030.EnclosedHeadExchange

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalPacketStaging PacketLayers HeadBoundary

variable {α β ρ ι η F : Type*} [DecidableEq ι] [DecidableEq F]

theorem execute (finger : F) (markerId : ι) (direction : Bool) (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : PacketAlignment.Neutral markerId newHeader) (dormantValid : PacketAlignment.Neutral markerId dormantHeader)
    (newClear : MarkerFreePackets.Packet markerId newHeader) (dormantClear : MarkerFreePackets.Packet markerId dormantHeader)
    (enclosing : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (current : Cursor β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (before : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (beforeFound : HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader = some before)
    (stored : Reached.Stored blocks before current.focus)
    (ready : PacketConditions.wings (fun base => Ready base (.prefix [])) (ObservedHeadBlueprint.bits old) blocks)
    (clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) current.tree)
    (reserved : markerId ∉ current.tree.inventory Prod.fst)
    (unique : (current.tree.inventory Prod.fst).Nodup)
    (aligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) current.tree)
    (predicate : RepairedComponentLayout.View β α (HeadBoundary.Record ρ η (Option Bool)) ι → Prop)
    (semantic : RepairedComponentLayout.Represents markerId blocks
      (HeadPacketRepair.after (ObservedHeadBlueprint.bits old) direction newHeader.length dormantHeader.length)
      (HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader) predicate)
    (config : MultiSourceProgram.Configuration F β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (located : MultiSourceSingleCursor.Represents finger
      ⟨PacketPrefixTransfer.attach enclosing current.focus,current.ancestors⟩ config)
    (wellFormed : MultiSourceProgram.WellFormed config) :
    ∃ after repairPlan,
      ∃ (bare : Cursor β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι)), ∃ finalConfig reads cost,
      HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader = some after ∧
      HeadPacketRepair.after (ObservedHeadBlueprint.bits old) direction newHeader.length dormantHeader.length = some repairPlan ∧
      MultiSourceProgram.Run (MultiSourceSingleCursor.program
        (EnclosingPacketOperation.program enclosing.length (!current.ancestors.isEmpty)
          (RepairedHeadExchange.program markerId
            (MixedHeadExchange.actions markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader)
            (Context.commands (after.mapRecords blueprint)) repairPlan)
          (.inl (.inl (.running (Context.commands (before.mapRecords blueprint)))))) finger)
        (some (.transferring .start)) config (some (.done (.inr (.ready [])))) finalConfig reads cost ∧
      MultiSourceSingleCursor.Represents finger (EnclosingPacketOperation.output enclosing current.focus.rootRecord.1 bare) finalConfig ∧
      predicate (some (bare.focus.mapRecords Prod.snd)) ∧
      finalConfig.tree.inventory Prod.fst = config.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId finalConfig.tree ∧
      markerId ∉ finalConfig.tree.inventory Prod.fst ∧
      MultiSourceProgram.WellFormed finalConfig ∧ cost ≤ 803 ∧ bare.ancestors.isEmpty = current.ancestors.isEmpty := by
  obtain ⟨after,repairPlan,bare,bodyReads,bodyCost,afterFound,planFound,body,outside,meaning,bareClear,bareReserved,ids,bareAligned,bound⟩ :=
    MaintainedHeadExchange.run markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader newValid dormantValid newClear dormantClear
      current blocks before beforeFound stored ready clear reserved aligned predicate semantic
  have bareUnique : (bare.tree.inventory Prod.fst).Nodup := by rw [ids]; exact unique
  have sameEmpty : bare.ancestors.isEmpty = current.ancestors.isEmpty := by
    simpa only [List.isEmpty_map] using congrArg List.isEmpty outside
  obtain ⟨finalConfig,reads,cost,actual,positioned,finalIds,physical,finalReserved,valid,costBound⟩ :=
    EnclosingPacketOperation.execute finger markerId enclosing _ _ _ current bare body rfl sameEmpty bareReserved
      ⟨bareAligned,bareClear,bareUnique⟩ config located wellFormed
  refine ⟨after,repairPlan,bare,finalConfig,reads,cost,afterFound,planFound,actual,positioned,meaning,?_,physical,
    finalReserved,valid,by omega,sameEmpty⟩
  rw [finalIds,ids,located.1]
  exact (plug_inventory_congr Prod.fst
    (Source.inventory_setRoot Prod.fst current.focus
      (current.focus.rootRecord.1,enclosing++current.focus.rootRecord.2) rfl) current.ancestors).symm

end ChaCha.Paper20261030.EnclosedHeadExchange
