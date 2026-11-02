import ChaCha.Paper20261030.LocalEnclosedHeadExchange
import ChaCha.Paper20261030.CanonicalHeadSuccessor

set_option autoImplicit false

/-!
# Executing the canonical head successor from retained input witnesses

This endpoint supplies the semantic after-layout proof to the actual
803-operation enclosed program. All semantic data come from the same
canonical input blocks. The new boundary payload is the reconstructed
dormant component, and every other payload is retained from the input.
Acquiring the observations and scheduling preparation/restoration remain
obligations of the complete primary controller.
-/

namespace ChaCha.Paper20261030.CanonicalHeadExecution

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers HeadBoundary
open RepairedPayloadLayouts

variable {α β ρ ι η F : Type*} [DecidableEq ι] [DecidableEq F]

theorem execute (finger : F) (markerId : ι) (direction : Bool) (depth : α)
    (old fresh : Records ρ η (Option Bool))
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
    (activePayload incomingPayload : Option Bool → α → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (headerKey : α)
    (head oldTail incomingTail : Bool → ProjectionLocal.Projected α (HeadBoundary.Record ρ η (Option Bool)))
    (witnesses : CanonicalRetainedBlocks.HeadWitnesses (ObservedHeadBlueprint.bits old) blocks
      activePayload incomingPayload headerKey head oldTail incomingTail)
    (separate : ∀ side, Separate (head side) (incomingTail side))
    (headAbsent : ∀ side, depth ∉ ports (head side)) (incomingAbsent : ∀ side, depth ∉ ports (incomingTail side))
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
      CanonicalHeadSuccessor.Result activePayload incomingPayload head oldTail incomingTail direction depth fresh
        newHeader dormantHeader (activePayload none headerKey) (incomingPayload none headerKey) (some (bare.focus.mapRecords Prod.snd)) ∧
      finalConfig.tree.inventory Prod.fst = config.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId finalConfig.tree ∧
      markerId ∉ finalConfig.tree.inventory Prod.fst ∧
      MultiSourceProgram.WellFormed finalConfig ∧ cost ≤ 803 ∧ bare.ancestors.isEmpty = current.ancestors.isEmpty := by
  have focusClear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) current.focus := by
    intro record member
    exact clear record (Multiset.mem_of_le (inventory_le_plug id current.focus current.ancestors) member)
  have semantic := CanonicalHeadSuccessor.represents markerId direction depth old fresh oldHeader incomingHeader newHeader dormantHeader
    activePayload incomingPayload headerKey head oldTail incomingTail blocks before beforeFound current.focus stored ready focusClear
    witnesses separate headAbsent incomingAbsent
  exact EnclosedHeadExchange.execute finger markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader
    newValid dormantValid newClear dormantClear enclosing current blocks before beforeFound stored ready clear reserved unique aligned
    _ semantic config located wellFormed

end ChaCha.Paper20261030.CanonicalHeadExecution
