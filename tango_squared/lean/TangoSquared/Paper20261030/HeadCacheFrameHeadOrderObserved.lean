import TangoSquared.Paper20261030.HeadCacheFrameHeadOrderMixed
import TangoSquared.Paper20261030.ObservedHeadExchangeExecution
import TangoSquared.Paper20261030.EnclosingPacketAnchors
import TangoSquared.Paper20261030.MultiSourceRunDeterminism

set_option autoImplicit false

/-! The observed head controller preserves physical inorder identifiers.
Its staging, immutable reassembly, repacking, field repair, enclosing
packet transfer, and parent repair are all accounted for in this theorem.
-/

namespace TangoSquared.Paper20261030.ObservedHeadExchangeExecution

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers HeadBoundary
open ObservedHeadParameters (Data packet)
open HeadCacheFrameHeadOrder

variable {α β ρ η F : Type*} [DecidableEq F]

theorem inorder_of_run (finger : F) (markerId : Nat) (data : Data α ρ η)
    (enclosing : Packet α (Logical ρ η) Nat) (current : Cursor β (Context.Cell α (Logical ρ η) Nat))
    (blocks : Fin 8 → Source β (Packet α (Logical ρ η) Nat))
    (before : Source (Fin 8) (Expression α (Logical ρ η) Nat))
    (beforeFound : HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits data.old) data.direction data.old
      (packet data.activeHeader) (packet data.incomingHeader) = some before)
    (stored : Reached.Stored blocks before current.focus)
    (ready : PacketConditions.wings (fun base => Ready base (.prefix [])) (ObservedHeadBlueprint.bits data.old) blocks)
    (clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) current.focus)
    (unique : (current.tree.inventory Prod.fst).Nodup)
    (aligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) current.tree)
    (config : MultiSourceProgram.Configuration F β (Context.Cell α (Logical ρ η) Nat))
    (located : MultiSourceSingleCursor.Represents finger
      ⟨PacketPrefixTransfer.attach enclosing current.focus,current.ancestors⟩ config)
    {final : MultiSourceProgram.Configuration F β (Context.Cell α (Logical ρ η) Nat)} {reads cost}
    (actual : MultiSourceProgram.Run (program finger markerId enclosing.length (!current.ancestors.isEmpty) data)
      (some (.transferring .start)) config (some (.done (.inr (.ready [])))) final reads cost) :
    final.tree.inorderLabels Prod.fst = config.tree.inorderLabels Prod.fst := by
  obtain ⟨after,repairPlan,middle,bare,bodyReads,bodyCost,afterFound,planFound,body,_,_,_,_,_,outside,ids,_,_⟩ :=
    RepairedHeadExchange.run_for markerId data.direction data.old data.fresh
      (packet data.activeHeader) (packet data.incomingHeader) (packet data.newHeader) (packet data.dormantHeader)
      (PacketAlignment.header markerId data.newHeader) (PacketAlignment.header markerId data.dormantHeader)
      current blocks before beforeFound stored ready clear aligned
  have bodyOrder := RepairedHeadExchange.order_of_run markerId data.direction data.old data.fresh
    (packet data.activeHeader) (packet data.incomingHeader) (packet data.newHeader) (packet data.dormantHeader)
    (PacketAlignment.header markerId data.newHeader) (PacketAlignment.header markerId data.dormantHeader)
    current blocks before after repairPlan beforeFound afterFound planFound stored ready clear aligned body
  have sameEmpty : bare.ancestors.isEmpty = current.ancestors.isEmpty := by
    simpa only [List.isEmpty_map] using congrArg List.isEmpty outside
  have bareUnique : (bare.tree.inventory Prod.fst).Nodup := by
    rw [ids]
    exact unique
  obtain ⟨observed,total,enclosed,_⟩ := EnclosingPacketOperation.run enclosing _ _ _ current bare
    body rfl sameEmpty bareUnique
  obtain ⟨checked,compiled,returned⟩ := MultiSourceSingleCursor.compile_run _ finger enclosed config located
  have selected : plan markerId data = some ⟨before,after,repairPlan⟩ := by
    simp only [plan,beforeFound,afterFound,planFound]
  have checkedRun : MultiSourceProgram.Run (program finger markerId enclosing.length (!current.ancestors.isEmpty) data)
      (some (.transferring .start)) config (some (.done (.inr (.ready [])))) checked
      (observed.map (fun record => (finger,record))) total := by
    rw [program,selected]
    exact compiled
  have same := checkedRun.deterministic actual
  have inputOrder : config.tree.inorderLabels Prod.fst = current.tree.inorderLabels Prod.fst := by
    rw [located.1]
    exact plug_inorderLabels_congr Prod.fst
      (Source.inorderLabels_setRoot Prod.fst current.focus
        (current.focus.rootRecord.1,enclosing ++ current.focus.rootRecord.2) rfl) current.ancestors
  rw [← same.2.1,returned.1]
  exact (order_of_identifier_tree Prod.fst Prod.fst bare.tree
    (EnclosingPacketOperation.output enclosing current.focus.rootRecord.1 bare).tree
    (EnclosingPacketOperation.identifier_tree enclosing current.focus.rootRecord.1 bare)).trans
    (bodyOrder.trans inputOrder.symm)

end TangoSquared.Paper20261030.ObservedHeadExchangeExecution
