import TangoSquared.Paper20261030.HeadCacheFrameHeadOrderObserved
import TangoSquared.Paper20261030.ObservedCanonicalHeadExecution
import TangoSquared.Paper20261030.ObservedCanonicalRootHeadExecution

set_option autoImplicit false

/-! Canonical input descriptors discharge all layout premises of the
physical inorder theorem for both forms of the observed head exchange. -/

namespace TangoSquared.Paper20261030.ObservedCanonicalHeadExecution

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalForestMetadata PhysicalPacketStaging
open PacketLayers LocalComponentCompiler RepairedPayloadLayouts

variable {β ρ η F : Type*} [DecidableEq F]

local instance headCacheFrameOrderColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem inorder_of_run (finger : F) (markerId depth : Nat) (identifier : ρ → η)
    (activeColor incomingColor : Nat → Option Bool)
    (low oldHigh incomingHigh oldTerminal incomingTerminal : ρ)
    (headPart oldTail incomingTail : Source Nat ρ)
    (headDepths : ∀ key ∈ headPart.shape.leaves, key < depth)
    (incomingDepths : ∀ key ∈ incomingTail.shape.leaves, depth < key)
    (data : ObservedHeadParameters.Data Nat ρ η)
    (boundary : activeColor depth = some data.direction) (sentinel : incomingColor depth = none)
    (observed : data.old = HeadBoundary.observed identifier activeColor incomingColor
      low oldHigh incomingHigh oldTerminal incomingTerminal depth headPart oldTail incomingTail)
    (activeForest incomingForest : TaggedForest (Option Bool) Nat (HeadBoundary.Record ρ η (Option Bool)) Nat)
    (activeRep : ProjectionForest.Represents activeColor
      ⟨annotate identifier activeColor none (.fork low headPart (.fork oldHigh (.leaf depth oldTerminal) oldTail)),[]⟩ (erase activeForest))
    (incomingRep : ProjectionForest.Represents incomingColor
      ⟨annotate identifier incomingColor none (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail),[]⟩ (erase incomingForest))
    (activeHeader : data.activeHeader = ForestMirrorController.transform wingOrientation (encode activeForest) none)
    (incomingHeader : data.incomingHeader = ForestMirrorController.transform wingOrientation (encode incomingForest) none)
    (headerKey : Nat) (activePayload incomingPayload : Option Bool → Nat → Source β (Packet Nat (HeadBoundary.Record ρ η (Option Bool)) Nat))
    (activeConfig incomingConfig : MultiSourceProgram.Configuration (Option Bool) β (Packet Nat (HeadBoundary.Record ρ η (Option Bool)) Nat))
    (activeAssembled : ForestConnector.assemble
      (ComponentPhysicalRepair.view none wingOrientation headerKey activePayload (encode activeForest))
      (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey activePayload (encode activeForest))) = some activeConfig)
    (incomingAssembled : ForestConnector.assemble
      (ComponentPhysicalRepair.view none wingOrientation headerKey incomingPayload (encode incomingForest))
      (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey incomingPayload (encode incomingForest))) = some incomingConfig)
    (attached : activePayload (some data.direction) depth = incomingConfig.tree)
    (current : Cursor β (Context.Cell Nat (HeadBoundary.Record ρ η (Option Bool)) Nat))
    (saved : Packet Nat (HeadBoundary.Record ρ η (Option Bool)) Nat)
    (view : current.focus.mapRecords Prod.snd = activeConfig.tree.setRoot (saved++activeConfig.tree.rootRecord))
    (global : MultiSourceProgram.Configuration F β (Context.Cell Nat (HeadBoundary.Record ρ η (Option Bool)) Nat))
    (located : MultiSourceSingleCursor.Represents finger current global)
    (wellFormed : MultiSourceProgram.WellFormed global)
    (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    {finalConfig : MultiSourceProgram.Configuration F β (Context.Cell Nat (HeadBoundary.Record ρ η (Option Bool)) Nat)}
    {reads cost}
    (actual : MultiSourceProgram.Run
      (ObservedHeadExchangeExecution.program finger markerId saved.length (!current.ancestors.isEmpty) data)
      (some (.transferring .start)) global (some (.done (.inr (.ready [])))) finalConfig reads cost) :
    finalConfig.tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst := by
  let normalized := SubtreeMetadata.replacePayload current activeConfig.tree.rootRecord
  have split := PacketPrefixErasure.root_packet current saved activeConfig.tree view
  have rawErases := PacketPrefixErasure.payload current saved activeConfig.tree view
  have rawPhysical := PacketPrefixErasure.physical markerId current saved activeConfig.tree.rootRecord global located.1 split physical
  have rawIds := PacketPrefixErasure.inventory current activeConfig.tree.rootRecord global located.1
  have rawReserved : markerId ∉ normalized.tree.inventory Prod.fst := by
    change markerId ∉ (PacketPrefixErasure.stripped current activeConfig.tree.rootRecord global).tree.inventory Prod.fst
    rw [rawIds]
    exact reserved
  obtain ⟨blocks,before,beforeFound,stored,ready,witnesses⟩ :=
    CanonicalMixedHeadInput.input markerId identifier activeColor incomingColor low oldHigh incomingHigh oldTerminal incomingTerminal
      depth headPart oldTail incomingTail data.direction boundary sentinel activeForest incomingForest activeRep incomingRep
      headerKey activePayload incomingPayload activeConfig incomingConfig activeAssembled incomingAssembled attached normalized.focus rawErases
  rw [← observed] at beforeFound ready witnesses
  change HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits data.old) data.direction data.old
    (ObservedHeadParameters.packet (ForestMirrorController.transform wingOrientation (encode activeForest) none))
    (ObservedHeadParameters.packet (ForestMirrorController.transform wingOrientation (encode incomingForest) none)) = some before at beforeFound
  rw [← activeHeader,← incomingHeader] at beforeFound
  have atInput : MultiSourceSingleCursor.Represents finger
      ⟨PacketPrefixTransfer.attach saved normalized.focus,normalized.ancestors⟩ global := by
    rw [show normalized.ancestors = current.ancestors from rfl,
      PacketPrefixErasure.reattach_cursor current saved activeConfig.tree.rootRecord split]
    exact located
  have clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) normalized.focus := by
    intro record member
    exact rawPhysical.2.1 record (Multiset.mem_of_le (inventory_le_plug id normalized.focus normalized.ancestors) member)
  exact ObservedHeadExchangeExecution.inorder_of_run finger markerId data saved normalized blocks before beforeFound
    stored ready clear rawPhysical.2.2 rawPhysical.1 global atInput actual

end TangoSquared.Paper20261030.ObservedCanonicalHeadExecution

namespace TangoSquared.Paper20261030.ObservedCanonicalRootHeadExecution

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalForestMetadata PhysicalPacketStaging
open PacketLayers LocalComponentCompiler RepairedPayloadLayouts

variable {β ρ η F : Type*} [DecidableEq F]

local instance headCacheFrameOrderColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem inorder_of_run (finger : F) (markerId depth : Nat) (identifier : ρ → η)
    (activeColor incomingColor : Nat → Option Bool)
    (oldHigh incomingHigh oldTerminal incomingTerminal : ρ)
    (oldTail incomingTail : Source Nat ρ)
    (incomingDepths : ∀ key ∈ incomingTail.shape.leaves, depth < key)
    (data : ObservedHeadParameters.Data Nat ρ η)
    (boundary : activeColor depth = some data.direction) (sentinel : incomingColor depth = none)
    (observed : data.old = RootMixedHeadExchange.lift (ObservedRootHeadParameters.observed identifier activeColor incomingColor
      oldHigh incomingHigh oldTerminal incomingTerminal depth oldTail incomingTail))
    (activeForest incomingForest : TaggedForest (Option Bool) Nat (HeadBoundary.Record ρ η (Option Bool)) Nat)
    (activeRep : ProjectionForest.Represents activeColor
      ⟨annotate identifier activeColor none (.fork oldHigh (.leaf depth oldTerminal) oldTail),[]⟩ (erase activeForest))
    (incomingRep : ProjectionForest.Represents incomingColor
      ⟨annotate identifier incomingColor none (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail),[]⟩ (erase incomingForest))
    (activeHeader : data.activeHeader = ForestMirrorController.transform wingOrientation (encode activeForest) none)
    (incomingHeader : data.incomingHeader = ForestMirrorController.transform wingOrientation (encode incomingForest) none)
    (headerKey : Nat) (activePayload incomingPayload : Option Bool → Nat → Source β (Packet Nat (HeadBoundary.Record ρ η (Option Bool)) Nat))
    (activeConfig incomingConfig : MultiSourceProgram.Configuration (Option Bool) β (Packet Nat (HeadBoundary.Record ρ η (Option Bool)) Nat))
    (activeAssembled : ForestConnector.assemble
      (ComponentPhysicalRepair.view none wingOrientation headerKey activePayload (encode activeForest))
      (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey activePayload (encode activeForest))) = some activeConfig)
    (incomingAssembled : ForestConnector.assemble
      (ComponentPhysicalRepair.view none wingOrientation headerKey incomingPayload (encode incomingForest))
      (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey incomingPayload (encode incomingForest))) = some incomingConfig)
    (attached : activePayload (some data.direction) depth = incomingConfig.tree)
    (current : Cursor β (Context.Cell Nat (HeadBoundary.Record ρ η (Option Bool)) Nat))
    (saved : Packet Nat (HeadBoundary.Record ρ η (Option Bool)) Nat)
    (view : current.focus.mapRecords Prod.snd = activeConfig.tree.setRoot (saved++activeConfig.tree.rootRecord))
    (global : MultiSourceProgram.Configuration F β (Context.Cell Nat (HeadBoundary.Record ρ η (Option Bool)) Nat))
    (located : MultiSourceSingleCursor.Represents finger current global)
    (wellFormed : MultiSourceProgram.WellFormed global)
    (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    {finalConfig : MultiSourceProgram.Configuration F β (Context.Cell Nat (HeadBoundary.Record ρ η (Option Bool)) Nat)}
    {reads cost}
    (actual : MultiSourceProgram.Run
      (ObservedHeadExchangeExecution.program finger markerId saved.length (!current.ancestors.isEmpty) data)
      (some (.transferring .start)) global (some (.done (.inr (.ready [])))) finalConfig reads cost) :
    finalConfig.tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst := by
  let normalized := SubtreeMetadata.replacePayload current activeConfig.tree.rootRecord
  have split := PacketPrefixErasure.root_packet current saved activeConfig.tree view
  have rawErases := PacketPrefixErasure.payload current saved activeConfig.tree view
  have rawPhysical := PacketPrefixErasure.physical markerId current saved activeConfig.tree.rootRecord global located.1 split physical
  have rawIds := PacketPrefixErasure.inventory current activeConfig.tree.rootRecord global located.1
  have rawReserved : markerId ∉ normalized.tree.inventory Prod.fst := by
    change markerId ∉ (PacketPrefixErasure.stripped current activeConfig.tree.rootRecord global).tree.inventory Prod.fst
    rw [rawIds]
    exact reserved
  obtain ⟨blocks,before,beforeFound,stored,ready,witnesses⟩ :=
    CanonicalMixedRootInput.input markerId identifier activeColor incomingColor oldHigh incomingHigh oldTerminal incomingTerminal
      depth oldTail incomingTail data.direction boundary sentinel activeForest incomingForest activeRep incomingRep
      headerKey activePayload incomingPayload activeConfig incomingConfig activeAssembled incomingAssembled attached normalized.focus rawErases
  change data.old = RootMixedHeadExchange.lift (CanonicalRootComponentView.observed identifier activeColor incomingColor
    oldHigh incomingHigh oldTerminal incomingTerminal depth oldTail incomingTail) at observed
  rw [← observed] at beforeFound ready witnesses
  change HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits data.old) data.direction data.old
    (ObservedHeadParameters.packet (ForestMirrorController.transform wingOrientation (encode activeForest) none))
    (ObservedHeadParameters.packet (ForestMirrorController.transform wingOrientation (encode incomingForest) none)) = some before at beforeFound
  rw [← activeHeader,← incomingHeader] at beforeFound
  have atInput : MultiSourceSingleCursor.Represents finger
      ⟨PacketPrefixTransfer.attach saved normalized.focus,normalized.ancestors⟩ global := by
    rw [show normalized.ancestors = current.ancestors from rfl,
      PacketPrefixErasure.reattach_cursor current saved activeConfig.tree.rootRecord split]
    exact located
  have clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) normalized.focus := by
    intro record member
    exact rawPhysical.2.1 record (Multiset.mem_of_le (inventory_le_plug id normalized.focus normalized.ancestors) member)
  exact ObservedHeadExchangeExecution.inorder_of_run finger markerId data saved normalized blocks before beforeFound
    stored ready clear rawPhysical.2.2 rawPhysical.1 global atInput actual

end TangoSquared.Paper20261030.ObservedCanonicalRootHeadExecution
