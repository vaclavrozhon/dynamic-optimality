import TangoSquared.Paper20261030.ObservedHeadExchangeExecution
import TangoSquared.Paper20261030.CanonicalMixedRootInput
import TangoSquared.Paper20261030.ObservedRootHeadParameters
import TangoSquared.Paper20261030.CanonicalRetainedPortFacts
import TangoSquared.Paper20261030.PacketPrefixErasure

set_option autoImplicit false

/-! Executing the computed minimum-depth exchange from two canonical
component representations. The absent prefix has no allocated vertex.
The program transfers the actual enclosing packet and preserves every
physical identifier, including the retained component attachments. -/

namespace TangoSquared.Paper20261030.ObservedCanonicalRootHeadExecution

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalForestMetadata PhysicalPacketStaging
open PacketLayers LocalComponentCompiler RepairedPayloadLayouts

variable {β ρ η F : Type*} [DecidableEq F]

local instance observedCanonicalRootHeadExecutionColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

abbrev projected (identifier : ρ → η) (color : Nat → Option Bool) (parent : η) (source : Source Nat ρ) :=
  fun side => packed color (some side) (annotate identifier color (some parent) source)

set_option backward.isDefEq.respectTransparency false in
theorem execute (finger : F) (markerId depth : Nat) (identifier : ρ → η)
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
    (reserved : markerId ∉ global.tree.inventory Prod.fst) :
    ∃ selected bare finalConfig reads cost,
      ObservedHeadExchangeExecution.plan markerId data = some selected ∧
      MultiSourceProgram.Run
        (ObservedHeadExchangeExecution.program finger markerId saved.length (!current.ancestors.isEmpty) data)
        (some (.transferring .start)) global (some (.done (.inr (.ready [])))) finalConfig reads cost ∧
      MultiSourceSingleCursor.Represents finger
        (EnclosingPacketOperation.output saved current.focus.rootRecord.1 bare) finalConfig ∧
      CanonicalHeadSuccessor.Result activePayload incomingPayload
        (fun _ => none)
        (projected identifier activeColor (identifier oldHigh) oldTail)
        (projected identifier incomingColor (identifier incomingHigh) incomingTail)
        data.direction depth data.fresh (ObservedHeadParameters.packet data.newHeader) (ObservedHeadParameters.packet data.dormantHeader)
        (activePayload none headerKey) (incomingPayload none headerKey) (some (bare.focus.mapRecords Prod.snd)) ∧
      finalConfig.tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId finalConfig.tree ∧ markerId ∉ finalConfig.tree.inventory Prod.fst ∧
      MultiSourceProgram.WellFormed finalConfig ∧ cost ≤ 803 ∧ bare.ancestors.isEmpty = current.ancestors.isEmpty := by
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
  have separate : ∀ side, Separate (none : ProjectionLocal.Projected Nat (HeadBoundary.Record ρ η (Option Bool)))
      (projected identifier incomingColor (identifier incomingHigh) incomingTail side) := by
    intro side key member
    exact False.elim (List.not_mem_nil member)
  have headAbsent : ∀ side : Bool, depth ∉ ports (none : ProjectionLocal.Projected Nat (HeadBoundary.Record ρ η (Option Bool))) := by
    intro side
    exact List.not_mem_nil
  have incomingAbsent : ∀ side, depth ∉ ports (projected identifier incomingColor (identifier incomingHigh) incomingTail side) := by
    intro side
    exact CanonicalRetainedPortFacts.absent identifier incomingColor _ _ incomingTail depth
      (fun member => (Nat.lt_irrefl depth) (incomingDepths depth member))
  have atInput : MultiSourceSingleCursor.Represents finger
      ⟨PacketPrefixTransfer.attach saved normalized.focus,normalized.ancestors⟩ global := by
    rw [show normalized.ancestors = current.ancestors from rfl,
      PacketPrefixErasure.reattach_cursor current saved activeConfig.tree.rootRecord split]
    exact located
  obtain ⟨selected,bare,finalConfig,reads,cost,planned,actual,returned,result,ids,valid,finalReserved,finalValid,bound,sameEmpty⟩ :=
    ObservedHeadExchangeExecution.execute finger markerId depth data saved normalized blocks before beforeFound stored ready
      rawPhysical.2.1 rawReserved rawPhysical.2.2 rawPhysical.1 activePayload incomingPayload headerKey _ _ _ witnesses
      separate headAbsent incomingAbsent global atInput wellFormed
  rw [PacketPrefixErasure.root_id] at returned
  exact ⟨selected,bare,finalConfig,reads,cost,planned,actual,returned,result,ids,valid,finalReserved,finalValid,bound,sameEmpty⟩

end TangoSquared.Paper20261030.ObservedCanonicalRootHeadExecution
