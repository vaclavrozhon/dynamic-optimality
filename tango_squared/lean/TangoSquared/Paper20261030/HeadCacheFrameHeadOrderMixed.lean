import TangoSquared.Paper20261030.HeadCacheFrameHeadOrder
import TangoSquared.Paper20261030.LocalRepairedHeadExchange

set_option autoImplicit false

/-! Inorder preservation for the actual mixed and repaired head programs.
The constructed component runs are identified with any supplied completed
run by determinism. No identifier-order invariant is assumed of a run.
-/

namespace TangoSquared.Paper20261030.MixedHeadExchange

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalPacketStaging PacketLayers
open PacketAlignment HeadBoundary HeadCacheFrameHeadOrder

variable {α β ρ ι η : Type*}

theorem order_of_run (markerId : ι) (direction : Bool) (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : Neutral markerId newHeader) (dormantValid : Neutral markerId dormantHeader)
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (ordinary : HeadPacketLayout.WingRoots markerId (ObservedHeadBlueprint.bits old) blocks)
    (before after : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (beforeFound : HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader = some before)
    (afterFound : HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader = some after)
    (current : Cursor β (ι × Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (represented : Reached.Stored blocks before current.focus)
    (aligned : SourceRecordPredicate.Holds (Predicate markerId) current.tree)
    {target : Cursor β (ι × Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)} {reads cost}
    (actual : Run (program markerId (actions markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader)
      (PacketLayers.Context.commands (after.mapRecords blueprint)))
      (.inl (.running (PacketLayers.Context.commands (before.mapRecords blueprint)))) current
      (.inr (.inr (.running []))) target reads cost) :
    target.tree.inorderLabels Prod.fst = current.tree.inorderLabels Prod.fst := by
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
  obtain ⟨checked,backReads,backCost,backRun,_,_,_,_,_,positive⟩ :=
    HeadReassembleRepack.run markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader
      newValid dormantValid blocks ordinary after afterFound _ stagedView.symm _ middle middleErases middleAligned
  have backOrder := HeadReassembleRepack.order_of_run markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader
    newValid dormantValid blocks ordinary after afterFound _ stagedView.symm _ middle middleErases middleAligned backRun
  have completed := Sequential.run stageRun (by rfl) backRun positive (by rfl)
  have same := source_run_deterministic completed actual
  rw [← same.2.1]
  exact backOrder.trans (plug_inorderLabels_congr Prod.fst
    (order_of_identifier_tree Prod.fst Prod.fst current.focus staged stagedIds) current.ancestors)

end TangoSquared.Paper20261030.MixedHeadExchange

namespace TangoSquared.Paper20261030.RepairedHeadExchange

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalPacketStaging PacketLayers HeadBoundary
open HeadCacheFrameHeadOrder

variable {α β ρ ι η : Type*}

theorem order_of_run (markerId : ι) (direction : Bool) (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : PacketAlignment.Neutral markerId newHeader) (dormantValid : PacketAlignment.Neutral markerId dormantHeader)
    (current : Cursor β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (before after : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (repairPlan : Source (Fin 8) MixedPacketRepair.Layers)
    (beforeFound : HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader = some before)
    (afterFound : HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader = some after)
    (planFound : HeadPacketRepair.after (ObservedHeadBlueprint.bits old) direction newHeader.length dormantHeader.length = some repairPlan)
    (stored : Reached.Stored blocks before current.focus)
    (ready : PacketConditions.wings (fun base => Ready base (.prefix [])) (ObservedHeadBlueprint.bits old) blocks)
    (clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) current.focus)
    (aligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) current.tree)
    {target : Cursor β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι)} {reads cost}
    (actual : Run (program markerId (MixedHeadExchange.actions markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader)
      (Context.commands (after.mapRecords blueprint)) repairPlan)
      (.inl (.inl (.running (Context.commands (before.mapRecords blueprint))))) current
      (.inr (.ready [])) target reads cost) :
    target.tree.inorderLabels Prod.fst = current.tree.inorderLabels Prod.fst := by
  have ordinary := MarkerFreePackets.wing_roots markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader
    blocks before beforeFound current.focus stored ready clear
  obtain ⟨middle,firstReads,firstCost,first,repacked,_,_,_,_⟩ :=
    MixedHeadExchange.run markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader newValid dormantValid
      blocks ordinary before after beforeFound afterFound current stored aligned
  have firstOrder := MixedHeadExchange.order_of_run markerId direction old fresh oldHeader incomingHeader newHeader dormantHeader
    newValid dormantValid blocks ordinary before after beforeFound afterFound current stored aligned first
  obtain ⟨checkedPlan,computed,_,fits,_⟩ := HeadPacketRepair.output_fits markerId direction old fresh newHeader dormantHeader
    after afterFound blocks middle.focus repacked
  have samePlan := Option.some.inj (computed.symm.trans planFound)
  subst checkedPlan
  obtain ⟨lastReads,last⟩ := MixedPacketRepair.run repairPlan none middle.focus fits middle.ancestors
  have positive : 0 < PhysicalContextRepair.cost repairPlan := by
    cases repairPlan <;> simp only [PhysicalContextRepair.cost] <;> omega
  have checked := Sequential.run first (by rfl) last positive (by rfl)
  have same := source_run_deterministic checked actual
  rw [← same.2.1]
  exact (plug_inorderLabels_congr Prod.fst
    (order_of_identifier_tree Prod.fst Prod.fst middle.focus (MixedPacketRepair.output repairPlan none middle.focus)
      (MixedPacketRepair.identifiers repairPlan none middle.focus)) middle.ancestors).trans firstOrder

end TangoSquared.Paper20261030.RepairedHeadExchange
