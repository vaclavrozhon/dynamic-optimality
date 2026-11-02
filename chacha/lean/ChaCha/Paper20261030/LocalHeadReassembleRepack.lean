import ChaCha.Paper20261030.HeadPacketRepacking
import ChaCha.Paper20261030.SourceSequential

/-!
# One controller for head reassembly followed by mixed-layer repacking

The initial tree is already staged. Its bounded boundary records and
headers determine the reassembly actions and the repacking blueprint.
The output is the actual repacked representation with ids read from the
reached vertices. Global identifier inventory and packet alignment are
preserved, including the untouched outer context. The total cost is at
most 634 operations, before repairing physical neighbor fields.

Staging the original representation, reading the boundary inputs, and
repairing neighbor fields are separate phases of the full head update.
-/

namespace ChaCha.Paper20261030.HeadReassembleRepack

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalPacketStaging PacketLayers
open PacketAlignment HeadBoundary

variable {α β ρ ι η : Type*}

abbrev State (α ρ ι : Type*) := Sum
  (ImmutableSource.State (LocalRecordActions.State (Option (Datum α ρ ι))) (Packet α ρ ι) ι)
  (RecordEditScript.State Blueprint (PacketLayers.Context.Cell α ρ ι))

def program (commands : List (RecordEditScript.Command Blueprint)) :
    Program (State α ρ ι) (PacketLayers.Context.Cell α ρ ι) :=
  Sequential.program (ImmutableSource.program LocalRecordActions.program)
    (RecordEditScript.program PacketLayers.Context.repacking) (.running commands)

private theorem budget_positive {κ τ : Type*} (context : Source κ τ) :
    0 < PhysicalPacketStaging.Context.budget context := by
  cases context <;> simp only [PhysicalPacketStaging.Context.budget] <;> omega

private theorem focus_valid (markerId : ι) (cursor : Cursor β (ι × Packet α ρ ι))
    (valid : SourceRecordPredicate.Holds (Predicate markerId) cursor.tree) :
    SourceRecordPredicate.Holds (Predicate markerId) cursor.focus := by
  intro record member
  exact valid record (Multiset.mem_of_le (inventory_le_plug id cursor.focus cursor.ancestors) member)

private theorem ids_inventory (first last : Source β (ι × Packet α ρ ι))
    (equal : first.mapRecords Prod.fst = last.mapRecords Prod.fst) : first.inventory Prod.fst = last.inventory Prod.fst := by
  have actual := congrArg (Source.inventory id) equal
  simpa only [mapRecords_inventory,Function.comp_def,id_eq] using actual

theorem run (markerId : ι) (direction : Bool) (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : Neutral markerId newHeader) (dormantValid : Neutral markerId dormantHeader)
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (ordinary : HeadPacketLayout.WingRoots markerId (ObservedHeadBlueprint.bits old) blocks)
    (layout : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (found : HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader = some layout)
    (initial : Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (initialView : OrderedContext.decorated
      (fun key => if ObservedHeadBlueprint.bits old key then some (blocks key) else none)
      (ObservedHeadBlueprint.beforeContext (markerValue markerId) direction old oldHeader incomingHeader) = some initial)
    (outside) (current : Cursor β (ι × Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (erases : current.mapRecords Prod.snd = ⟨initial,outside⟩)
    (aligned : SourceRecordPredicate.Holds (Predicate markerId) current.tree) :
    ∃ target reads cost,
      Run (program (PacketLayers.Context.commands (layout.mapRecords blueprint)))
        (.inl (.ready (.ready (OrderedContext.Local.decoratedActions (ObservedHeadBlueprint.bits old)
          (ObservedHeadBlueprint.beforeContext (markerValue markerId) direction old oldHeader incomingHeader)
          (ObservedHeadBlueprint.afterContext (markerValue markerId) direction fresh newHeader dormantHeader))))) current
        (.inr (.running [])) target reads cost ∧
      Reached.Repacked blocks layout target.focus ∧
      target.ancestors.map (Frame.mapRecords Prod.snd) = current.ancestors.map (Frame.mapRecords Prod.snd) ∧
      target.tree.inventory Prod.fst = current.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (Predicate markerId) target.tree ∧ cost ≤ 634 ∧ 0 < cost := by
  have finalView := HeadPacketLayout.after_realizes markerId (ObservedHeadBlueprint.bits old) direction fresh
    newHeader dormantHeader rfl rfl layout found blocks
  let finalTree := Reached.stagedTree markerId blocks layout
  have finalEq : OrderedContext.decorated
      (fun key => if ObservedHeadBlueprint.bits old key then some (blocks key) else none)
      (ObservedHeadBlueprint.afterContext (markerValue markerId) direction fresh newHeader dormantHeader) = some finalTree :=
    finalView.symm
  have presence (key : Fin 8) :
      (if ObservedHeadBlueprint.bits old key then some (blocks key) else none).isSome = ObservedHeadBlueprint.bits old key := by
    cases ObservedHeadBlueprint.bits old key <;> rfl
  obtain ⟨middle,frontReads,frontCost,frontRun,middleErases,middleIds,middleAligned,frontBound⟩ :=
    PacketAlignment.reassemble markerId _ _ _
      (ObservedHeadBlueprint.block_order (markerValue markerId) direction old fresh oldHeader incomingHeader newHeader dormantHeader)
      (PacketAlignment.after_neutral markerId direction fresh newHeader dormantHeader newValid dormantValid)
      initial finalTree initialView finalEq outside current erases aligned
  simp only [presence,ObservedHeadBlueprint.block_count] at frontRun frontBound
  have focusedEq := congrArg Cursor.focus middleErases
  change middle.focus.mapRecords Prod.snd = finalTree at focusedEq
  obtain ⟨last,backRun,repacked,lastIds,lastAligned⟩ := Reached.repack markerId blocks layout
    (HeadPacketLayout.after_good markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader blocks ordinary layout found)
    middle.focus focusedEq (focus_valid markerId middle middleAligned)
  obtain ⟨backReads,backRun⟩ := backRun middle.ancestors
  have actual := Sequential.run frontRun (by rfl) backRun (budget_positive layout) (by rfl)
  have small := HeadPacketLayout.after_size markerId (ObservedHeadBlueprint.bits old) direction fresh
    newHeader dormantHeader rfl rfl layout found
  have budget := PhysicalPacketStaging.Context.budget_leaves layout
  have positive := budget_positive layout
  refine ⟨⟨last,middle.ancestors⟩,_,_,actual,repacked,?_,?_,?_,by omega,by omega⟩
  · exact (congrArg Cursor.ancestors middleErases).trans (congrArg Cursor.ancestors erases).symm
  · exact (plug_inventory_congr Prod.fst (ids_inventory last middle.focus lastIds) middle.ancestors).trans middleIds
  · exact SourceRecordPredicate.context (Predicate markerId) middle.focus last middle.ancestors
      (fun _ => lastAligned) middleAligned

theorem execute {F : Type*} [DecidableEq F] (finger : F)
    (markerId : ι) (direction : Bool) (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : Neutral markerId newHeader) (dormantValid : Neutral markerId dormantHeader)
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (ordinary : HeadPacketLayout.WingRoots markerId (ObservedHeadBlueprint.bits old) blocks)
    (layout : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (found : HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader = some layout)
    (initial : Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (initialView : OrderedContext.decorated
      (fun key => if ObservedHeadBlueprint.bits old key then some (blocks key) else none)
      (ObservedHeadBlueprint.beforeContext (markerValue markerId) direction old oldHeader incomingHeader) = some initial)
    (outside) (current : Cursor β (ι × Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (erases : current.mapRecords Prod.snd = ⟨initial,outside⟩)
    (config : MultiSourceProgram.Configuration F β (ι × Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (represented : MultiSourceSingleCursor.Represents finger current config)
    (valid : MultiSourceProgram.WellFormed config)
    (aligned : SourceRecordPredicate.Holds (Predicate markerId) config.tree) :
    ∃ target cursor reads cost,
      MultiSourceProgram.Run
        (MultiSourceSingleCursor.program (program (PacketLayers.Context.commands (layout.mapRecords blueprint))) finger)
        (some (.inl (.ready (.ready (OrderedContext.Local.decoratedActions (ObservedHeadBlueprint.bits old)
          (ObservedHeadBlueprint.beforeContext (markerValue markerId) direction old oldHeader incomingHeader)
          (ObservedHeadBlueprint.afterContext (markerValue markerId) direction fresh newHeader dormantHeader)))))) config
        (some (.inr (.running []))) target reads cost ∧
      MultiSourceSingleCursor.Represents finger cursor target ∧ Reached.Repacked blocks layout cursor.focus ∧
      target.tree.inventory Prod.fst = config.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (Predicate markerId) target.tree ∧ MultiSourceProgram.WellFormed target ∧ cost ≤ 634 := by
  have initialAligned : SourceRecordPredicate.Holds (Predicate markerId) current.tree := represented.1 ▸ aligned
  obtain ⟨cursor,reads,cost,actual,repacked,_,ids,preserved,bound,_⟩ := run markerId direction old fresh oldHeader incomingHeader
    newHeader dormantHeader newValid dormantValid blocks ordinary layout found initial initialView outside current erases initialAligned
  obtain ⟨target,compiled,positioned⟩ := MultiSourceSingleCursor.compile_run _ finger actual config represented
  refine ⟨target,cursor,_,cost,compiled,positioned,repacked,?_,?_,compiled.wellFormed valid,bound⟩
  · rw [positioned.1,ids,← represented.1]
  · rw [positioned.1]
    exact preserved

end ChaCha.Paper20261030.HeadReassembleRepack
