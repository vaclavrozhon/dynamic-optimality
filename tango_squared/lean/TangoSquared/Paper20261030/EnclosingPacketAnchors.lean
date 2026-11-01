import TangoSquared.Paper20261030.MultiSourceEnclosingOperation
import TangoSquared.Paper20261030.MultiSourceFingerLabels

set_option autoImplicit false

/-! Enclosing packet transfer and parent repair preserve the complete
physical-id labelled tree and the positions of all other fingers. -/

namespace TangoSquared.Paper20261030.EnclosingPacketOperation

open ColoredStorage SourcePointer PhysicalPacketStaging PacketLayers

variable {α β ρ ι : Type*} [DecidableEq ι]

theorem identifier_tree (packet : Packet α ρ ι) (oldId : ι) (current : Cursor β (Context.Cell α ρ ι)) :
    (output packet oldId current).tree.mapRecords Prod.fst = current.tree.mapRecords Prod.fst := by
  obtain ⟨focus,outside⟩ := current
  have rootSame : (PacketPrefixTransfer.output packet focus).mapRecords Prod.fst = focus.mapRecords Prod.fst := by
    cases focus <;> rfl
  cases outside with
  | nil => exact rootSame
  | cons first rest =>
    have frameSame : (PacketParentRepair.frame oldId focus.rootRecord.1 first).mapRecords Prod.fst =
        first.mapRecords Prod.fst := by cases first <;> rfl
    simp only [output,Cursor.tree,← plug_mapRecords,List.map_cons]
    rw [rootSame,frameSame]

end TangoSquared.Paper20261030.EnclosingPacketOperation

namespace TangoSquared.Paper20261030.PacketParentRepair

open SourceLocalProgram

variable {α ρ ι : Type*} [DecidableEq ι]

theorem edgeOnly (old fresh : ι) : MultiSourceSingleCursor.EdgeOnly (program (α := α) (ρ := ρ) old fresh) := by
  intro state move next code
  cases state with
  | start | toLeft | fromLeft | toRight =>
    simp only [program,Instruction.nav.injEq] at code
    cases code.1
    trivial
  | readParent | writeParent | inspectLeft | done => simp only [program,reduceCtorEq] at code

end TangoSquared.Paper20261030.PacketParentRepair

namespace TangoSquared.Paper20261030.MultiSourceEnclosingOperation

open ColoredStorage SourcePointer MultiSourceProgram PhysicalPacketStaging PacketLayers

variable {α β ρ ι F σ : Type*} [DecidableEq F] [DecidableEq ι]

theorem repair_run_others (exit : σ → F) (oldId : ι) (last : σ)
    (root : Source β (Context.Cell α ρ ι)) (outside : List (Frame β (Context.Cell α ρ ι)))
    (config : Configuration F β (Context.Cell α ρ ι))
    (positioned : MultiSourceSingleCursor.Represents (exit last) ⟨root,outside⟩ config)
    (unique : ((plug root outside).inventory Prod.fst).Nodup) :
    ∃ target reads cost,
      Run (repair exit (!outside.isEmpty) (some ⟨oldId,root.rootRecord.1,last⟩))
        (repairInitial (!outside.isEmpty) (some ⟨oldId,root.rootRecord.1,last⟩)) config (some .done) target reads cost ∧
      MultiSourceSingleCursor.Represents (exit last)
        ⟨root,match outside with
          | [] => []
          | first::rest => PacketParentRepair.frame oldId root.rootRecord.1 first::rest⟩ target ∧ (∀ other, other ≠ exit last → target.fingers other = config.fingers other) ∧ cost ≤ 7 := by
  cases outside with
  | nil => exact ⟨config,[],0,.halt rfl,positioned,(fun _ _ => rfl),by omega⟩
  | cons first rest =>
    obtain ⟨reads,cost,body,bound⟩ := PacketParentRepair.run oldId root first rest unique
    obtain ⟨target,actual,targetRep,others⟩ := MultiSourceSingleCursor.compile_edge_run _
      (PacketParentRepair.edgeOnly oldId root.rootRecord.1) (exit last) body config positioned
    exact ⟨target,_,cost,actual,targetRep,others,bound⟩

theorem execute_others (entry : F) (exit : σ → F) (saved : Packet α ρ ι)
    (kernel : Program σ F (Context.Cell α ρ ι)) (initial last : σ)
    (before after : Configuration F β (Context.Cell α ρ ι)) {reads cost}
    (body : Run kernel initial before last after reads cost)
    (focus finalFocus : Source β (Context.Cell α ρ ι))
    (outside inside finalOutside : List (Frame β (Context.Cell α ρ ι)))
    (entryRep : MultiSourceSingleCursor.Represents entry ⟨focus,outside⟩ before)
    (exitRep : MultiSourceSingleCursor.Represents (exit last) ⟨finalFocus,inside++finalOutside⟩ after)
    (unique : (after.tree.inventory Prod.fst).Nodup)
    (valid : WellFormed (MultiSourcePacketPrefix.attached saved focus outside before)) :
    ∃ target observed total,
      Run (program entry exit saved.length inside.length (!finalOutside.isEmpty) kernel initial)
        (.first .start) (MultiSourcePacketPrefix.attached saved focus outside before)
        (.second (some ⟨focus.rootRecord.1,(plug finalFocus inside).rootRecord.1,last⟩) (some .done))
        target observed total ∧
      MultiSourceSingleCursor.Represents (exit last)
        (EnclosingPacketOperation.output saved focus.rootRecord.1 ⟨plug finalFocus inside,finalOutside⟩) target ∧
      target.tree.inventory Prod.fst = after.tree.inventory Prod.fst ∧
      (∀ other, other ≠ exit last → target.fingers other = after.fingers other) ∧
      WellFormed target ∧ total ≤ cost+inside.length+11 := by
  obtain ⟨middle,frontReads,front,middleRep,frontOthers⟩ :=
    MultiSourcePacketPrefix.execute entry exit saved kernel initial last before after body
      focus finalFocus outside inside finalOutside entryRep exitRep
  let root := plug finalFocus inside
  have afterTree : after.tree = plug root finalOutside := by
    rw [exitRep.1]
    exact plug_append finalFocus inside finalOutside
  have restoredIds : (plug (PacketPrefixTransfer.output saved root) finalOutside).inventory Prod.fst =
      after.tree.inventory Prod.fst := by
    rw [afterTree]
    exact plug_inventory_congr Prod.fst (PacketPrefixTransfer.identifiers saved root) finalOutside
  obtain ⟨target,backReads,backCost,back,targetRep,backOthers,bound⟩ :=
    repair_run_others exit focus.rootRecord.1 last (PacketPrefixTransfer.output saved root) finalOutside middle middleRep
      (restoredIds ▸ unique)
  simp only [PacketPrefixTransfer.output_root_id] at back targetRep
  have actual := MultiSourceFinish.finish (select (α := α) (ρ := ρ))
    (repairInitial (!finalOutside.isEmpty)) (repair exit (!finalOutside.isEmpty)) front back
  have finalRep : MultiSourceSingleCursor.Represents (exit last)
      (EnclosingPacketOperation.output saved focus.rootRecord.1 ⟨root,finalOutside⟩) target := by
    cases finalOutside <;> exact targetRep
  refine ⟨target,_,_,actual,finalRep,?_,(fun other different => (backOthers other different).trans (frontOthers other different)),actual.wellFormed valid,by omega⟩
  rw [finalRep.1]
  exact (EnclosingPacketOperation.inventory saved focus.rootRecord.1 ⟨root,finalOutside⟩).trans
    (congrArg (fun tree => tree.inventory Prod.fst) afterTree.symm)

end TangoSquared.Paper20261030.MultiSourceEnclosingOperation
