import TangoSquared.Paper20261030.MultiSourcePacketPrefix
import TangoSquared.Paper20261030.EnclosingPacketInvariants
import TangoSquared.Paper20261030.MultiSourceFinish

set_option autoImplicit false

/-! A multifinger component operation with actual enclosing-prefix
transfer and parent-reference repair. Both physical root identifiers
used by the repair come from the prefix controller's reads. The known
connector depth costs one operation per upward edge; all remaining
wrapper work costs at most eleven operations. -/

namespace TangoSquared.Paper20261030.MultiSourceEnclosingOperation

open ColoredStorage SourcePointer MultiSourceProgram PhysicalPacketStaging PacketLayers

variable {α β ρ ι F σ : Type*} [DecidableEq F] [DecidableEq ι]

structure Result (σ ι : Type*) where
  oldId : ι
  newId : ι
  last : σ

def select : MultiSourcePacketPrefix.State σ α ρ ι → Option (Result σ ι)
  | .returning _ oldId last (some (.done newId)) => some ⟨oldId,newId,last⟩
  | _ => none

def repairInitial (hasParent : Bool) (_ : Option (Result σ ι)) : Option (PacketParentRepair.State α ρ ι) :=
  some (if hasParent then .start else .done)

def repair (exit : σ → F) (hasParent : Bool) (result : Option (Result σ ι)) :
    Program (Option (PacketParentRepair.State α ρ ι)) F (Context.Cell α ρ ι) :=
  match result with
  | none => fun _ => .halt
  | some result => if hasParent then
      MultiSourceSingleCursor.program (PacketParentRepair.program result.oldId result.newId) (exit result.last)
    else fun _ => .halt

def program (entry : F) (exit : σ → F) (count levels : Nat) (hasParent : Bool)
    (kernel : Program σ F (Context.Cell α ρ ι)) (initial : σ) :=
  MultiSourceFinish.program (MultiSourcePacketPrefix.program entry exit count levels kernel initial)
    select (repairInitial hasParent) (repair exit hasParent)

theorem repair_run (exit : σ → F) (oldId : ι) (last : σ)
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
          | first::rest => PacketParentRepair.frame oldId root.rootRecord.1 first::rest⟩ target ∧ cost ≤ 7 := by
  cases outside with
  | nil => exact ⟨config,[],0,.halt rfl,positioned,by omega⟩
  | cons first rest =>
    obtain ⟨reads,cost,body,bound⟩ := PacketParentRepair.run oldId root first rest unique
    obtain ⟨target,actual,targetRep⟩ := MultiSourceSingleCursor.compile_run _ (exit last) body config positioned
    exact ⟨target,_,cost,actual,targetRep,bound⟩

theorem execute (entry : F) (exit : σ → F) (saved : Packet α ρ ι)
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
      WellFormed target ∧ total ≤ cost+inside.length+11 := by
  obtain ⟨middle,frontReads,front,middleRep,_⟩ :=
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
  obtain ⟨target,backReads,backCost,back,targetRep,bound⟩ :=
    repair_run exit focus.rootRecord.1 last (PacketPrefixTransfer.output saved root) finalOutside middle middleRep
      (restoredIds ▸ unique)
  simp only [PacketPrefixTransfer.output_root_id] at back targetRep
  have actual := MultiSourceFinish.finish (select (α := α) (ρ := ρ))
    (repairInitial (!finalOutside.isEmpty)) (repair exit (!finalOutside.isEmpty)) front back
  have finalRep : MultiSourceSingleCursor.Represents (exit last)
      (EnclosingPacketOperation.output saved focus.rootRecord.1 ⟨root,finalOutside⟩) target := by
    cases finalOutside <;> exact targetRep
  refine ⟨target,_,_,actual,finalRep,?_,actual.wellFormed valid,by omega⟩
  rw [finalRep.1]
  exact (EnclosingPacketOperation.inventory saved focus.rootRecord.1 ⟨root,finalOutside⟩).trans
    (congrArg (fun tree => tree.inventory Prod.fst) afterTree.symm)

end TangoSquared.Paper20261030.MultiSourceEnclosingOperation
