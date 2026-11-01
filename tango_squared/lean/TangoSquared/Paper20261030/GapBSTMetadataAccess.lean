import TangoSquared.Paper20261030.GapBSTMetadataTrace
import TangoSquared.Paper20261030.GapBSTAccess
import DynamicOptimality.MetadataExecution

/-! Complete original-key services in the appendix's decorated ordinary
BST. Every source read/write and each slot relocation is charged. The
requested original key is read at a real visited physical cursor. -/

namespace TangoSquared.Paper20261030.GapBST.Storage

open ColoredStorage DynamicOptimality
open Auxiliary.Metadata (Trace)

variable {α ρ : Type*}

theorem forget_frames (last : α) (slot : Option ρ) (rest : List (SourcePointer.Frame α ρ)) :
    (frames last slot rest).map Auxiliary.Metadata.forgetFrame = GapBST.frames last rest := by
  induction rest generalizing last slot with
  | nil => rfl
  | cons first rest ih =>
    cases first <;> simp [frames,GapBST.frames,Auxiliary.Metadata.forgetFrame,forget_gaps,record,ih]

theorem forget_park (tree : MTR.Tree (Auxiliary.NodeRecord α (fun _ => Slots ρ)))
    (rest : List (MTR.Pointer.Frame (Auxiliary.NodeRecord α (fun _ => Slots ρ)))) :
    Auxiliary.Metadata.forgetCursor (park tree rest) =
      park (Auxiliary.Metadata.forgetTree tree) (rest.map Auxiliary.Metadata.forgetFrame) := by
  cases tree with
  | empty => cases rest with
    | nil => rfl
    | cons first rest => cases first <;> rfl
  | node => rfl

theorem forget_cursor (logical : SourcePointer.Cursor α ρ) :
    Auxiliary.Metadata.forgetCursor (cursor logical) = GapBST.cursor logical := by
  simp only [cursor,GapBST.cursor,forget_park,forget_gaps,forget_frames]

theorem enter_root (tree : Source α ρ) :
    ∃ cost, Trace (.atRoot (encode tree)) [] (cursor ⟨tree,[]⟩) cost ∧ cost ≤ 1 := by
  cases tree with
  | leaf => exact ⟨0,.nil _,by decide⟩
  | fork => exact ⟨1,.step (.nav (.left _ _ _ _ _ _)) (.nil _),le_rfl⟩

theorem leave_root (tree : Source α ρ) :
    ∃ cost, Trace (cursor ⟨tree,[]⟩) [] (.atRoot (encode tree)) cost ∧ cost ≤ 1 := by
  cases tree with
  | leaf => exact ⟨0,.nil _,by decide⟩
  | fork => exact ⟨1,.step (.nav (.upLeft _ _ _ _)) (.nil _),le_rfl⟩

theorem visitsLeaf {key : α} {before after : Source α ρ} {budget : Nat}
    (visit : SourcePointer.VisitsLeaf key before after budget) :
    ∃ cost, Auxiliary.Metadata.Access key (encode before) (encode after) cost ∧ cost ≤ 7*budget+3 := by
  obtain ⟨atLeaf,value,firstReads,lastReads,firstCost,lastCost,first,focus,last,bound⟩ := visit []
  obtain ⟨startCost,startTrace,startBound⟩ := enter_root before
  obtain ⟨frontReads,frontCost,frontTrace,_,frontBound⟩ := trace first
  obtain ⟨backReads,backCost,backTrace,_,backBound⟩ := trace last
  obtain ⟨endCost,endTrace,endBound⟩ := leave_root after
  have reaches : key ∈ pathKeys (Auxiliary.Metadata.forgetCursor (cursor atLeaf)) := by
    rw [forget_cursor]
    rcases atLeaf with ⟨leaf,rest⟩
    dsimp only at focus
    subst leaf
    exact GapBST.leaf_path key value rest
  obtain ⟨servedReads,frontRun,served⟩ := Auxiliary.Metadata.trace_read_ancestor (startTrace.append frontTrace) reaches
  have backRun := backTrace.append endTrace
  refine ⟨_,⟨servedReads++(backReads++[]),frontRun.append backRun,?_⟩,by omega⟩
  simp only [List.map_append,List.mem_append]
  exact .inl served

theorem services {before after : Source α ρ} {requests : List α} {budget : Nat}
    (execution : SourcePointer.Services before requests after budget) :
    ∃ cost, Auxiliary.Metadata.Execution (encode before) requests (encode after) cost ∧
      cost ≤ 7*budget+3*requests.length := by
  induction execution with
  | nil => exact ⟨0,.nil _,by omega⟩
  | cons first rest bound ih =>
    obtain ⟨firstCost,firstRun,firstBound⟩ := visitsLeaf first
    obtain ⟨lastCost,lastRun,lastBound⟩ := ih
    refine ⟨firstCost+lastCost,.cons firstRun lastRun,?_⟩
    simp only [List.length_cons]
    omega

end TangoSquared.Paper20261030.GapBST.Storage
