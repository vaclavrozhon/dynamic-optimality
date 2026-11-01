import TangoSquared.Paper20261030.GapBSTRepresentation
import TangoSquared.Paper20261030.SourceServices
import DynamicOptimality.VisitedAncestors

/-! The gap-key encoding serves the original request. The gap key to the
right of a reached leaf is an ancestor; the final leaf uses the extra
maximum-key root. The shared ancestor-visitation theorem inserts a real
BST service at a cursor that occurs in the compiled trace. -/

namespace TangoSquared.Paper20261030.GapBST

open ColoredStorage DynamicOptimality

variable {α ρ : Type*}

theorem last_mem_frames (last : α) (rest : List (SourcePointer.Frame α ρ)) :
    last ∈ ancestorKeys (frames last rest) := by
  induction rest with
  | nil => simp [frames,ancestorKeys]
  | cons frame rest ih =>
    cases frame with
    | left => simp [frames,ancestorKeys]
    | right => simp only [frames,ancestorKeys,List.mem_cons]; exact .inr ih

theorem park_empty_path (rest : List (MTR.Pointer.Frame α)) :
    pathKeys (park .empty rest) = ancestorKeys rest := by
  cases rest with
  | nil => rfl
  | cons frame rest => cases frame <;> rfl

theorem leaf_path (key : α) (record : ρ) (rest : List (SourcePointer.Frame α ρ)) :
    key ∈ pathKeys (cursor ⟨.leaf key record,rest⟩) := by
  simpa only [cursor,gaps,lastKey,park_empty_path] using last_mem_frames key rest

theorem enter_root (tree : Source α ρ) :
    ∃ cost, MTR.Pointer.Trace (.atRoot (encode tree)) [] (cursor ⟨tree,[]⟩) cost ∧ cost ≤ 1 := by
  cases tree with
  | leaf => exact ⟨0,.nil _,by decide⟩
  | fork => exact ⟨1,.step (.left _ _ _ _ _ _) (.nil _),le_rfl⟩

theorem leave_root (tree : Source α ρ) :
    ∃ cost, MTR.Pointer.Trace (cursor ⟨tree,[]⟩) [] (.atRoot (encode tree)) cost ∧ cost ≤ 1 := by
  cases tree with
  | leaf => exact ⟨0,.nil _,by decide⟩
  | fork => exact ⟨1,.step (.upLeft _ _ _ _) (.nil _),le_rfl⟩

theorem visitsLeaf {key : α} {before after : Source α ρ} {budget : Nat}
    (visit : SourcePointer.VisitsLeaf key before after budget) :
    ∃ cost, MTR.Pointer.Trace (.atRoot (encode before)) [key] (.atRoot (encode after)) cost ∧ cost ≤ budget+3 := by
  obtain ⟨atLeaf,record,firstReads,lastReads,firstCost,lastCost,first,focus,last,bound⟩ := visit []
  obtain ⟨startCost,startTrace,startBound⟩ := enter_root before
  obtain ⟨frontCost,frontTrace,frontBound⟩ := trace first
  obtain ⟨backCost,backTrace,backBound⟩ := trace last
  obtain ⟨endCost,endTrace,endBound⟩ := leave_root after
  have reaches : key ∈ pathKeys (cursor atLeaf) := by
    rcases atLeaf with ⟨leaf,rest⟩
    dsimp only at focus
    subst leaf
    exact leaf_path key record rest
  have frontRun := trace_serve_ancestor (Auxiliary.trace_append startTrace frontTrace) reaches
  have backRun := Auxiliary.trace_append backTrace endTrace
  exact ⟨_,Auxiliary.trace_append frontRun backRun,by omega⟩

theorem services {before after : Source α ρ} {requests : List α} {budget : Nat}
    (execution : SourcePointer.Services before requests after budget) :
    ∃ cost, MTR.Pointer.Execution (encode before) requests (encode after) cost ∧ cost ≤ budget+3*requests.length := by
  induction execution with
  | nil => exact ⟨0,.nil _,by omega⟩
  | cons first rest bound ih =>
    obtain ⟨firstCost,firstTrace,firstBound⟩ := visitsLeaf first
    obtain ⟨lastCost,lastExecution,lastBound⟩ := ih
    refine ⟨firstCost+lastCost,.cons ⟨.atRoot _,rfl,firstTrace⟩ lastExecution,?_⟩
    simp only [List.length_cons]
    omega

end TangoSquared.Paper20261030.GapBST
