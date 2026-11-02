import MultiSplay.ComparatorPointerProgram
import ChaCha.Paper20261030.GapBSTRepresentation

/-!
# Comparator preparation on the actual gap keys

Only the existing `GapBST.gaps` tree is used: no additional maximum-key root
is introduced. A source leaf cursor is parked at its adjacent physical
parent, and source metadata operations disappear from the physical trace.
-/

namespace MultiSplay.ComparatorGap

open ChaCha
open Paper20261030
open ColoredStorage
open GapBST (gaps lastKey park setRoot_gaps setRoot_lastKey)

variable {α ρ : Type*}

def frames (last : α) : List (SourcePointer.Frame α ρ) → List (MTR.Pointer.Frame α)
  | [] => []
  | .left _ right :: rest => .left last (gaps right) :: frames (lastKey right) rest
  | .right left _ :: rest => .right (gaps left) (lastKey left) :: frames last rest

def cursor (logical : SourcePointer.Cursor α ρ) : MTR.Pointer.Cursor α :=
  park (gaps logical.focus) (frames (lastKey logical.focus) logical.ancestors)

theorem frames_tree (focus : Source α ρ) (rest : List (SourcePointer.Frame α ρ)) :
    MTR.Pointer.plug (gaps focus) (frames (lastKey focus) rest) = gaps (SourcePointer.plug focus rest) := by
  induction rest generalizing focus with
  | nil => rfl
  | cons frame rest ih =>
      cases frame with
      | left record right => exact ih (.fork record focus right)
      | right left record => exact ih (.fork record left focus)

theorem cursor_tree (logical : SourcePointer.Cursor α ρ) :
    (cursor logical).tree = gaps logical.tree :=
  (GapBST.park_tree _ _).trans (frames_tree _ _)

theorem cursor_root (tree : Source α ρ) :
    cursor ⟨tree,[]⟩ = MTR.Pointer.Cursor.atRoot (gaps tree) := by
  cases tree <;> rfl

theorem step_trace {before after : SourcePointer.Cursor α ρ}
    (step : SourcePointer.Step before after) :
    ∃ cost, MTR.Pointer.Trace (cursor before) [] (cursor after) cost ∧ cost ≤ 1 := by
  cases step with
  | left left right record rest =>
      cases left with
      | leaf key old => exact ⟨0,.nil _,by decide⟩
      | fork old a b => exact ⟨1,.step (.left _ _ _ _ _ _) (.nil _),le_rfl⟩
  | right left right record rest =>
      cases right with
      | leaf key old => exact ⟨0,.nil _,by decide⟩
      | fork old a b => exact ⟨1,.step (.right _ _ _ _ _ _) (.nil _),le_rfl⟩
  | upLeft left right record rest =>
      cases left with
      | leaf key old => exact ⟨0,.nil _,by decide⟩
      | fork old a b => exact ⟨1,.step (.upLeft _ _ _ _) (.nil _),le_rfl⟩
  | upRight left right record rest =>
      cases right with
      | leaf key old => exact ⟨0,.nil _,by decide⟩
      | fork old a b => exact ⟨1,.step (.upRight _ _ _ _) (.nil _),le_rfl⟩
  | rotateRight => exact ⟨1,.step (.rotateRight _ _ _ _ _ _) (.nil _),le_rfl⟩
  | rotateLeft => exact ⟨1,.step (.rotateLeft _ _ _ _ _ _) (.nil _),le_rfl⟩
  | write focus record rest =>
      refine ⟨0,?_,by decide⟩
      simp only [cursor,setRoot_gaps,setRoot_lastKey]
      exact .nil _

theorem trace {before after : SourcePointer.Cursor α ρ} {reads : List ρ} {budget : Nat}
    (execution : SourcePointer.Trace before reads after budget) :
    ∃ cost, MTR.Pointer.Trace (cursor before) [] (cursor after) cost ∧ cost ≤ budget := by
  induction execution with
  | nil => exact ⟨0,.nil _,le_rfl⟩
  | step move rest ih =>
      obtain ⟨first,firstTrace,firstBound⟩ := step_trace move
      obtain ⟨last,lastTrace,lastBound⟩ := ih
      exact ⟨first+last,Auxiliary.trace_append firstTrace lastTrace,by omega⟩
  | read rest ih =>
      obtain ⟨cost,run,bound⟩ := ih
      exact ⟨cost,run,by omega⟩

theorem root_trace_program {before after : Source α ρ} {reads : List ρ} {budget : Nat}
    (execution : SourcePointer.Trace ⟨before,[]⟩ reads ⟨after,[]⟩ budget) :
    ∃ work ≤ 12 * (budget + 1), CommonForest.Program [gaps before] [] [gaps after] work := by
  obtain ⟨cost,run,bound⟩ := trace execution
  rw [cursor_root,cursor_root] at run
  obtain ⟨work,workBound,program⟩ := CommonForest.pointer_trace_program run rfl
  exact ⟨work,by omega,program⟩

theorem rearranges_program {before after : Source α ρ} {budget : Nat}
    (execution : SourcePointer.Rearranges before after budget) :
    ∃ work ≤ 12 * (budget + 1), CommonForest.Program [gaps before] [] [gaps after] work := by
  obtain ⟨reads,cost,run,bound⟩ := execution []
  obtain ⟨work,workBound,program⟩ := root_trace_program run
  exact ⟨work,by omega,program⟩

end MultiSplay.ComparatorGap
