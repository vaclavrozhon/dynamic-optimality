import MultiSplay.ComparatorReconfiguration
import ChaCha.PointerModel

/-!
# Turning an actual pointer rearrangement into comparator preparation

The pointer trace determines its touched rooted skeleton and all untouched
gap subtrees. Shallow reconfiguration of that skeleton costs linear work in
the common-forest metric, even when the original rotations occurred deeply.
-/

namespace MultiSplay.CommonForest

open ChaCha.MTR
open ChaCha.MTR.Tree

variable {α : Type*}

theorem pointer_trace_program {before after : DynamicOptimality.RawTree α} {final : Pointer.Cursor α} {cost : Nat}
    (execution : Pointer.Trace (Pointer.Cursor.atRoot before) [] final cost)
    (endpoint : final.tree = after) :
    ∃ work ≤ 12 * (cost + 1), Program [before] [] [after] work := by
  cases before with
  | empty =>
      have unchanged : final = Pointer.Cursor.atRoot .empty := by
        cases execution with
        | nil => rfl
        | step move rest => cases move
      have endEmpty : after = .empty := endpoint.symm.trans (congrArg Pointer.Cursor.tree unchanged)
      exact ⟨0,by omega,by rw [endEmpty]; exact .nil _⟩
  | node left key right =>
      let start : Pointer.SeenCursor α := ⟨.hole left,key,.hole right,[]⟩
      let source : Pointer.MarkedTree α := .node (.hole left) key (.hole right)
      obtain ⟨last,touched,lastCursor,sourceTree,sameHoles,sameKeys,_,sizeBound,_⟩ :=
        execution.tracked start rfl source rfl rfl
      have beforeTree : graft touched.skeleton touched.gapArray 0 = .node left key right :=
        touched.graft_gapArray.trans sourceTree
      have afterTree : graft last.tree.skeleton touched.gapArray 0 = after := by
        have gapArrays : touched.gapArray = last.tree.gapArray := by
          funext i
          simp only [Pointer.MarkedTree.gapArray,sameHoles]
        rw [gapArrays,last.tree.graft_gapArray,last.erase_tree,lastCursor,endpoint]
      obtain ⟨count,countBound,rotations⟩ :=
        graft_simulation_linear touched.skeleton last.tree.skeleton sameKeys touched.gapArray 0
      obtain ⟨work,workBound,program⟩ := restrictedSteps_program rotations
      have equalSize : size touched.skeleton = size last.tree.skeleton := by
        simpa only [length_inorder] using congrArg List.length sameKeys
      have small : size touched.skeleton ≤ cost + 1 := by
        simpa [source,Pointer.MarkedTree.skeleton,size,Nat.add_comm] using sizeBound
      refine ⟨work,by omega,?_⟩
      simpa only [beforeTree,afterTree] using program

end MultiSplay.CommonForest
