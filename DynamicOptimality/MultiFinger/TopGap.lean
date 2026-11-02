import DynamicOptimality.MultiFinger.TopDeletion
import Mathlib.Data.List.Nodup

/-! # Exposing any retained inorder gap near the physical root

Splay the predecessor marker, then the least marker in its right child.
The selected gap is then at depth at most two. The outermost gaps need
only one splay. Every opaque gap keeps its exact physical subtree and
inorder position, including when the selected subtree is empty.
-/

namespace DynamicOptimality.MultiFinger.Top

open ChaCha.MTR
open Pointer (MarkedTree)
open SearchRotation
open ChaCha.Paper20261030.SplayAuxiliary (potential)

variable {α : Type*}

theorem context_gapArray (context : MarkedTree.Context α) (gap : RawTree α) :
    (context.plug (.hole gap)).gapArray context.holesBefore.length = gap := by
  simp only [MarkedTree.gapArray,MarkedTree.Context.holes_plug,MarkedTree.holes,
    List.append_assoc,List.singleton_append]
  rw [List.getElem?_append_right (by omega)]
  simp

theorem original_gap (before : MarkedTree α) (context : MarkedTree.Context α)
    (gap : RawTree α) (index : Nat)
    (holes : (context.plug (.hole gap)).holes = before.holes)
    (position : context.holesBefore.length = index) : gap = before.gapArray index := by
  rw [← position]
  have same : (context.plug (.hole gap)).gapArray = before.gapArray := by
    funext i
    simp only [MarkedTree.gapArray,holes]
  rw [← same]
  exact (context_gapArray context gap).symm

variable [LinearOrder α]

theorem root_index (left right : RawTree α) (key : α)
    (ordered : (ChaCha.MTR.Tree.node left key right).Ordered) :
    (ChaCha.MTR.Tree.node left key right).inorder.idxOf key = left.size := by
  have absent : key ∉ left.inorder := fun member =>
    lt_irrefl key ((RawDepth.node_parts ordered).2.2.1 key member)
  simp [Tree.inorder,List.append_assoc,List.idxOf_append,absent,Tree.length_inorder]

/-- The returned context is shallow in the actual marked tree; its hole
is the original selected subtree, not merely an inorder-equivalent one. -/
theorem expose_gap (before : MarkedTree α) (ordered : before.skeleton.Ordered)
    (index : Nat) (within : index ≤ before.skeleton.size)
    {capacity : Nat} (fits : before.skeleton.size ≤ capacity) :
    ∃ (after : MarkedTree α) (context : MarkedTree.Context α) (gap : RawTree α) (rotations : Nat),
      after = context.plug (.hole gap) ∧ contextDepth context ≤ 2 ∧
      context.holesBefore.length = index ∧ gap = before.gapArray index ∧
      after.holes = before.holes ∧ after.skeleton.inorder = before.skeleton.inorder ∧
      Rotations before.erase after.erase rotations ∧
      rotations+2*potential after.skeleton ≤
        2*potential before.skeleton+12*Nat.log 2 capacity+2 := by
  by_cases empty : before.skeleton = .empty
  · obtain ⟨gap,rfl⟩ := hole_of_empty empty
    have zero : index = 0 := by simp only [MarkedTree.skeleton,Tree.size] at within; omega
    subst index
    exact ⟨.hole gap,.top,gap,0,rfl,by simp [contextDepth],rfl,rfl,rfl,rfl,.refl _,by omega⟩
  · by_cases zero : index = 0
    · subst index
      obtain ⟨key,gap,right,rotations,splay,holes,actual,bound⟩ :=
        expose_minimum before ordered empty fits
      let context : MarkedTree.Context α := .left key right .top
      have position : context.holesBefore.length = 0 := rfl
      refine ⟨.node (.hole gap) key right,context,gap,rotations,rfl,by simp [context,contextDepth],position,
        original_gap before context gap 0 holes position,holes,splay.inorder_eq.symm,actual,?_⟩
      omega
    · have keyBound : index-1 < before.skeleton.inorder.length := by
        rw [Tree.length_inorder]
        omega
      let key := before.skeleton.inorder[index-1]
      have member : key ∈ before.skeleton.inorder := List.getElem_mem keyBound
      have unique : before.skeleton.inorder.Nodup := ordered.imp (fun less => ne_of_lt less)
      have keyPosition : before.skeleton.inorder.idxOf key = index-1 := unique.idxOf_getElem _ keyBound
      obtain ⟨middle,firstWork,firstSplay,firstHoles,root,physicalRoot,firstActual,firstBound⟩ :=
        expose before key unique member fits
      have nextOrdered := firstSplay.ordered_after ordered
      cases middle with
      | hole tree => simp [MarkedTree.skeleton,Tree.rootKey] at root
      | node left pivot right =>
          have same : pivot = key := Option.some.inj root
          subst pivot
          have leftSize : left.skeleton.size+1 = index := by
            rw [firstSplay.inorder_eq] at keyPosition
            change (ChaCha.MTR.Tree.node left.skeleton key right.skeleton).inorder.idxOf key = index-1 at keyPosition
            rw [root_index left.skeleton right.skeleton key nextOrdered] at keyPosition
            omega
          by_cases rightEmpty : right.skeleton = .empty
          · obtain ⟨gap,rfl⟩ := hole_of_empty rightEmpty
            let context : MarkedTree.Context α := .right left key .top
            have position : context.holesBefore.length = index := by
              simpa only [context,MarkedTree.Context.holesBefore,List.length_append,List.length_nil,
                Nat.add_zero,MarkedTree.holes_length] using leftSize
            refine ⟨.node left key (.hole gap),context,gap,firstWork,rfl,by simp [context,contextDepth],position,
              original_gap before context gap index firstHoles position,firstHoles,
              firstSplay.inorder_eq.symm,firstActual,?_⟩
            omega
          · have rightFits : right.skeleton.size ≤ capacity := by
              have sizes := firstSplay.size_eq
              simp only [MarkedTree.skeleton,Tree.size] at sizes
              omega
            obtain ⟨hi,gap,last,secondWork,secondSplay,secondHoles,secondActual,secondBound⟩ :=
              expose_minimum right (RawDepth.node_parts nextOrdered).2.1 rightEmpty rightFits
            let after := MarkedTree.node left key (.node (.hole gap) hi last)
            let context : MarkedTree.Context α := .right left key (.left hi last .top)
            have holes : after.holes = before.holes := by
              change left.holes ++ (MarkedTree.node (.hole gap) hi last).holes = _
              rw [secondHoles]
              exact firstHoles
            have position : context.holesBefore.length = index := by
              simpa only [context,MarkedTree.Context.holesBefore,List.length_append,List.length_nil,
                Nat.add_zero,MarkedTree.holes_length] using leftSize
            have exchange := root_potential_exchange left.skeleton left.skeleton right.skeleton
              (MarkedTree.node (.hole gap) hi last).skeleton key rfl secondSplay.size_eq
            refine ⟨after,context,gap,firstWork+secondWork,rfl,by simp [context,contextDepth],position,
              original_gap before context gap index holes position,holes,?_,
              firstActual.append (secondActual.plug [.right left.erase key]),?_⟩
            · rw [firstSplay.inorder_eq]
              change left.skeleton.inorder++[key]++(MarkedTree.node (.hole gap) hi last).skeleton.inorder =
                left.skeleton.inorder++[key]++right.skeleton.inorder
              rw [secondSplay.inorder_eq]
            · dsimp only [after]
              simp only [MarkedTree.skeleton,potential] at firstBound secondBound exchange ⊢
              omega

end DynamicOptimality.MultiFinger.Top
