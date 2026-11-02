import DynamicOptimality.MultiFinger.TopDeletionPrimitives
import DynamicOptimality.MultiFinger.TopExtremes

/-! # Complete deletion of an exposed top marker

At most two ordinary splays expose its predecessor and successor among
the other top keys. The remaining rotations move the removed marker into
an opaque gap. This changes the retained top set by exactly one key and
does not delete any physical BST key.
-/

namespace DynamicOptimality.MultiFinger.Top

open ChaCha.MTR
open Pointer (MarkedTree)
open SearchRotation
open ChaCha.Paper20261030.SplayAuxiliary (potential rank)

variable {α : Type*}

theorem hole_of_empty {tree : MarkedTree α} (empty : tree.skeleton = .empty) :
    ∃ physical, tree = .hole physical := by
  cases tree with
  | hole physical => exact ⟨physical,rfl⟩
  | node left key right => cases empty

theorem root_potential_exchange (beforeLeft afterLeft beforeRight afterRight : RawTree α)
    (key : α) (leftSize : beforeLeft.size = afterLeft.size)
    (rightSize : beforeRight.size = afterRight.size) :
    potential (.node afterLeft key afterRight)+potential beforeLeft+potential beforeRight =
      potential (.node beforeLeft key beforeRight)+potential afterLeft+potential afterRight := by
  simp only [potential,rank,Tree.size,leftSize,rightSize]
  omega

variable [LinearOrder α]

/-- Remove only the mark on the exposed root. Every original physical key
is preserved by the returned ordinary-rotation transcript. -/
theorem remove_root (left right : MarkedTree α) (key : α)
    (ordered : (MarkedTree.node left key right).skeleton.Ordered)
    {capacity : Nat} (fits : (MarkedTree.node left key right).skeleton.size ≤ capacity) :
    ∃ after : MarkedTree α, ∃ rotations : Nat,
      Rotations (MarkedTree.node left key right).erase after.erase rotations ∧
      after.skeleton.inorder = left.skeleton.inorder++right.skeleton.inorder ∧
      after.holes = mergedRootHoles key left.holes right.holes ∧
      after.skeleton.size+1 = (MarkedTree.node left key right).skeleton.size ∧
      rotations+2*potential after.skeleton ≤
        2*potential (MarkedTree.node left key right).skeleton+12*Nat.log 2 capacity+4 := by
  have parts := RawDepth.node_parts ordered
  have leftFits : left.skeleton.size ≤ capacity := by
    simp only [MarkedTree.skeleton,Tree.size] at fits
    omega
  have rightFits : right.skeleton.size ≤ capacity := by
    simp only [MarkedTree.skeleton,Tree.size] at fits
    omega
  by_cases leftEmpty : left.skeleton = .empty
  · obtain ⟨first,rfl⟩ := hole_of_empty leftEmpty
    by_cases rightEmpty : right.skeleton = .empty
    · obtain ⟨last,rfl⟩ := hole_of_empty rightEmpty
      obtain ⟨actual,sizes,cheaper⟩ := remove_only first last key
      exact ⟨.hole (.node first key last),0,actual,rfl,remove_only_holes first last key,sizes,by omega⟩
    · obtain ⟨hi,inner,last,work,splay,holes,actual,bound⟩ :=
        expose_minimum right parts.2.1 rightEmpty rightFits
      obtain ⟨finish,sizes,cheaper⟩ := remove_with_right last first inner key hi
      have exchange := root_potential_exchange (.empty : RawTree α) .empty
        right.skeleton (MarkedTree.node (.hole inner) hi last).skeleton key rfl splay.size_eq
      refine ⟨.node (.hole (.node first key inner)) hi last,work+1,
        (actual.plug [.right first key]).append finish,?_,?_,?_,?_⟩
      · simpa only [MarkedTree.skeleton,Tree.inorder,List.nil_append] using splay.inorder_eq.symm
      · rw [← holes]
        exact remove_with_right_holes last first inner key hi
      · have shape := splay.size_eq
        simp only [MarkedTree.skeleton,Tree.size] at sizes shape ⊢
        omega
      · simp only [MarkedTree.skeleton,potential] at bound exchange cheaper ⊢
        omega
  · obtain ⟨lo,first,innerLeft,leftWork,leftSplay,leftHoles,leftActual,leftBound⟩ :=
      expose_maximum left parts.1 leftEmpty leftFits
    by_cases rightEmpty : right.skeleton = .empty
    · obtain ⟨last,rfl⟩ := hole_of_empty rightEmpty
      obtain ⟨finish,sizes,cheaper⟩ := remove_with_left first innerLeft last lo key
      have exchange := root_potential_exchange left.skeleton
        (MarkedTree.node first lo (.hole innerLeft)).skeleton .empty .empty key leftSplay.size_eq rfl
      refine ⟨.node first lo (.hole (.node innerLeft key last)),leftWork+1,
        (leftActual.plug [.left key last]).append finish,?_,?_,?_,?_⟩
      · simpa only [MarkedTree.skeleton,Tree.inorder,List.append_nil] using leftSplay.inorder_eq.symm
      · rw [← leftHoles]
        exact remove_with_left_holes first innerLeft last lo key
      · have shape := leftSplay.size_eq
        simp only [MarkedTree.skeleton,Tree.size] at sizes shape ⊢
        omega
      · simp only [MarkedTree.skeleton,potential] at leftBound exchange cheaper ⊢
        omega
    · obtain ⟨hi,innerRight,last,rightWork,rightSplay,rightHoles,rightActual,rightBound⟩ :=
        expose_minimum right parts.2.1 rightEmpty rightFits
      obtain ⟨finish,sizes,cheaper⟩ := remove_both first last innerLeft innerRight lo key hi
      have exchange := root_potential_exchange left.skeleton
        (MarkedTree.node first lo (.hole innerLeft)).skeleton right.skeleton
        (MarkedTree.node (.hole innerRight) hi last).skeleton key leftSplay.size_eq rightSplay.size_eq
      have localRun := (leftActual.plug [.left key right.erase]).append
        (rightActual.plug [.right (MarkedTree.node first lo (.hole innerLeft)).erase key])
      refine ⟨.node first lo (.node (.hole (.node innerLeft key innerRight)) hi last),
        leftWork+rightWork+2,localRun.append finish,?_,?_,?_,?_⟩
      · rw [leftSplay.inorder_eq,rightSplay.inorder_eq]
        simp only [MarkedTree.skeleton,Tree.inorder,List.nil_append,List.append_nil,List.append_assoc]
      · rw [← leftHoles,← rightHoles]
        exact remove_both_holes first last innerLeft innerRight lo key hi
      · have shapeLeft := leftSplay.size_eq
        have shapeRight := rightSplay.size_eq
        simp only [MarkedTree.skeleton,Tree.size] at sizes shapeLeft shapeRight ⊢
        omega
      · simp only [MarkedTree.skeleton,potential] at leftBound rightBound exchange cheaper ⊢
        omega

end DynamicOptimality.MultiFinger.Top
