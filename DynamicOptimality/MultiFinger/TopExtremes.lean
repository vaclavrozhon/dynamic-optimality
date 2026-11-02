import DynamicOptimality.MultiFinger.TopAccess
import DynamicOptimality.SearchRotationDepth
import Mathlib.Data.Finset.Max

/-! # Exposing a top predecessor or successor

The extreme key is selected from the existing marked skeleton. Ordinary
splaying then leaves the corresponding outer child as one actual gap.
These lemmas include the complete physical rotation transcript.
-/

namespace DynamicOptimality.MultiFinger.Top

open ChaCha.MTR
open Pointer (MarkedTree)
open SearchRotation
open ChaCha.Paper20261030.SplayAuxiliary (potential)

variable {α : Type*} [LinearOrder α]

theorem expose_maximum (before : MarkedTree α)
    (ordered : before.skeleton.Ordered) (nonempty : before.skeleton ≠ .empty)
    {capacity : Nat} (fits : before.skeleton.size ≤ capacity) :
    ∃ key : α, ∃ left : MarkedTree α, ∃ gap : RawTree α, ∃ rotations : Nat,
      let after := MarkedTree.node left key (.hole gap)
      MultiSplay.Auxiliary.Splay key before.skeleton after.skeleton rotations ∧
      after.holes = before.holes ∧ Rotations before.erase after.erase rotations ∧
      rotations+2*potential after.skeleton ≤
        2*potential before.skeleton+6*Nat.log 2 capacity+1 := by
  classical
  let keys := before.skeleton.inorder.toFinset
  have someKey : keys.Nonempty := by
    cases shape : before.skeleton with
    | empty => exact (nonempty shape).elim
    | node left key right => exact ⟨key,by simp [keys,shape,Tree.inorder]⟩
  let key := keys.max' someKey
  have member : key ∈ before.skeleton.inorder := List.mem_toFinset.mp (Finset.max'_mem keys someKey)
  have unique : before.skeleton.inorder.Nodup := ordered.imp (fun less => ne_of_lt less)
  obtain ⟨after,rotations,splay,holes,root,physicalRoot,actual,bound⟩ := expose before key unique member fits
  have nextOrdered : after.skeleton.Ordered := by
    change after.skeleton.inorder.Pairwise (· < ·)
    rw [← splay.inorder_eq]
    exact ordered
  cases after with
  | hole tree => simp [MarkedTree.skeleton,Tree.rootKey] at root
  | node left pivot right =>
      have same : pivot = key := Option.some.inj root
      subst pivot
      cases right with
      | hole gap => exact ⟨key,left,gap,rotations,splay,holes,actual,bound⟩
      | node a bad b =>
          have above := (RawDepth.node_parts nextOrdered).2.2.2 bad
            (by simp [MarkedTree.skeleton,Tree.inorder])
          have oldMember : bad ∈ before.skeleton.inorder := by
            rw [splay.inorder_eq]
            simp [MarkedTree.skeleton,Tree.inorder]
          have below : bad ≤ key := Finset.le_max' keys bad (List.mem_toFinset.mpr oldMember)
          exact False.elim (not_lt_of_ge below above)

theorem expose_minimum (before : MarkedTree α)
    (ordered : before.skeleton.Ordered) (nonempty : before.skeleton ≠ .empty)
    {capacity : Nat} (fits : before.skeleton.size ≤ capacity) :
    ∃ key : α, ∃ gap : RawTree α, ∃ right : MarkedTree α, ∃ rotations : Nat,
      let after := MarkedTree.node (.hole gap) key right
      MultiSplay.Auxiliary.Splay key before.skeleton after.skeleton rotations ∧
      after.holes = before.holes ∧ Rotations before.erase after.erase rotations ∧
      rotations+2*potential after.skeleton ≤
        2*potential before.skeleton+6*Nat.log 2 capacity+1 := by
  classical
  let keys := before.skeleton.inorder.toFinset
  have someKey : keys.Nonempty := by
    cases shape : before.skeleton with
    | empty => exact (nonempty shape).elim
    | node left key right => exact ⟨key,by simp [keys,shape,Tree.inorder]⟩
  let key := keys.min' someKey
  have member : key ∈ before.skeleton.inorder := List.mem_toFinset.mp (Finset.min'_mem keys someKey)
  have unique : before.skeleton.inorder.Nodup := ordered.imp (fun less => ne_of_lt less)
  obtain ⟨after,rotations,splay,holes,root,physicalRoot,actual,bound⟩ := expose before key unique member fits
  have nextOrdered : after.skeleton.Ordered := by
    change after.skeleton.inorder.Pairwise (· < ·)
    rw [← splay.inorder_eq]
    exact ordered
  cases after with
  | hole tree => simp [MarkedTree.skeleton,Tree.rootKey] at root
  | node left pivot right =>
      have same : pivot = key := Option.some.inj root
      subst pivot
      cases left with
      | hole gap => exact ⟨key,gap,right,rotations,splay,holes,actual,bound⟩
      | node a bad b =>
          have below := (RawDepth.node_parts nextOrdered).2.2.1 bad
            (by simp [MarkedTree.skeleton,Tree.inorder])
          have oldMember : bad ∈ before.skeleton.inorder := by
            rw [splay.inorder_eq]
            simp [MarkedTree.skeleton,Tree.inorder]
          have above : key ≤ bad := Finset.min'_le keys bad (List.mem_toFinset.mpr oldMember)
          exact False.elim (not_lt_of_ge above below)

end DynamicOptimality.MultiFinger.Top
