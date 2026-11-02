import DynamicOptimality.MultiFinger.MarkedBoundary

/-! A symbolic region step retains exact marker and physical-gap words.
The kernel is an actual rotation trace on at most three exposed markers;
its hanging physical subtrees are unrestricted in size. -/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR
open Pointer (MarkedTree)
open SearchRotation

variable {α : Type*}

def RegionStep (before after : MarkedTree α) (count : Nat) : Prop :=
  ∃ (frame : RegionFrame α) (oldBlock newBlock : MarkedTree α),
    frame.Contains before oldBlock ∧ frame.Contains after newBlock ∧
    oldBlock.skeleton.size ≤ 3 ∧ newBlock.skeleton.size ≤ 3 ∧
    Rotations oldBlock.erase newBlock.erase count

theorem RegionStep.symm {before after : MarkedTree α} {count : Nat}
    (step : RegionStep before after count) : RegionStep after before count := by
  obtain ⟨frame,oldBlock,newBlock,oldInside,newInside,oldSize,newSize,actual⟩ := step
  exact ⟨frame,newBlock,oldBlock,newInside,oldInside,newSize,oldSize,actual.symm⟩

theorem RegionStep.congr {before after newBefore newAfter : MarkedTree α} {count : Nat}
    (step : RegionStep before after count) (oldEq : DataEquivalent before newBefore)
    (newEq : DataEquivalent after newAfter) : RegionStep newBefore newAfter count := by
  obtain ⟨frame,oldBlock,newBlock,oldInside,newInside,oldSize,newSize,actual⟩ := step
  exact ⟨frame,oldBlock,newBlock,⟨oldEq.1.symm.trans oldInside.1,oldEq.2.symm.trans oldInside.2⟩,
    ⟨newEq.1.symm.trans newInside.1,newEq.2.symm.trans newInside.2⟩,oldSize,newSize,actual⟩

theorem RegionStep.left {before after : MarkedTree α} {count : Nat}
    (step : RegionStep before after count) (key : α) (right : MarkedTree α) :
    RegionStep (.node before key right) (.node after key right) count := by
  obtain ⟨frame,oldBlock,newBlock,oldInside,newInside,oldSize,newSize,actual⟩ := step
  let outer : RegionFrame α := {
    beforeKeys := frame.beforeKeys
    beforeHoles := frame.beforeHoles
    afterKeys := frame.afterKeys ++ [key] ++ right.skeleton.inorder
    afterHoles := frame.afterHoles ++ right.holes
    beforeCount := frame.beforeCount
    afterCount := by simp only [List.length_append,List.length_cons,List.length_nil,
      MarkedTree.holes_length,Tree.length_inorder,frame.afterCount] <;> omega }
  refine ⟨outer,oldBlock,newBlock,?_,?_,oldSize,newSize,actual⟩ <;>
    simp [RegionFrame.Contains,outer,MarkedTree.skeleton,Tree.inorder,MarkedTree.holes,
      oldInside.1,oldInside.2,newInside.1,newInside.2,List.append_assoc]

theorem RegionStep.right {before after : MarkedTree α} {count : Nat}
    (step : RegionStep before after count) (left : MarkedTree α) (key : α) :
    RegionStep (.node left key before) (.node left key after) count := by
  obtain ⟨frame,oldBlock,newBlock,oldInside,newInside,oldSize,newSize,actual⟩ := step
  let outer : RegionFrame α := {
    beforeKeys := left.skeleton.inorder ++ [key] ++ frame.beforeKeys
    beforeHoles := left.holes ++ frame.beforeHoles
    afterKeys := frame.afterKeys
    afterHoles := frame.afterHoles
    beforeCount := by simp only [List.length_append,List.length_cons,List.length_nil,
      MarkedTree.holes_length,Tree.length_inorder,frame.beforeCount] <;> omega
    afterCount := frame.afterCount }
  refine ⟨outer,oldBlock,newBlock,?_,?_,oldSize,newSize,actual⟩ <;>
    simp [RegionFrame.Contains,outer,MarkedTree.skeleton,Tree.inorder,MarkedTree.holes,
      oldInside.1,oldInside.2,newInside.1,newInside.2,List.append_assoc]

theorem RegionStep.low {before after : MarkedTree α} {count : Nat}
    (step : RegionStep before after count)
    (queue : Option (GeometricOnlineSimulation.OpenDeque.Right α)) :
    RegionStep (lowMarked queue before) (lowMarked queue after) count := by
  cases queue with
  | none => exact step
  | some layout =>
      cases shape : layout.port.middle with
      | none => simpa only [lowMarked,rightMarked,shape] using step.right (.hole layout.port.left) layout.port.pivot
      | some pair =>
          rcases pair with ⟨middle,key⟩
          simpa only [lowMarked,rightMarked,shape] using
            (step.right (.hole middle) key).right (.hole layout.port.left) layout.port.pivot

theorem RegionStep.high {before after : MarkedTree α} {count : Nat}
    (step : RegionStep before after count)
    (queue : Option (GeometricOnlineSimulation.OpenDeque.Left α)) :
    RegionStep (highMarked queue before) (highMarked queue after) count := by
  cases queue with
  | none => exact step
  | some layout =>
      cases shape : layout.port.middle with
      | none => simpa only [highMarked,leftMarked,shape] using step.left layout.port.pivot (.hole layout.port.right)
      | some pair =>
          rcases pair with ⟨key,middle⟩
          simpa only [highMarked,leftMarked,shape] using
            (step.left key (.hole middle)).left layout.port.pivot (.hole layout.port.right)

theorem RegionStep.tendon {before after : MarkedTree α} {count : Nat}
    (step : RegionStep before after count) (tendon : TendonContents.Tendon α) :
    RegionStep (tendon.marked before) (tendon.marked after) count :=
  (step.high tendon.highQueue).low tendon.lowQueue

end DynamicOptimality.MultiFinger
