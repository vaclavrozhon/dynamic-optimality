import ChaCha.Paper20261030.SplayAuxiliaryPreferred
import ChaCha.Paper20261030.SearchRotationMetadata

/-!
# Root-auxiliary reshaping preserves actual attached components

A rotation sequence of the root auxiliary carries its complete ordered gap
payloads. Its descendants, their shapes, and their potential remain fixed.
This is the structural lemma used by terminal and boundary exposures.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open DynamicOptimality.SearchRotation
open ChaCha.MTR
open MultiSplay EndpointEncoding ClassicalSwitch Global Global.Preferred
open Pointer (MarkedTree)

variable {α : Type*}

theorem reshape_inventory {state : State} {reference : RawTree α} {before : MarkedTree α}
    (unique : reference.inorder.Nodup) (represented : Component state reference before)
    {trees : List (RawTree α)} (inventory : Core state reference before.erase trees)
    {after : RawTree α} {rotations : Nat} (run : Rotations before.skeleton after rotations) :
    ∃ main : MarkedTree α, ∃ next : List (RawTree α),
      main.skeleton = after ∧ main.holes = before.holes ∧
      Component state reference main ∧ Core state reference main.erase next ∧
      Rotations before.erase main.erase rotations ∧
      forestPotential next+potential before.skeleton = forestPotential trees+potential after := by
  let main := markedGraft after before.gapArray 0
  have skeleton : main.skeleton = after := markedGraft_skeleton _ _ _
  have holes : main.holes = before.holes := by
    have same := rotations_holes run before.gapArray 0
    simpa only [markedGraft_gapArray,main] using same.symm
  have keys : main.skeleton.inorder = (preferred state reference).inorder := by
    rw [skeleton,SearchRotationBridge.rotations_inorder run,represented.1]
  have representation : Component state reference main := by
    refine ⟨keys,?_⟩
    intro index entry found
    simpa only [MarkedTree.gapArray,holes] using represented.2 index entry found
  obtain ⟨descendants,treeEq,children⟩ := inventory.expose unique represented
  have newChildren : Branches state (preferredHoles state reference) main.holes descendants := by
    rw [holes]
    exact children
  have nextInventory := Core.of_branches keys newChildren
  have actual : Rotations before.erase main.erase rotations := by
    simpa only [main,markedGraft_erase,MarkedTree.graft_gapArray] using
      rotations_graft run before.gapArray 0
  refine ⟨main,_,skeleton,holes,representation,nextInventory,actual,?_⟩
  rw [treeEq]
  simp only [forestPotential_append,forestPotential_rootPart,skeleton]
  omega

/-- A genuine ordinary splay changes only the root auxiliary's contribution
to the global inventory. All nested components retain their potential. -/
theorem root_splay {state : State} {reference : RawTree α} {before : MarkedTree α}
    (unique : reference.inorder.Nodup) (represented : Component state reference before)
    {trees : List (RawTree α)} (inventory : Core state reference before.erase trees)
    {key : α} (present : key ∈ before.skeleton.inorder)
    {capacity : Nat} (fits : before.skeleton.size ≤ capacity) :
    ∃ main : MarkedTree α, ∃ next : List (RawTree α), ∃ rotations : Nat,
      Auxiliary.Splay key before.skeleton main.skeleton rotations ∧
      main.holes = before.holes ∧
      Component state reference main ∧ Core state reference main.erase next ∧
      Rotations before.erase main.erase rotations ∧
      rotations+2*forestPotential next ≤ 2*forestPotential trees+6*Nat.log 2 capacity+1 := by
  classical
  have skeletonUnique : before.skeleton.inorder.Nodup := by
    rw [represented.1]
    exact unique.sublist (preferred_sublist state reference)
  obtain ⟨after,rotations,splay,pointer⟩ := Auxiliary.exists_pointer_splay present
  obtain ⟨main,next,skeleton,holes,representation,nextInventory,actual,potentialEq⟩ :=
    reshape_inventory unique represented inventory (splay_rotations splay)
  have bound := splay_amortized_capacity splay skeletonUnique fits
  refine ⟨main,next,rotations,?_,holes,representation,nextInventory,actual,?_⟩
  · rw [skeleton]
    exact splay
  · omega

end ChaCha.Paper20261030.SplayAuxiliary
