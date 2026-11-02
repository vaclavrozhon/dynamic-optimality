import MultiSplay.Obstructions.ClassicalRelabelFamily
import MultiSplay.Obstructions.ClassicalReferenceFamily
import MultiSplay.GlobalPreferredInventoryRoot
import DynamicOptimality.ModelOnline
import ChaCha.Paper20261030.SearchRotationMetadata

/-! Physical attachment and the complete persistent classical potential.
Changing the root auxiliary shape retains every foreign subtree. The
leaf switch replaces only that auxiliary's contribution to the inventory. -/

namespace MultiSplay.Obstructions.Classical

open DynamicOptimality (RawTree)
open DynamicOptimality.SearchRotation
open ChaCha.MTR
open ChaCha.MTR.Tree
open Pointer (MarkedTree)
open ChaCha.Primary (Key)
open ChaCha.Paper20261030
open EndpointEncoding ClassicalSwitch Global Global.Preferred

noncomputable def forestRank (trees : List (RawTree Nat)) : ℝ := (trees.map potential).sum

@[simp] theorem forestRank_append (a b : List (RawTree Nat)) :
    forestRank (a++b) = forestRank a+forestRank b := by simp [forestRank]

@[simp] theorem forestRank_rootPart (tree : RawTree Nat) :
    forestRank (rootPart tree) = potential tree := by cases tree <;> simp [rootPart,forestRank,potential]

 theorem forestRank_perm {a b : List (RawTree Nat)} (same : a.Perm b) :
    forestRank a = forestRank b := (same.map potential).sum_eq

/-- Every auxiliary shape on exactly the preferred path's keys has an
actual initial physical representation, with the original off-path trees. -/
 theorem initial_shape (state : State) (reference skeleton : RawTree Nat)
    (word : skeleton.inorder = (preferred state reference).inorder) :
    ∃ before : MarkedTree Nat,
      before.skeleton = skeleton ∧ Component state reference before ∧
      before.erase.inorder = reference.inorder := by
  obtain ⟨initial,physical,represented⟩ := (Global.Preferred.initial state reference).expose
  have same : initial.skeleton.inorder = skeleton.inorder := represented.1.trans word.symm
  obtain ⟨count,_,steps⟩ := restricted_rotation_linear initial.skeleton skeleton same
  have run := DynamicOptimality.OnlineModel.restrictedSteps_to_rotations steps
  let before := markedGraft skeleton initial.gapArray 0
  have shape : before.skeleton = skeleton := markedGraft_skeleton _ _ _
  have holes : before.holes = initial.holes := by
    simpa only [before,markedGraft_gapArray] using (rotations_holes run initial.gapArray 0).symm
  have valid : Component state reference before := by
    refine ⟨by rw [shape]; exact word,?_⟩
    intro index entry found
    simpa only [MarkedTree.gapArray,holes] using represented.2 index entry found
  have actual : Rotations initial.erase before.erase count := by
    simpa only [before,markedGraft_erase,MarkedTree.graft_gapArray] using rotations_graft run initial.gapArray 0
  exact ⟨before,shape,valid,(SearchRotationBridge.rotations_inorder actual).trans (congrArg inorder physical)⟩

/-- A prescribed actual leaf switch lifts to the shared physical BST,
including the original component inventory. Its real sum-log potential
changes by exactly the change in the selected auxiliary. -/
 theorem embed_leaf_execution {state : State} {reference : RawTree Nat} {pivot : Nat}
    {address : Key} {spine : Spine Nat}
    (path : Path state reference address spine (.node .empty pivot .empty))
    (unique : reference.inorder.Nodup) {before : MarkedTree Nat}
    (represented : Component state reference before)
    {target : RawTree Nat} {rotations : Nat}
    (run : ClassicalSwitch.Execution pivot .empty (state address) spine.lower spine.upper
      before.skeleton target .empty rotations)
    (sameWord : target.inorder = before.skeleton.inorder) :
    ∃ (main : MarkedTree Nat) (trees next : List (RawTree Nat)) (work : Nat),
      main.skeleton = target ∧
      Component (toggle state address) reference main ∧
      Core state reference before.erase trees ∧
      Core (toggle state address) reference main.erase next ∧
      Switch state reference address before.erase main.erase rotations work ∧
      forestRank next+potential before.skeleton = forestRank trees+potential target := by
  obtain ⟨foreign,foreignRep,attached⟩ := represented.incoming path
  have emptyForeign : Component (restrict state (address++[!(state address)])) .empty foreign := by
    simpa only [ite_self] using foreignRep
  have foreignEq := emptyForeign.empty_marked
  have foreignSkeleton : foreign.skeleton = .empty := by rw [foreignEq]; rfl
  have attached' : foreign.erase = before.gapArray (incomingGapIndex (state address) spine.lower .empty) := by
    simpa only [tail,preferred,ite_self] using attached
  obtain ⟨main,old,mainSkeleton,oldSkeleton,actual,_,partition⟩ :=
    execution_repartition run before foreign rfl foreignSkeleton attached'
  have samePreferred := (leaf_toggle_partition state reference address pivot path.referenceAt).1
  have mainWord : main.skeleton.inorder = (preferred (toggle state address) reference).inorder := by
    rw [mainSkeleton,sameWord,represented.1,samePreferred]
  have oldWord : old.skeleton.inorder =
      (tail (restrict state address) (state address) (.node .empty pivot .empty)).inorder := by
    simp only [oldSkeleton,tail,preferred,ite_self]
  obtain ⟨mainRep,oldRep⟩ := repartition_components path represented foreignRep mainWord oldWord partition
  have oldEmpty : old.skeleton = .empty := oldSkeleton
  have execution : ClassicalSwitch.Execution pivot foreign.skeleton (state address) spine.lower spine.upper
      before.skeleton main.skeleton old.skeleton rotations := by
    simpa only [foreignSkeleton,mainSkeleton,oldSkeleton] using run
  have trace : CommonForest.SplayTrace [before.skeleton,foreign.skeleton]
      (eventWord reference state address) [main.skeleton,old.skeleton]
      (rotations+2+2*spine.lower.count+2*spine.upper.count) := by
    simpa only [eventWord,path.referenceAt,path.componentSpine,tail,preferred,ite_self,
      foreignSkeleton,oldSkeleton] using execution.trace
  have switch := Switch.root path represented foreignRep mainRep oldRep attached execution partition actual trace
  obtain ⟨trees,inventory⟩ := represented.realizes.inventory
  obtain ⟨next,remainder,nextInventory,previousOrder,nextOrder⟩ :=
    repartition_inventory path unique represented foreignRep mainRep oldRep partition inventory
  have previousSum := forestRank_perm previousOrder
  have nextSum := forestRank_perm nextOrder
  simp only [forestRank_append,forestRank_rootPart,foreignSkeleton,oldSkeleton,potential,
    add_zero,mainSkeleton] at previousSum nextSum
  exact ⟨main,trees,next,_,mainSkeleton,mainRep,inventory,nextInventory,switch,by linarith⟩

end MultiSplay.Obstructions.Classical
