import ChaCha.Paper20261030.SplayAuxiliarySwitch
import ChaCha.Paper20261030.SplayAuxiliaryForest
import MultiSplay.GlobalPreferredInventoryRoot

/-!
# Actual preferred-path repair with a persistent global inventory

The root preferred component can have any ordinary BST shape. The existing
classical switch supplies its actual pivot and guard splays and ordinary
rotations of the physically attached tree. Combining that construction with
the access lemma charges the complete before/after inventory. Descendant
components are retained and their potential is never restarted.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open DynamicOptimality.SearchRotation
open ChaCha.MTR
open MultiSplay EndpointEncoding ClassicalSwitch Global.Preferred
open Pointer (MarkedTree)

variable {α : Type*}

@[simp] theorem forestPotential_rootPart (tree : RawTree α) :
    forestPotential (rootPart tree) = potential tree := by
  cases tree <;> simp [rootPart,forestPotential,potential]

/-- Total physical root-component repair, with its own actual splay
certificate and global amortized bound. Capacity is a structural size bound,
not an assumed implementation budget. -/
theorem preferred_root_repair {state : State} {reference left right : RawTree α} {pivot : α}
    {address : ChaCha.Primary.Key} {spine : Spine α}
    (path : Path state reference address spine (.node left pivot right))
    (unique : reference.inorder.Nodup) {before : MarkedTree α}
    (represented : Component state reference before)
    {trees : List (RawTree α)} (inventory : Core state reference before.erase trees)
    {capacity : Nat} (fits : (preferred state reference).size ≤ capacity)
    (nextFits : (preferred (toggle state address) reference).size ≤ capacity) :
    ∃ main old foreign : MarkedTree α, ∃ next : List (RawTree α), ∃ rotations : Nat,
      Component (toggle state address) reference main ∧
      Core (toggle state address) reference main.erase next ∧
      Rotations before.erase main.erase rotations ∧
      Execution pivot foreign.skeleton (state address) spine.lower spine.upper
        before.skeleton main.skeleton old.skeleton rotations ∧
      Switch state reference address before.erase main.erase rotations
        (rotations+2+2*spine.lower.count+2*spine.upper.count) ∧
      rotations+2*forestPotential next ≤
        2*forestPotential trees+24*Nat.log 2 capacity+3 := by
  obtain ⟨main,old,foreign,rotations,mainRep,foreignRep,oldRep,attached,physical,
    execution,events,root,parked,partition⟩ := root_execution path unique represented
  obtain ⟨next,remainder,nextInventory,beforeOrder,afterOrder⟩ :=
    repartition_inventory path unique represented foreignRep mainRep oldRep partition inventory
  have skeletonUnique : before.skeleton.inorder.Nodup := by
    rw [represented.1]
    exact unique.sublist (preferred_sublist state reference)
  have skeletonSize : before.skeleton.size = (preferred state reference).size := by
    simpa only [Tree.length_inorder] using congrArg List.length represented.1
  have mainSize : main.skeleton.size = (preferred (toggle state address) reference).size := by
    simpa only [Tree.length_inorder] using congrArg List.length mainRep.1
  have amortized := switch_amortized (capacity := capacity) execution skeletonUnique
    (by rw [skeletonSize]; exact fits) (by rw [mainSize]; exact nextFits)
  have ordinary : Switch state reference address before.erase main.erase rotations
      (rotations+2+2*spine.lower.count+2*spine.upper.count) :=
    .root path represented foreignRep mainRep oldRep attached execution partition physical events
  refine ⟨main,old,foreign,next,rotations,mainRep,nextInventory,physical,execution,ordinary,?_⟩
  rw [forestPotential_perm beforeOrder,forestPotential_perm afterOrder]
  simp only [forestPotential_append,forestPotential_rootPart]
  omega

end ChaCha.Paper20261030.SplayAuxiliary
