import ChaCha.Paper20261030.SplayAuxiliaryGlobalPortReferences
import ChaCha.Paper20261030.SplayAuxiliaryAdapter
import ChaCha.Paper20261030.SplayAuxiliaryInventory

/-!
# Persistent inventories attached to an ordered list of source ports

Addresses are unnecessary after a preferred hole has been matched with
its exact source reference. This interface splits and concatenates the
existing descendant inventories while retaining their actual BST shapes.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ColoredStorage
open MultiSplay.EndpointEncoding MultiSplay.ClassicalSwitch
open MultiSplay.Global MultiSplay.Global.Preferred
open ChaCha.MTR.Pointer (MarkedTree)

variable {α ρ κ : Type*}

inductive PortInventory (key : ρ → κ) (right : ρ → Bool) :
    List (Source α ρ) → List (RawTree κ) → List (RawTree κ) → Prop
  | nil : PortInventory key right [] [] []
  | cons {reference : Source α ρ} {physical : RawTree κ}
      {references : List (Source α ρ)} {physicals first rest : List (RawTree κ)}
      (head : Core (referenceState right reference) (referenceCuts key reference) physical first)
      (tail : PortInventory key right references physicals rest) :
      PortInventory key right (reference::references) (physical::physicals) (first++rest)

namespace PortInventory

theorem length {key : ρ → κ} {right : ρ → Bool} {references : List (Source α ρ)}
    {physical trees : List (RawTree κ)} (inventory : PortInventory key right references physical trees) :
    references.length = physical.length := by
  induction inventory with
  | nil => rfl
  | cons first rest ih => simp only [List.length_cons,ih]

theorem append {key : ρ → κ} {right : ρ → Bool} {first rest : List (Source α ρ)}
    {firstPhysical restPhysical firstTrees restTrees : List (RawTree κ)}
    (before : PortInventory key right first firstPhysical firstTrees)
    (after : PortInventory key right rest restPhysical restTrees) :
    PortInventory key right (first++rest) (firstPhysical++restPhysical) (firstTrees++restTrees) := by
  induction before with
  | nil => simpa only [List.nil_append] using after
  | cons head tail ih => simpa only [List.cons_append,List.append_assoc] using PortInventory.cons head ih

theorem split {key : ρ → κ} {right : ρ → Bool} {first rest : List (Source α ρ)}
    {firstPhysical restPhysical trees : List (RawTree κ)}
    (inventory : PortInventory key right (first++rest) (firstPhysical++restPhysical) trees)
    (sameLength : first.length = firstPhysical.length) :
    ∃ firstTrees restTrees, trees = firstTrees++restTrees ∧
      PortInventory key right first firstPhysical firstTrees ∧
      PortInventory key right rest restPhysical restTrees := by
  induction first generalizing firstPhysical trees with
  | nil =>
      have empty := List.eq_nil_of_length_eq_zero sameLength.symm
      subst firstPhysical
      exact ⟨[],trees,rfl,.nil,inventory⟩
  | cons reference first ih =>
      cases firstPhysical with
      | nil => simp at sameLength
      | cons physical firstPhysical =>
          cases inventory with
          | cons head tail =>
              obtain ⟨front,back,rfl,firstInventory,lastInventory⟩ := ih tail (by simpa using sameLength)
              exact ⟨_,back,(List.append_assoc _ _ _).symm,.cons head firstInventory,lastInventory⟩

theorem of_branches {key : ρ → κ} {right : ρ → Bool} {state : State}
    {entries : List (ChaCha.Primary.Key × Source α ρ)} {physical trees : List (RawTree κ)}
    (states : ∀ entry ∈ entries, restrict state entry.1 = referenceState right entry.2)
    (branches : Branches state (entries.map (fun e => (e.1,referenceCuts key e.2))) physical trees) :
    PortInventory key right (entries.map Prod.snd) physical trees := by
  induction entries generalizing physical trees with
  | nil => cases branches; exact .nil
  | cons entry entries ih =>
      cases branches with
      | cons head tail =>
          refine .cons ?_ (ih (fun e member => states e (by simp [member])) tail)
          rw [states entry (by simp)] at head
          exact head

theorem to_branches {key : ρ → κ} {right : ρ → Bool} {state : State}
    {entries : List (ChaCha.Primary.Key × Source α ρ)} {physical trees : List (RawTree κ)}
    (states : ∀ entry ∈ entries, restrict state entry.1 = referenceState right entry.2)
    (inventory : PortInventory key right (entries.map Prod.snd) physical trees) :
    Branches state (entries.map (fun e => (e.1,referenceCuts key e.2))) physical trees := by
  induction entries generalizing physical trees with
  | nil => cases inventory; exact .nil state
  | cons entry entries ih =>
      cases inventory with
      | cons head tail =>
          refine .cons ?_ (ih (fun e member => states e (by simp [member])) tail)
          rw [states entry (by simp)]
          exact head

end PortInventory

theorem markedSource_holes (component : RawComponent α κ) :
    (markedSource component.core component.ports).holes =
      component.portWord.map (referenceCuts id) := by
  apply List.ext_getElem
  · simp only [MarkedTree.holes_length,markedSource_skeleton,List.length_map,RawComponent.portWord_length]
  · intro index before after
    have bound : index ≤ component.core.size := by
      rw [MarkedTree.holes_length,markedSource_skeleton] at before
      omega
    have value := markedSource_gapArray component.core component.ports index bound
    simp only [MarkedTree.gapArray,List.getElem?_eq_getElem before,Option.getD_some] at value
    simpa only [RawComponent.portWord,List.getElem_map,List.getElem_range] using value

theorem component_inventory_expose {key : ρ → κ} {right : ρ → Bool} {reference : Source α ρ}
    {component : RawComponent α κ} {trees : List (RawTree κ)}
    (unique : (referenceCuts key reference).inorder.Nodup)
    (represented : Decomposition.Represents key right reference component)
    (inventory : Core (referenceState right reference) (referenceCuts key reference)
      (referenceCuts id component.closed) trees) :
    ∃ descendants, trees = rootPart component.core ++ descendants ∧
      PortInventory key right (sourcePorts right reference)
        (component.portWord.map (referenceCuts id)) descendants := by
  have actual : Core (referenceState right reference) (referenceCuts key reference)
      (markedSource component.core component.ports).erase trees := by
    simpa only [markedSource_erase,RawComponent.closed] using inventory
  obtain ⟨descendants,same,children⟩ := actual.expose unique (represented_component represented)
  rw [← referenceEntries_raw key right reference,markedSource_holes] at children
  refine ⟨descendants,by simpa only [markedSource_skeleton] using same,?_⟩
  exact PortInventory.of_branches
    (fun entry member => (referenceEntries_state right reference member).symm) children

theorem component_inventory_of_ports {key : ρ → κ} {right : ρ → Bool} {reference : Source α ρ}
    {component : RawComponent α κ} {descendants : List (RawTree κ)}
    (represented : Decomposition.Represents key right reference component)
    (children : PortInventory key right (sourcePorts right reference)
      (component.portWord.map (referenceCuts id)) descendants) :
    Core (referenceState right reference) (referenceCuts key reference)
      (referenceCuts id component.closed) (rootPart component.core ++ descendants) := by
  have branches := PortInventory.to_branches (entries := referenceEntries right reference)
    (fun entry member => (referenceEntries_state right reference member).symm) children
  rw [referenceEntries_raw,← markedSource_holes] at branches
  simpa only [markedSource_erase,RawComponent.closed,markedSource_skeleton] using
    Core.of_branches (represented_component represented).1 branches

end ChaCha.Paper20261030.SplayAuxiliary
