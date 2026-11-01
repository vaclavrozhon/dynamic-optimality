import MultiSplay.GlobalPreferredInventory

/-! # Exposing and constructing the persistent component inventory -/

namespace MultiSplay.Global.Preferred

open DynamicOptimality (RawTree)
open TangoSquared.MTR
open Pointer (MarkedTree)
open TangoSquared.Primary (Key)
open EndpointEncoding ClassicalSwitch

variable {α : Type*}

/-- Empty analytical slots carry no nonempty component. -/
def rootPart : RawTree α → List (RawTree α)
  | .empty => []
  | .node left key right => [.node left key right]

theorem rootPart_nonempty {tree : RawTree α} (nonempty : tree ≠ .empty) :
    rootPart tree = [tree] := by cases tree <;> simp_all [rootPart]

theorem Component.empty_marked {state : State} {actual : MarkedTree α}
    (represented : Component state .empty actual) : actual = .hole .empty := by
  have physical := represented.realizes.empty_eq
  cases actual with
  | hole tree => simpa only [MarkedTree.erase, MarkedTree.hole.injEq] using physical
  | node left key right => simp [MarkedTree.erase] at physical

theorem Core.empty_trees {state : State} {physical : RawTree α} {trees : List (RawTree α)}
    (inventory : Core state .empty physical trees) : trees = [] ∧ physical = .empty := by
  cases inventory with
  | empty => exact ⟨rfl,rfl⟩
  | component _ nonempty => exact False.elim (nonempty rfl)

theorem Core.all_nonempty {state : State} {reference physical : RawTree α}
    {trees : List (RawTree α)} (inventory : Core state reference physical trees) :
    ∀ tree ∈ trees, tree ≠ .empty := by
  induction inventory using Core.rec
      (motive_2 := fun _ _ _ trees _ => ∀ tree ∈ trees, tree ≠ .empty) with
  | empty => simp
  | @component state reference actual descendants nonempty keys children ih =>
      intro tree member
      rcases List.mem_cons.mp member with rfl | member
      · intro absent
        rw [absent] at keys
        cases reference with
        | empty => exact nonempty rfl
        | node left key right =>
            cases direction : state [] <;> simp [preferred, direction, Tree.inorder] at keys
      · exact ih tree member
  | nil => simp_all
  | cons child children head rest =>
      rename_i tree member
      rcases List.mem_append.mp member with member | member
      · exact head tree member
      · exact rest tree member

/-- Expose an inventory using any valid marking of the same physical
component. Uniqueness of reference keys removes dependence on a chosen
representation proof. -/
theorem Core.expose {state : State} {reference : RawTree α}
    {actual : MarkedTree α} {trees : List (RawTree α)}
    (unique : reference.inorder.Nodup) (inventory : Core state reference actual.erase trees)
    (represented : Component state reference actual) :
    ∃ descendants, trees = rootPart actual.skeleton ++ descendants ∧
      Branches state (preferredHoles state reference) actual.holes descendants := by
  generalize physicalEq : actual.erase = physical at inventory
  cases inventory with
  | empty state =>
      have same := represented.empty_marked
      subst actual
      refine ⟨[],rfl,?_⟩
      change Branches state [([], .empty)] [.empty] []
      exact .cons (entry := ([], .empty)) (.empty state) (.nil state)
  | component other nonempty keys children =>
      have otherRep := component_of_attached keys children.attached
      have same := represented.marked_unique unique otherRep physicalEq
      subst other
      refine ⟨_,?_,children⟩
      rw [rootPart_nonempty]
      · rfl
      · intro absent
        rw [absent] at keys
        cases reference with
        | empty => exact nonempty rfl
        | node left key right =>
            cases direction : state [] <;> simp [preferred, direction, Tree.inorder] at keys

/-- Reassemble a component from its old descendant inventory. In the empty
case its single terminal hole contributes no analytical component. -/
theorem Core.of_branches {state : State} {reference : RawTree α}
    {actual : MarkedTree α} {descendants : List (RawTree α)}
    (keys : actual.skeleton.inorder = (preferred state reference).inorder)
    (children : Branches state (preferredHoles state reference) actual.holes descendants) :
    Core state reference actual.erase (rootPart actual.skeleton ++ descendants) := by
  by_cases nonempty : reference = .empty
  · subst reference
    have same := (component_of_attached keys children.attached).empty_marked
    subst actual
    cases children with
    | cons child rest =>
        obtain ⟨rfl,_⟩ := child.empty_trees
        cases rest
        exact .empty state
  · have skeletonNonempty : actual.skeleton ≠ .empty := by
      intro absent
      rw [absent] at keys
      cases reference with
      | empty => exact nonempty rfl
      | node left key right =>
          cases direction : state [] <;> simp [preferred, direction, Tree.inorder] at keys
    rw [rootPart_nonempty skeletonNonempty]
    exact .component actual nonempty keys children

theorem Branches.of_lookup {state : State} {entries : List (Key × RawTree α)}
    {physical : List (RawTree α)} (length : entries.length = physical.length)
    (children : ∀ (index : Nat) (entry : Key × RawTree α), entries[index]? = some entry →
      ∃ trees, Core (restrict state entry.1) entry.2 (physical[index]?.getD .empty) trees) :
    ∃ trees, Branches state entries physical trees := by
  induction entries generalizing physical with
  | nil =>
      have empty := List.eq_nil_of_length_eq_zero length.symm
      subst physical
      exact ⟨[],.nil state⟩
  | cons entry entries ih =>
      cases physical with
      | nil => simp at length
      | cons tree physical =>
          obtain ⟨head,headCore⟩ := children 0 entry rfl
          obtain ⟨rest,restCore⟩ := ih (by simpa using length)
            (fun index entry found => children (index+1) entry found)
          exact ⟨head ++ rest,.cons headCore restCore⟩

theorem Realizes.inventory {state : State} {reference physical : RawTree α}
    (represented : Realizes state reference physical) :
    ∃ trees, Core state reference physical trees := by
  induction represented with
  | empty state => exact ⟨[],.empty state⟩
  | component actual keys holes ih =>
      have component : Component _ _ actual := ⟨keys,holes⟩
      obtain ⟨descendants,children⟩ := Branches.of_lookup component.attached.length_eq ih
      exact ⟨_,Core.of_branches keys children⟩

end MultiSplay.Global.Preferred
