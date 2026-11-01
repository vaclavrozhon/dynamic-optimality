import MultiSplay.GlobalPreferredAttached
import MultiSplay.ClassicalSwitchAccountingHoles

/-!
# The nonempty physical component inventory

The recursive physical representation has one terminal empty hole per
preferred path. Those holes are not extra components. `Core` records only
nonempty component skeletons; a completed analytical forest supplies its
indistinguishable empty slots separately. No component is reinitialized.
-/

namespace MultiSplay.Global.Preferred

open DynamicOptimality (RawTree)
open TangoSquared.MTR
open Pointer (MarkedTree)
open TangoSquared.Primary (Key)
open EndpointEncoding ClassicalSwitch

variable {α : Type*}

/-- On distinct keys, the physical tree and the component's inorder domain
determine its marking, including its actual auxiliary shape. -/
theorem marked_inorder_ext {before after : MarkedTree α}
    (unique : before.skeleton.inorder.Nodup)
    (keys : before.skeleton.inorder = after.skeleton.inorder)
    (physical : before.erase = after.erase) : before = after := by
  induction before generalizing after with
  | hole tree =>
      cases after with
      | hole other => simpa only [MarkedTree.erase, MarkedTree.hole.injEq] using physical
      | node left key right => simp [MarkedTree.skeleton, Tree.inorder] at keys
  | node left key right ihLeft ihRight =>
      cases after with
      | hole tree => simp [MarkedTree.skeleton, Tree.inorder] at keys
      | node left' key' right' =>
          simp only [MarkedTree.erase, Tree.node.injEq] at physical
          obtain ⟨leftPhysical, rfl, rightPhysical⟩ := physical
          have parts := Auxiliary.nodup_node unique
          have split := (List.append_cons_inj_of_notMem parts.2.2.1 parts.2.2.2.1).mp
            (by simpa only [MarkedTree.skeleton, Tree.inorder, List.append_assoc,
              List.singleton_append] using keys)
          rw [ihLeft parts.1 split.1 leftPhysical,
            ihRight parts.2.1 split.2.2 rightPhysical]

theorem Component.marked_unique {state : State} {reference : RawTree α}
    {before after : MarkedTree α} (unique : reference.inorder.Nodup)
    (first : Component state reference before) (second : Component state reference after)
    (physical : before.erase = after.erase) : before = after := by
  apply marked_inorder_ext _ (first.1.trans second.1.symm) physical
  rw [first.1]
  exact unique.sublist (preferred_sublist state reference)

theorem Realizes.empty_eq {state : State} {physical : RawTree α}
    (represented : Realizes state .empty physical) : physical = .empty := by
  generalize referenceEq : (Tree.empty : RawTree α) = reference at represented
  induction represented with
  | empty => rfl
  | component actual keys holes ih =>
      cases referenceEq
      cases actual with
      | node left key right => simp [MarkedTree.skeleton, preferred, Tree.inorder] at keys
      | hole tree =>
          exact ih 0 ([],.empty) rfl rfl

/- One actual component, or no component when its reference subtree is
empty, followed recursively by all its nonempty descendant components. -/
mutual
  inductive Core : State → RawTree α → RawTree α → List (RawTree α) → Prop
    | empty (state : State) : Core state .empty .empty []
    | component {state : State} {reference : RawTree α} (actual : MarkedTree α)
        {descendants : List (RawTree α)} (nonempty : reference ≠ .empty)
        (keys : actual.skeleton.inorder = (preferred state reference).inorder)
        (children : Branches state (preferredHoles state reference) actual.holes descendants) :
        Core state reference actual.erase (actual.skeleton :: descendants)
  inductive Branches : State → List (Key × RawTree α) → List (RawTree α) →
      List (RawTree α) → Prop
    | nil (state : State) : Branches state [] [] []
    | cons {state : State} {entry : Key × RawTree α} {physical : RawTree α}
        {entries : List (Key × RawTree α)} {physicals head rest : List (RawTree α)}
        (child : Core (restrict state entry.1) entry.2 physical head)
        (children : Branches state entries physicals rest) :
        Branches state (entry :: entries) (physical :: physicals) (head ++ rest)
end

theorem Branches.length {state : State} {entries : List (Key × RawTree α)}
    {physical trees : List (RawTree α)} (children : Branches state entries physical trees) :
    entries.length = physical.length := by
  induction entries generalizing physical trees with
  | nil => cases children; rfl
  | cons entry entries ih =>
      cases children with
      | cons child children => simp only [List.length_cons, ih children]

theorem Core.realizes {state : State} {reference physical : RawTree α}
    {trees : List (RawTree α)} (inventory : Core state reference physical trees) :
    Realizes state reference physical := by
  induction inventory using Core.rec
      (motive_2 := fun state entries physical _ _ => Attached state entries physical) with
  | empty state => exact .empty state
  | component actual nonempty keys children attached =>
      exact (component_of_attached keys attached).realizes
  | nil => exact .nil
  | cons child children head rest => exact .cons head rest

theorem Branches.attached {state : State} {entries : List (Key × RawTree α)}
    {physical trees : List (RawTree α)} (children : Branches state entries physical trees) :
    Attached state entries physical := by
  induction entries generalizing physical trees with
  | nil => cases children; exact .nil
  | cons entry entries ih =>
      cases children with
      | cons child children => exact .cons child.realizes (ih children)

theorem Branches.append {state : State} {entries entries' : List (Key × RawTree α)}
    {physical physical' trees trees' : List (RawTree α)}
    (first : Branches state entries physical trees)
    (second : Branches state entries' physical' trees') :
    Branches state (entries ++ entries') (physical ++ physical') (trees ++ trees') := by
  induction entries generalizing physical trees with
  | nil => cases first; simpa only [List.nil_append] using second
  | cons entry entries ih =>
      cases first with
      | cons child children =>
          simpa only [List.cons_append, List.append_assoc] using Branches.cons child (ih children)

theorem Branches.split {state : State} {first rest : List (Key × RawTree α)}
    {firstPhysical restPhysical trees : List (RawTree α)}
    (children : Branches state (first ++ rest) (firstPhysical ++ restPhysical) trees)
    (length : first.length = firstPhysical.length) :
    ∃ front back, trees = front ++ back ∧
      Branches state first firstPhysical front ∧ Branches state rest restPhysical back := by
  induction first generalizing firstPhysical trees with
  | nil =>
      have : firstPhysical = [] := List.eq_nil_of_length_eq_zero length.symm
      subst firstPhysical
      exact ⟨[], trees, rfl, .nil state, children⟩
  | cons entry first ih =>
      cases firstPhysical with
      | nil => simp at length
      | cons physical firstPhysical =>
          cases children with
          | cons child children =>
              obtain ⟨front,back,rfl,frontChildren,backChildren⟩ := ih children (by simpa using length)
              exact ⟨_,back,(List.append_assoc _ _ _).symm,.cons child frontChildren,backChildren⟩

theorem Branches.state_congr {before after : State} {entries : List (Key × RawTree α)}
    {physical trees : List (RawTree α)} (children : Branches before entries physical trees)
    (same : ∀ entry ∈ entries, restrict after entry.1 = restrict before entry.1) :
    Branches after entries physical trees := by
  induction entries generalizing physical trees with
  | nil => cases children; exact .nil after
  | cons entry entries ih =>
      cases children with
      | cons child children =>
          refine .cons ?_ (ih children fun entry member => same entry (by simp [member]))
          rw [same entry (by simp)]
          exact child

theorem Branches.prefix {state : State} (address : Key)
    {entries : List (Key × RawTree α)} {physical trees : List (RawTree α)}
    (children : Branches (restrict state address) entries physical trees) :
    Branches state (prefixHoles address entries) physical trees := by
  induction entries generalizing physical trees with
  | nil => cases children; exact .nil state
  | cons entry entries ih =>
      cases children with
      | cons child children =>
          apply Branches.cons _ (ih children)
          simpa only [restrict_append] using child

theorem Branches.unprefix {state : State} (address : Key)
    {entries : List (Key × RawTree α)} {physical trees : List (RawTree α)}
    (children : Branches state (prefixHoles address entries) physical trees) :
    Branches (restrict state address) entries physical trees := by
  induction entries generalizing physical trees with
  | nil => cases children; exact .nil _
  | cons entry entries ih =>
      cases children with
      | cons child children =>
          exact .cons (by simpa only [restrict_append] using child) (ih children)

end MultiSplay.Global.Preferred
