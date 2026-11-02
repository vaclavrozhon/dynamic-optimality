import MultiSplay.GlobalPreferredRepresentation
import MultiSplay.ClassicalSwitchMarkedUpdate
import Mathlib.Data.List.Forall2

/-! # Ordered attachment relations and component interfaces -/

namespace MultiSplay.Global.Preferred

open DynamicOptimality (RawTree)
open ChaCha.MTR
open Pointer (MarkedTree)
open ChaCha.Primary (Key)
open EndpointEncoding ClassicalSwitch

variable {α : Type*}

def Attached (state : State) (entries : List (Key × RawTree α)) (physical : List (RawTree α)) : Prop :=
  List.Forall₂ (fun entry tree => Realizes (restrict state entry.1) entry.2 tree) entries physical

theorem Attached.lookup {state : State} {entries : List (Key × RawTree α)}
    {physical : List (RawTree α)} (attached : Attached state entries physical)
    (index : Nat) (entry : Key × RawTree α) (found : entries[index]? = some entry) :
    Realizes (restrict state entry.1) entry.2 (physical[index]?.getD .empty) := by
  induction attached generalizing index with
  | nil => simp at found
  | @cons first tree entries physical head tail ih =>
      cases index with
      | zero => cases Option.some.inj found; exact head
      | succ index => exact ih index found

theorem Component.attached {state : State} {reference : RawTree α} {actual : MarkedTree α}
    (represented : Component state reference actual) :
    Attached state (preferredHoles state reference) actual.holes := by
  have size : actual.skeleton.size = (preferred state reference).size := by
    simpa only [Tree.length_inorder] using congrArg List.length represented.1
  apply List.forall₂_of_length_eq_of_get
  · rw [preferredHoles_length, MarkedTree.holes_length, size]
  · intro index beforeBound afterBound
    have found := represented.2 index ((preferredHoles state reference).get ⟨index,beforeBound⟩)
      (by simp)
    simpa [MarkedTree.gapArray, List.getElem?_eq_getElem afterBound] using found

theorem component_of_attached {state : State} {reference : RawTree α} {actual : MarkedTree α}
    (keys : actual.skeleton.inorder = (preferred state reference).inorder)
    (attached : Attached state (preferredHoles state reference) actual.holes) :
    Component state reference actual :=
  ⟨keys, attached.lookup⟩

theorem Attached.append {state : State} {first rest : List (Key × RawTree α)}
    {firstPhysical restPhysical : List (RawTree α)}
    (left : Attached state first firstPhysical) (right : Attached state rest restPhysical) :
    Attached state (first ++ rest) (firstPhysical ++ restPhysical) := List.rel_append left right

/-- Equal prefix lengths identify the same cut in two attached lists. -/
theorem Attached.split {state : State} {first rest : List (Key × RawTree α)}
    {firstPhysical restPhysical : List (RawTree α)}
    (attached : Attached state (first ++ rest) (firstPhysical ++ restPhysical))
    (length : first.length = firstPhysical.length) :
    Attached state first firstPhysical ∧ Attached state rest restPhysical := by
  constructor
  · have front := List.forall₂_take first.length attached
    simp only [List.take_left] at front
    simpa only [Attached, length, List.take_left] using front
  · have back := List.forall₂_drop first.length attached
    simp only [List.drop_left] at back
    simpa only [Attached, length, List.drop_left] using back

/-- Reinterpret a list under a preference state unchanged inside all its
annotated reference subtrees. -/
theorem Attached.state_congr {before after : State} {entries : List (Key × RawTree α)}
    {physical : List (RawTree α)} (attached : Attached before entries physical)
    (same : ∀ entry ∈ entries, restrict after entry.1 = restrict before entry.1) :
    Attached after entries physical := by
  induction attached with
  | nil => exact .nil
  | @cons entry tree entries physical head tail ih =>
      refine .cons ?_ (ih fun child member => same child (by simp [member]))
      rw [same entry (by simp)]
      exact head

/-- A child's local hole addresses become actual global hole addresses by
prefixing its reference location. -/
theorem Attached.prefix {state : State} (address : Key)
    {entries : List (Key × RawTree α)} {physical : List (RawTree α)}
    (attached : Attached (restrict state address) entries physical) :
    Attached state (prefixHoles address entries) physical := by
  simpa only [Attached, prefixHoles, List.forall₂_map_left_iff, restrict_append] using attached

theorem Attached.unprefix {state : State} (address : Key)
    {entries : List (Key × RawTree α)} {physical : List (RawTree α)}
    (attached : Attached state (prefixHoles address entries) physical) :
    Attached (restrict state address) entries physical := by
  simpa only [Attached, prefixHoles, List.forall₂_map_left_iff, restrict_append] using attached

end MultiSplay.Global.Preferred
