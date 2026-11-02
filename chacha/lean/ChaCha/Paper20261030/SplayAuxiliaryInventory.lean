import ChaCha.Paper20261030.SplayAuxiliaryReferenceCore

/-!
# Size and initial potential of the persistent secondary forest

Every separator belongs to exactly one physical auxiliary. The inventory
therefore has the same total size as the physical tree, and each auxiliary
contains at most a root-to-leaf reference path. These structural facts bound
the initial potential without resetting any component later.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ChaCha.MTR
open MultiSplay EndpointEncoding ClassicalSwitch Global.Preferred
open Pointer (MarkedTree)
open ColoredStorage

variable {α ρ κ : Type*}

def rawHeight : RawTree κ → Nat
  | .empty => 0
  | .node l _ r => max (rawHeight l) (rawHeight r)+1

@[simp] theorem rawHeight_source (key : ρ → κ) (reference : Source α ρ) :
    rawHeight (referenceCuts key reference) = reference.shape.height := by
  induction reference <;> simp_all [referenceCuts,rawHeight,Source.shape,RouterProjection.Router.height]

theorem preferred_rawHeight (state : State) (reference : RawTree κ) :
    (preferred state reference).size ≤ rawHeight reference := by
  induction reference generalizing state with
  | empty => rfl
  | node l key r ihl ihr =>
      have left := ihl (below state false)
      have right := ihr (below state true)
      cases direction : state [] <;>
        simp only [preferred,direction,Bool.false_eq_true,if_false,if_true,Tree.size,rawHeight] <;> omega

theorem preferredHoles_height (state : State) (reference : RawTree κ)
    {entry : ChaCha.Primary.Key × RawTree κ} (member : entry ∈ preferredHoles state reference) :
    rawHeight entry.2 ≤ rawHeight reference := by
  induction reference generalizing state entry with
  | empty => simp only [preferredHoles,List.mem_singleton] at member; subst entry; rfl
  | node l key r ihl ihr =>
      cases direction : state [] with
      | false =>
          simp only [preferredHoles,direction,Bool.false_eq_true,if_false,List.mem_append,
            List.mem_singleton] at member
          rcases member with child | rfl
          · obtain ⟨e,present,rfl⟩ := List.mem_map.mp child
            have bounded := ihl (below state false) present
            simp only [rawHeight]
            omega
          · simp only [rawHeight]; omega
      | true =>
          simp only [preferredHoles,direction,if_true,List.mem_cons] at member
          rcases member with rfl | child
          · simp only [rawHeight]; omega
          · obtain ⟨e,present,rfl⟩ := List.mem_map.mp child
            have bounded := ihr (below state true) present
            simp only [rawHeight]
            omega

theorem marked_size (actual : MarkedTree κ) :
    actual.erase.size = actual.skeleton.size+forestSize actual.holes := by
  induction actual with
  | hole tree => simp [MarkedTree.erase,MarkedTree.skeleton,MarkedTree.holes,forestSize,Tree.size]
  | node l key r ihl ihr =>
      simp only [MarkedTree.erase,MarkedTree.skeleton,MarkedTree.holes,Tree.size,
        forestSize,List.map_append,List.sum_append] at *
      omega

theorem core_mass {state : State} {reference physical : RawTree κ} {trees : List (RawTree κ)}
    (inventory : Core state reference physical trees) : forestSize trees = physical.size := by
  induction inventory using Core.rec
      (motive_2 := fun _ _ physical trees _ => forestSize trees = forestSize physical) with
  | empty => rfl
  | component actual nonempty keys children mass =>
      simp only [forestSize,List.map_cons,List.sum_cons]
      simpa only [forestSize] using (congrArg (actual.skeleton.size + ·) mass).trans (marked_size actual).symm
  | nil => rfl
  | cons child children head rest =>
      simp only [forestSize,List.map_append,List.sum_append,List.map_cons,List.sum_cons] at *
      omega

theorem core_height {state : State} {reference physical : RawTree κ} {trees : List (RawTree κ)}
    (inventory : Core state reference physical trees) :
    ∀ tree ∈ trees, tree.size ≤ rawHeight reference := by
  induction inventory using Core.rec
      (motive_2 := fun _ entries _ trees _ =>
        ∀ tree ∈ trees, ∃ entry ∈ entries, tree.size ≤ rawHeight entry.2) with
  | empty => simp
  | component actual nonempty keys children bounded =>
      intro tree member
      rcases List.mem_cons.mp member with rfl | tail
      · have size := congrArg List.length keys
        simp only [Tree.length_inorder] at size
        rw [size]
        exact preferred_rawHeight _ _
      · obtain ⟨entry,present,bound⟩ := bounded tree tail
        exact bound.trans (preferredHoles_height _ _ present)
  | nil => rename_i tree member; simp at member
  | cons child children head rest =>
      rename_i tree member
      rcases List.mem_append.mp member with first | last
      · exact ⟨_,by simp,head tree first⟩
      · obtain ⟨entry,present,bound⟩ := rest tree last
        exact ⟨entry,by simp [present],bound⟩

theorem forestPotential_size_bound (trees : List (RawTree κ)) (capacity : Nat)
    (bounded : ∀ tree ∈ trees, tree.size ≤ capacity) :
    forestPotential trees ≤ forestSize trees*Nat.log 2 capacity := by
  induction trees with
  | nil => simp [forestPotential,forestSize]
  | cons tree tail ih =>
      have first := potential_le tree capacity (bounded tree (by simp))
      have rest := ih (by intro t member; exact bounded t (by simp [member]))
      simp only [forestPotential,forestSize,List.map_cons,List.sum_cons] at *
      nlinarith

theorem core_potential_bound {state : State} {reference physical : RawTree κ}
    {trees : List (RawTree κ)} (inventory : Core state reference physical trees) :
    forestPotential trees ≤ physical.size*Nat.log 2 (rawHeight reference) := by
  have bound := forestPotential_size_bound trees (rawHeight reference) (core_height inventory)
  rwa [core_mass inventory] at bound

end ChaCha.Paper20261030.SplayAuxiliary
