import MultiSplay.InterfacePlacement
import MultiSplay.InterfaceFramedTrace

/-!
# Recovering the passive frame from actual component placements

The frame is constructed by selecting exactly the unplaced global records.
It is not provided as an execution oracle. Separation says these records have
no active payloads or active growing creators; retired creators are unrestricted.
-/

namespace MultiSplay.InterfacePlacement

open Splay.Interface

variable {n m : Nat} {component : State n} {whole : State m}

def Placement.Separated (placement : Placement component whole) : Prop :=
  ∀ i : Fin whole.blocks.length, (∀ j, placement.id j ≠ i.val) →
    (∀ x ∈ (whole.blocks.get i).elements, ∀ old, x ≠ placement.element old) ∧
    ((whole.blocks.get i).mode = .growing → ∀ old, (whole.blocks.get i).creator ≠ placement.element old)

theorem Placement.id_bound (placement : Placement component whole) (i : Fin component.blocks.length) :
    placement.id i < whole.blocks.length := by
  obtain ⟨block, found, _⟩ := placement.lookup i
  exact (List.getElem?_eq_some_iff.mp found).1

def Placement.finId (placement : Placement component whole) (i : Fin component.blocks.length) : Fin whole.blocks.length :=
  ⟨placement.id i, placement.id_bound i⟩

theorem Placement.finId_injective (placement : Placement component whole) : Function.Injective placement.finId := by
  intro i j same
  exact placement.id_injective (congrArg Fin.val same)

def Placement.activeIds (placement : Placement component whole) : List (Fin whole.blocks.length) :=
  (List.finRange component.blocks.length).map placement.finId

@[simp] theorem Placement.mem_activeIds (placement : Placement component whole) (i : Fin whole.blocks.length) :
    i ∈ placement.activeIds ↔ ∃ j, placement.id j = i.val := by
  simp only [Placement.activeIds, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, same⟩
    exact ⟨j, congrArg Fin.val same⟩
  · rintro ⟨j, same⟩
    exact ⟨j, Fin.ext same⟩

noncomputable def Placement.foreignIds (placement : Placement component whole) : List (Fin whole.blocks.length) :=
  (List.finRange whole.blocks.length).filter (fun i => decide (i ∉ placement.activeIds))

@[simp] theorem Placement.mem_foreignIds (placement : Placement component whole) (i : Fin whole.blocks.length) :
    i ∈ placement.foreignIds ↔ ∀ j, placement.id j ≠ i.val := by
  simp [Placement.foreignIds]

theorem Placement.partition (placement : Placement component whole) :
    (placement.foreignIds ++ placement.activeIds).Perm (List.finRange whole.blocks.length) := by
  classical
  have own : ((List.finRange whole.blocks.length).filter (fun i => !decide (i ∉ placement.activeIds))).Perm placement.activeIds := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) ((List.nodup_finRange _).map placement.finId_injective)).mpr
    intro i
    simp only [List.mem_filter, List.mem_finRange, true_and]
    change (!decide (i ∉ placement.activeIds)) = true ↔ i ∈ placement.activeIds
    by_cases inside : i ∈ placement.activeIds <;> simp [inside]
  exact (List.Perm.append_left placement.foreignIds own.symm).trans (List.filter_append_perm _ _)

noncomputable def Placement.frame (placement : Placement component whole) : State m :=
  ⟨placement.foreignIds.map whole.blocks.get, whole.value⟩

theorem Placement.frame_sublist (placement : Placement component whole) : placement.frame.blocks.Sublist whole.blocks := by
  have sub := (List.filter_sublist (l := List.finRange whole.blocks.length)
    (p := fun i => decide (i ∉ placement.activeIds))).map whole.blocks.get
  simpa only [Placement.frame, Placement.foreignIds, List.map_get_finRange] using sub

theorem Placement.frame_valid (placement : Placement component whole) {params : Parameters} (valid : whole.Valid params) :
    placement.frame.Valid params := by
  refine ⟨valid.1.sublist (placement.frame_sublist.flatMap Block.elements), valid.2.1, ?_⟩
  intro creator
  exact le_trans (placement.frame_sublist.filter (fun block => decide (block.mode = .growing ∧ block.creator = creator))).length_le (valid.2.2 creator)

theorem Placement.frame_passive (placement : Placement component whole) (separated : placement.Separated) :
    InterfacePrefix.Passive placement.element placement.frame := by
  constructor
  · intro x member old
    obtain ⟨block, blockMem, present⟩ := List.mem_flatMap.mp member
    obtain ⟨i, iMem, rfl⟩ := List.mem_map.mp blockMem
    exact (separated i ((placement.mem_foreignIds i).mp iMem)).1 x present old
  · intro block member growing old
    obtain ⟨i, iMem, rfl⟩ := List.mem_map.mp member
    exact (separated i ((placement.mem_foreignIds i).mp iMem)).2 growing old

theorem Placement.active_observable (placement : Placement component whole) :
    placement.activeIds.map (fun i => InterfaceHistory.observable (whole.blocks.get i)) =
      (component.blocks.map (InterfaceEmbedding.block placement.element)).map InterfaceHistory.observable := by
  rw [Placement.activeIds, List.map_map]
  conv_rhs => rw [← List.map_get_finRange component.blocks]
  simp only [List.map_map]
  apply List.map_congr_left
  intro i _
  obtain ⟨block, found, same⟩ := placement.lookup i
  have getEq : whole.blocks.get (placement.finId i) = block := by
    exact (List.getElem?_eq_some_iff.mp found).2
  simpa only [Function.comp_apply, getEq] using same.symm

theorem Placement.equivalent (placement : Placement component whole) :
    InterfacePermutation.Equivalent (InterfacePrefix.state placement.element placement.frame component) whole := by
  constructor
  · have perm := placement.partition.map (fun i => InterfaceHistory.observable (whole.blocks.get i))
    simp only [List.map_append, placement.active_observable] at perm
    have mappedAll : (List.finRange whole.blocks.length).map (fun i => InterfaceHistory.observable (whole.blocks.get i)) =
        whole.blocks.map InterfaceHistory.observable := by
      change (List.finRange whole.blocks.length).map (InterfaceHistory.observable ∘ whole.blocks.get) = _
      rw [← List.map_map, List.map_get_finRange]
    rw [mappedAll] at perm
    simpa only [InterfacePrefix.state, Placement.frame, List.map_append, List.map_map, Function.comp_def] using perm
  · funext x
    by_cases inside : x ∈ Set.range placement.element
    · obtain ⟨old, rfl⟩ := inside
      rw [InterfacePrefix.value_image placement.element placement.element_injective]
      exact (placement.value old).symm
    · exact InterfacePrefix.value_outside placement.element placement.frame component x inside

noncomputable def Placement.framed (placement : Placement component whole) (separated : placement.Separated)
    {params : Parameters} (valid : whole.Valid params) : InterfaceFramedTrace.Framed params component whole :=
  ⟨placement.element, placement.element_injective, placement.frame, placement.frame_passive separated,
    placement.frame_valid valid, placement.equivalent⟩

end MultiSplay.InterfacePlacement
