import MultiSplay.RichJoinTopDown
import MultiSplay.InterfaceHistory

/-!
# Restricting a persistent rich history to one heap component

A component embedding preserves the ordered child lists and the internal raw
rank gaps. Restriction selects records by their current owner, retaining their
order, pass counters, modes, and interval minima. The selected original IDs are
kept explicitly. Only retired creators outside the component use local proxies.
-/

namespace MultiSplay.RichRestriction

open Splay.Lazy (State Block HeapView Element Side)

variable {n m : Nat}

structure Embedding (small : HeapView n) (big : HeapView m) where
  element : Element n → Element m
  injective : Function.Injective element
  children : ∀ owner side, big.topDown (element owner) side = (small.topDown owner side).map element
  gap : ∀ x, x ≠ small.root → big.rawGap (element x) = small.rawGap x

noncomputable def Embedding.project {small : HeapView n} {big : HeapView m}
    (embedding : Embedding small big) : Element m → Element n := Function.invFun embedding.element

@[simp] theorem Embedding.project_element {small : HeapView n} {big : HeapView m}
    (embedding : Embedding small big) (x : Element n) : embedding.project (embedding.element x) = x :=
  Function.leftInverse_invFun embedding.injective x

theorem Embedding.element_project {small : HeapView n} {big : HeapView m}
    (embedding : Embedding small big) {x : Element m} (inside : x ∈ Set.range embedding.element) :
    embedding.element (embedding.project x) = x := Function.invFun_eq inside

noncomputable def ids (source : State m) {small : HeapView n} (embedding : Embedding small source.view) :
    List (Fin source.blocks.length) := by
  classical
  exact (List.finRange source.blocks.length).filter (fun id => decide ((source.blocks.get id).owner ∈ Set.range embedding.element))

@[simp] theorem mem_ids (source : State m) {small : HeapView n} (embedding : Embedding small source.view)
    (id : Fin source.blocks.length) : id ∈ ids source embedding ↔ (source.blocks.get id).owner ∈ Set.range embedding.element := by
  classical
  simp [ids]

theorem ids_nodup (source : State m) {small : HeapView n} (embedding : Embedding small source.view) :
    (ids source embedding).Nodup := (List.nodup_finRange _).filter _

theorem selected_eq_filter (source : State m) {small : HeapView n} (embedding : Embedding small source.view) :
    (ids source embedding).map source.blocks.get =
      source.blocks.filter (fun block => decide (block.owner ∈ Set.range embedding.element)) := by
  classical
  change ((List.finRange source.blocks.length).filter
    ((fun block : Block m => decide (block.owner ∈ Set.range embedding.element)) ∘ source.blocks.get)).map source.blocks.get = _
  rw [← List.filter_map, List.map_get_finRange]

noncomputable def state (source : State m) (small : HeapView n) (embedding : Embedding small source.view) : State n where
  view := small
  blocks := (ids source embedding).map (fun id => BlockEmbedding.block embedding.project (source.blocks.get id))
  value := fun x => if x = small.root then 1 else source.value (embedding.element x)

noncomputable def origin (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (id : Fin (state source small embedding).blocks.length) : Fin source.blocks.length :=
  (ids source embedding).get ⟨id.val, by simpa [state] using id.isLt⟩

theorem origin_injective (source : State m) (small : HeapView n) (embedding : Embedding small source.view) :
    Function.Injective (origin source small embedding) := by
  intro i j same
  have eq := (ids_nodup source embedding).get_inj_iff.mp same
  exact Fin.ext (congrArg (fun k : Fin (ids source embedding).length => k.val) eq)

theorem origin_inside (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (id : Fin (state source small embedding).blocks.length) :
    (source.blocks.get (origin source small embedding id)).owner ∈ Set.range embedding.element :=
  (mem_ids source embedding _).mp (List.get_mem _ _)

@[simp] theorem get_block (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (id : Fin (state source small embedding).blocks.length) :
    (state source small embedding).blocks.get id =
      BlockEmbedding.block embedding.project (source.blocks.get (origin source small embedding id)) := by
  simp [state, origin, List.get_eq_getElem]

theorem origin_surjective_on (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (id : Fin source.blocks.length) (inside : (source.blocks.get id).owner ∈ Set.range embedding.element) :
    ∃ j, origin source small embedding j = id := by
  obtain ⟨j, eq⟩ := List.mem_iff_get.mp ((mem_ids source embedding id).mpr inside)
  exact ⟨⟨j.val, by simpa [state] using j.isLt⟩, eq⟩

theorem old_elements_inside {params : Splay.Interface.Parameters}
    (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (stable : source.Stable params) (block : Block m) (member : block ∈ source.blocks)
    (inside : block.owner ∈ Set.range embedding.element) {x : Element m} (present : x ∈ block.elements) :
    x ∈ Set.range embedding.element := by
  obtain ⟨owner, ownerEq⟩ := inside
  have attached := (stable.valid.2 block member).1.mem present
  rw [RichJoin.complete_attached source stable.2.1, ← ownerEq, embedding.children] at attached
  obtain ⟨element, _, eq⟩ := List.mem_map.mp attached
  exact ⟨element, eq⟩

theorem old_elements_map {params : Splay.Interface.Parameters}
    (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (stable : source.Stable params) (block : Block m) (member : block ∈ source.blocks)
    (inside : block.owner ∈ Set.range embedding.element) :
    (block.elements.map embedding.project).map embedding.element = block.elements := by
  rw [List.map_map]
  calc
    _ = block.elements.map id := List.map_congr_left (fun x present => ?_)
    _ = block.elements := List.map_id _
  
  exact embedding.element_project (old_elements_inside source small embedding stable block member inside present)

theorem allElements_sublist {params : Splay.Interface.Parameters}
    (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (stable : source.Stable params) :
    ((state source small embedding).allElements.map embedding.element).Sublist source.allElements := by
  classical
  have eq : (state source small embedding).allElements.map embedding.element =
      ((ids source embedding).map source.blocks.get).flatMap Block.elements := by
    simp only [state, State.allElements, List.flatMap_map, List.map_flatMap, BlockEmbedding.block]
    apply List.flatMap_congr
    intro id member
    exact old_elements_map source small embedding stable _ (List.get_mem _ _) ((mem_ids source embedding id).mp member)
  rw [eq, selected_eq_filter]
  exact List.filter_sublist.flatMap _

theorem complete {params : Splay.Interface.Parameters}
    (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (stable : source.Stable params) : (state source small embedding).Complete := by
  intro x
  constructor
  · intro assigned
    obtain ⟨block, member, present⟩ := State.mem_allElements_iff.mp assigned
    obtain ⟨id, idMem, rfl⟩ := List.mem_map.mp member
    obtain ⟨old, oldMem, oldEq⟩ := List.mem_map.mp present
    obtain ⟨owner, ownerEq⟩ := (mem_ids source embedding id).mp idMem
    have attached := (stable.valid.2 _ (List.get_mem _ id)).1.mem oldMem
    rw [RichJoin.complete_attached source stable.2.1, ← ownerEq, embedding.children] at attached
    obtain ⟨original, localMem, localEq⟩ := List.mem_map.mp attached
    have same : original = x := by rw [← oldEq, ← localEq, Embedding.project_element]
    subst original
    have parent := small.mem_topDown_parent localMem
    change small.parent x ≠ none
    rw [parent]
    exact Option.some_ne_none _
  · intro notRoot
    obtain ⟨owner, parent⟩ := Option.ne_none_iff_exists'.mp notRoot
    have localMem := small.mem_topDown_iff.mpr ⟨parent, rfl⟩
    have globalMem : embedding.element x ∈ source.view.topDown (embedding.element owner) (small.side x) := by
      rw [embedding.children]
      exact List.mem_map.mpr ⟨x, localMem, rfl⟩
    have globalParent := source.view.mem_topDown_parent globalMem
    have assigned := (stable.2.1 _).mpr (by rw [globalParent]; exact Option.some_ne_none _)
    obtain ⟨block, member, present⟩ := State.mem_allElements_iff.mp assigned
    have ownerEq : block.owner = embedding.element owner := Option.some.inj
      (((stable.valid.2 block member).parent_eq present).symm.trans globalParent)
    obtain ⟨id, idEq⟩ := List.mem_iff_get.mp member
    apply State.mem_allElements_iff.mpr
    refine ⟨BlockEmbedding.block embedding.project block, ?_, ?_⟩
    · apply List.mem_map.mpr
      exact ⟨id, (mem_ids source embedding id).mpr (by rw [idEq, ownerEq]; exact Set.mem_range_self _), by rw [idEq]⟩
    · exact List.mem_map.mpr ⟨embedding.element x, present, embedding.project_element x⟩

end MultiSplay.RichRestriction
