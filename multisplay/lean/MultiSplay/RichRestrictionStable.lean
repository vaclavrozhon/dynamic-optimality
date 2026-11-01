import MultiSplay.RichRestriction

/-! # Stability of a restricted component with its retained history -/

namespace MultiSplay.RichRestriction

open Splay.Lazy (State Block HeapView Element Side)

variable {n m : Nat}

theorem blocks_eq_filter (source : State m) (small : HeapView n) (embedding : Embedding small source.view) :
    (state source small embedding).blocks =
      (source.blocks.filter (fun block => decide (block.owner ∈ Set.range embedding.element))).map (BlockEmbedding.block embedding.project) := by
  classical
  rw [← selected_eq_filter, List.map_map]
  rfl

theorem projected_member {params : Splay.Interface.Parameters}
    (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (stable : source.Stable params) (block : Block m) (member : block ∈ source.blocks)
    (inside : block.owner ∈ Set.range embedding.element) {x : Element m} (present : x ∈ block.elements) :
    embedding.project x ∈ small.topDown (embedding.project block.owner) block.side := by
  have attached := (stable.valid.2 block member).1.mem present
  rw [RichJoin.complete_attached source stable.2.1,
    ← embedding.element_project inside, embedding.children] at attached
  obtain ⟨original, originalMem, eq⟩ := List.mem_map.mp attached
  simpa only [← eq, Embedding.project_element] using originalMem

theorem projected_not_root {params : Splay.Interface.Parameters}
    (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (stable : source.Stable params) (block : Block m) (member : block ∈ source.blocks)
    (inside : block.owner ∈ Set.range embedding.element) {x : Element m} (present : x ∈ block.elements) :
    embedding.project x ≠ small.root := by
  have parent := small.mem_topDown_parent (projected_member source small embedding stable block member inside present)
  intro eq
  rw [eq, small.root_parent] at parent
  cases parent

theorem owner_iff (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (block : Block m) (inside : block.owner ∈ Set.range embedding.element) (owner : Element n) :
    embedding.project block.owner = owner ↔ block.owner = embedding.element owner := by
  constructor
  · intro eq
    rw [← eq, embedding.element_project inside]
  · intro eq
    rw [eq, Embedding.project_element]

theorem creator_iff {params : Splay.Interface.Parameters}
    (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (stable : source.Stable params) (block : Block m) (member : block ∈ source.blocks)
    (inside : block.owner ∈ Set.range embedding.element) (growing : block.mode = .growing) (creator : Element n) :
    embedding.project block.creator = creator ↔ block.creator = embedding.element creator := by
  rw [← (stable.valid.2 block member).2.1 growing]
  exact owner_iff source small embedding block inside creator

theorem growingCount {params : Splay.Interface.Parameters}
    (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (stable : source.Stable params) (creator : Element n) :
    (state source small embedding).toInterface.growingCount creator = source.toInterface.growingCount (embedding.element creator) := by
  classical
  simp only [Splay.Interface.State.growingCount, State.toInterface, blocks_eq_filter,
    List.filter_map, List.length_map, List.filter_filter, Function.comp_def, Block.toInterface, BlockEmbedding.block]
  congr 1
  apply List.filter_congr
  intro block member
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨growing, same⟩, inside⟩
    exact ⟨growing, (creator_iff source small embedding stable block member inside growing creator).mp same⟩
  · rintro ⟨growing, same⟩
    have inside : block.owner ∈ Set.range embedding.element := by
      rw [(stable.valid.2 block member).2.1 growing, same]
      exact Set.mem_range_self _
    exact ⟨⟨growing, (creator_iff source small embedding stable block member inside growing creator).mpr same⟩, inside⟩

theorem valid {params : Splay.Interface.Parameters}
    (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (stable : source.Stable params) : (state source small embedding).Valid params := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [State.toInterface_allElements]
    exact List.Nodup.of_map embedding.element ((stable.valid.allElements_nodup).sublist (allElements_sublist source small embedding stable))
  · intro x
    change 1 ≤ (if x = small.root then 1 else source.value (embedding.element x)) ∧
      (if x = small.root then 1 else source.value (embedding.element x)) ≤ params.valueBound
    by_cases eq : x = small.root
    · simp only [eq, if_pos]
      exact ⟨Nat.le_refl 1, Nat.le_trans (by decide : 1 ≤ 2) params.valueBound_ge_two⟩
    · simpa only [eq, if_false, State.toInterface] using stable.valid.1.2.1 (embedding.element x)
  · intro creator
    rw [growingCount source small embedding stable]
    exact stable.valid.1.2.2 _
  · intro block member
    obtain ⟨id, idMem, rfl⟩ := List.mem_map.mp member
    have inside := (mem_ids source embedding id).mp idMem
    apply HeapEmbedding.structurallyValid embedding.project source.view small source.allElements
      (state source small embedding).allElements _ (stable.valid.2 _ (List.get_mem _ id))
    · change (state source small embedding).view.attachedTopDown _ _ _ = _
      rw [RichJoin.complete_attached _ (complete source small embedding stable),
        RichJoin.complete_attached source stable.2.1,
        ← embedding.element_project inside, embedding.children, List.map_map]
      simp [state, Function.comp_def]
    · intro x present
      rw [← embedding.gap (embedding.project x) (projected_not_root source small embedding stable _ (List.get_mem _ id) inside present),
        embedding.element_project (old_elements_inside source small embedding stable _ (List.get_mem _ id) inside present)]

theorem oneGrowingPerSide {params : Splay.Interface.Parameters}
    (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (stable : source.Stable params) : (state source small embedding).OneGrowingPerSide := by
  intro owner side
  obtain ⟨oldId, fields, unique⟩ := stable.2.2.2.1 (embedding.element owner) side
  have inside : (source.blocks.get oldId).owner ∈ Set.range embedding.element := by
    rw [fields.2.1]
    exact Set.mem_range_self _
  obtain ⟨id, originEq⟩ := origin_surjective_on source small embedding oldId inside
  refine ⟨id, ?_, ?_⟩
  · simp only [get_block, originEq, BlockEmbedding.block]
    exact ⟨fields.1, by rw [fields.2.1, Embedding.project_element], fields.2.2⟩
  · intro other otherFields
    apply origin_injective source small embedding
    rw [originEq]
    apply unique
    simp only [get_block, BlockEmbedding.block] at otherFields
    exact ⟨otherFields.1, (owner_iff source small embedding _ (origin_inside source small embedding other) owner).mp otherFields.2.1, otherFields.2.2⟩

theorem growingTopmost {params : Splay.Interface.Parameters}
    (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (stable : source.Stable params) : (state source small embedding).GrowingTopmost := by
  intro id
  dsimp only
  intro growing
  rw [get_block] at growing ⊢
  obtain ⟨suffix, oldTop⟩ := stable.2.2.2.2.1 (origin source small embedding id) growing
  refine ⟨suffix.map embedding.project, ?_⟩
  have inside := origin_inside source small embedding id
  have mapped := congrArg (List.map embedding.project) oldTop
  rw [← embedding.element_project inside, embedding.children, List.map_map] at mapped
  simpa [state, BlockEmbedding.block, List.map_append, Function.comp_def] using mapped

theorem valuesRealizeGaps {params : Splay.Interface.Parameters}
    (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (stable : source.Stable params) : (state source small embedding).ValuesRealizeGaps := by
  refine ⟨by simp [state], ?_⟩
  intro block member x present
  obtain ⟨id, idMem, rfl⟩ := List.mem_map.mp member
  obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp present
  have inside := (mem_ids source embedding id).mp idMem
  have notRoot := projected_not_root source small embedding stable _ (List.get_mem _ id) inside oldMem
  change (if embedding.project old = small.root then 1 else source.value (embedding.element (embedding.project old))) = _
  rw [if_neg notRoot, embedding.element_project (old_elements_inside source small embedding stable _ (List.get_mem _ id) inside oldMem)]
  rw [stable.2.2.2.2.2.2 _ (List.get_mem _ id) old oldMem]
  change Splay.Analysis.transientContractedGap (source.view.rawGap old) _ =
    Splay.Analysis.transientContractedGap (small.rawGap (embedding.project old)) _
  rw [← embedding.gap _ notRoot, embedding.element_project (old_elements_inside source small embedding stable _ (List.get_mem _ id) inside oldMem)]
  rfl

theorem stable {params : Splay.Interface.Parameters}
    (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (old : source.Stable params) (ordered : small.HeapOrdered) :
    (state source small embedding).Stable params :=
  ⟨valid source small embedding old, complete source small embedding old, ordered,
   oneGrowingPerSide source small embedding old, growingTopmost source small embedding old,
   valuesRealizeGaps source small embedding old⟩

/-- The actual global creator remains unchanged. A local proxy for a retired
creator agrees on every field observed by a legal strict operation. -/
theorem observable_retained {params : Splay.Interface.Parameters}
    (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (old : source.Stable params) (id : Fin (state source small embedding).blocks.length) :
    InterfaceHistory.observable (InterfaceEmbedding.block embedding.element
      ((state source small embedding).blocks.get id).toInterface) =
    InterfaceHistory.observable (source.blocks.get (origin source small embedding id)).toInterface := by
  rw [get_block]
  apply InterfaceHistory.observable_eq.mpr
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact old_elements_map source small embedding old _ (List.get_mem _ _) (origin_inside source small embedding id)
  · intro growing
    change embedding.element (embedding.project (source.blocks.get (origin source small embedding id)).creator) = _
    apply embedding.element_project
    rw [← (old.valid.2 _ (List.get_mem _ _)).2.1 growing]
    exact origin_inside source small embedding id

end MultiSplay.RichRestriction
