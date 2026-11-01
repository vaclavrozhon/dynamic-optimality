import TangoSquared.Paper20261030.CachedRootMetadataAssociation
import TangoSquared.Paper20261030.SourceSubtreeMetadata

set_option autoImplicit false

/-! Compositional cache frames for a head switch. A frame records the
finite list of physical identifiers whose cache may have been changed.
All other caches remain associated with their original physical ids.
The cursors used below are proof witnesses, not additional runtime fingers.
-/

namespace TangoSquared.Paper20261030.HeadCacheFrame

open ColoredStorage SourcePointer Structural SourcePositions MultiSourceProgram

variable {α ρ τ ι μ : Type*}

/-- Only identifiers in `changed` may acquire different metadata.
Identifier inventory equality supplies the intermediate occurrence when
two frames are composed. Repetitions in `changed` are harmless. -/
structure MetadataFrame (identify : ρ → ι) (changed : List ι)
    (before after : Source α (ρ × μ)) : Prop where
  ids : after.inventory (identify ∘ Prod.fst) = before.inventory (identify ∘ Prod.fst)
  retained : ∀ old, old ∈ before.inventory id → ∀ fresh, fresh ∈ after.inventory id →
    identify fresh.1 = identify old.1 → identify old.1 ∉ changed → fresh.2 = old.2

theorem record_of_label (identify : ρ → ι) (tree : Source α (ρ × μ)) (label : ι)
    (member : label ∈ tree.inventory (identify ∘ Prod.fst)) :
    ∃ record, record ∈ tree.inventory id ∧ identify record.1 = label := by
  simp only [Source.inventory] at member
  obtain ⟨record,present,same⟩ := Multiset.mem_map.mp member
  exact ⟨record,by simpa only [Source.inventory,Multiset.map_id] using present,same⟩

theorem label_of_record (identify : ρ → ι) (tree : Source α (ρ × μ))
    (record : ρ × μ) (member : record ∈ tree.inventory id) :
    identify record.1 ∈ tree.inventory (identify ∘ Prod.fst) := by
  simp only [Source.inventory,Multiset.map_id] at member
  exact Multiset.mem_map.mpr ⟨record,member,rfl⟩

theorem MetadataFrame.mono {identify : ρ → ι} {first second : List ι}
    {before after : Source α (ρ × μ)} (frame : MetadataFrame identify first before after)
    (subset : ∀ ident ∈ first, ident ∈ second) : MetadataFrame identify second before after := by
  refine ⟨frame.ids,?_⟩
  intro old oldPresent fresh freshPresent same outside
  exact frame.retained old oldPresent fresh freshPresent same
    (fun member => outside (subset _ member))

theorem MetadataFrame.trans {identify : ρ → ι} {first second : List ι}
    {before middle after : Source α (ρ × μ)}
    (front : MetadataFrame identify first before middle)
    (back : MetadataFrame identify second middle after) :
    MetadataFrame identify (first ++ second) before after := by
  refine ⟨back.ids.trans front.ids,?_⟩
  intro old oldPresent fresh freshPresent same outside
  have middleMember : identify old.1 ∈ middle.inventory (identify ∘ Prod.fst) := by
    rw [front.ids]
    exact label_of_record identify before old oldPresent
  obtain ⟨intermediate,intermediatePresent,intermediateId⟩ :=
    record_of_label identify middle (identify old.1) middleMember
  have frontCache := front.retained old oldPresent intermediate intermediatePresent intermediateId
    (fun member => outside (List.mem_append_left _ member))
  have backCache := back.retained intermediate intermediatePresent fresh freshPresent
    (same.trans intermediateId.symm) (by
      rw [intermediateId]
      exact fun member => outside (List.mem_append_right _ member))
  exact backCache.trans frontCache

theorem MetadataFrame.of_retained (identify : ρ → ι) (changed : ι)
    (before after : Source α (ρ × μ))
    (ids : after.inventory (identify ∘ Prod.fst) = before.inventory (identify ∘ Prod.fst))
    (retained : CachedRootOperation.RetainedMetadata identify changed before after) :
    MetadataFrame identify [changed] before after := by
  refine ⟨ids,?_⟩
  intro old oldPresent fresh freshPresent same outside
  exact retained old oldPresent fresh freshPresent same (by simpa only [List.mem_singleton] using outside)

theorem MetadataFrame.of_retained_order (identify : ρ → ι) (changed : ι)
    (before after : Source α (ρ × μ))
    (order : after.inorderLabels (identify ∘ Prod.fst) = before.inorderLabels (identify ∘ Prod.fst))
    (retained : CachedRootOperation.RetainedMetadata identify changed before after) :
    MetadataFrame identify [changed] before after := by
  apply MetadataFrame.of_retained identify changed before after _ retained
  rw [← Source.inorderLabels_multiset,← Source.inorderLabels_multiset,order]

theorem MetadataFrame.of_paired (identify : ρ → ι) (before after : Source α (ρ × μ))
    (unique : (before.inventory (identify ∘ Prod.fst)).Nodup)
    (paired : after.inventory (fun record => (identify record.1,record.2)) =
      before.inventory (fun record => (identify record.1,record.2))) :
    MetadataFrame identify [] before after := by
  refine ⟨?_,?_⟩
  · have projected := congrArg (Multiset.map Prod.fst) paired
    simpa only [Source.inventory,Multiset.map_map,Function.comp_def] using projected
  · intro old oldPresent fresh freshPresent same _
    exact Source.metadata_of_paired_inventory (identify ∘ Prod.fst) Prod.snd before after unique paired
      old fresh oldPresent freshPresent same

theorem MetadataFrame.refl (identify : ρ → ι) (tree : Source α (ρ × μ))
    (unique : (tree.inventory (identify ∘ Prod.fst)).Nodup) :
    MetadataFrame identify [] tree tree := MetadataFrame.of_paired identify tree tree unique rfl

/-- A cache write may change one cache, even if the enclosing packet at
that vertex has previously changed. -/
theorem MetadataFrame.write (identify : ρ → ι) (current : Cursor α (ρ × μ)) (fresh : μ)
    (unique : (current.tree.inventory (identify ∘ Prod.fst)).Nodup) :
    MetadataFrame identify [identify current.focus.rootRecord.1] current.tree
      (plug (current.focus.setRoot (current.focus.rootRecord.1,fresh)) current.ancestors) := by
  refine ⟨plug_inventory_congr (identify ∘ Prod.fst)
    (Source.inventory_setRoot (identify ∘ Prod.fst) current.focus (current.focus.rootRecord.1,fresh) rfl) current.ancestors,?_⟩
  intro old oldPresent new newPresent same outside
  let predicate : ρ × μ → Prop := fun record => identify record.1 = identify old.1 → record.2 = old.2
  have invariant : SourceRecordPredicate.Holds predicate current.tree := by
    intro record member identity
    exact Source.metadata_of_paired_inventory (identify ∘ Prod.fst) Prod.snd current.tree current.tree unique rfl
      old record oldPresent member identity
  have updated := SourceRecordPredicate.write predicate current (current.focus.rootRecord.1,fresh) invariant (by
    intro identity
    exact False.elim (outside (List.mem_singleton.mpr identity.symm)))
  exact updated new newPresent same

theorem MetadataFrame.cache_at {identify : ρ → ι} {changed : List ι}
    {before after : Source α (ρ × μ)} (frame : MetadataFrame identify changed before after)
    (old fresh : Cursor α (ρ × μ)) (oldTree : old.tree = before) (freshTree : fresh.tree = after)
    (same : identify fresh.focus.rootRecord.1 = identify old.focus.rootRecord.1)
    (outside : identify old.focus.rootRecord.1 ∉ changed) :
    fresh.focus.rootRecord.2 = old.focus.rootRecord.2 := by
  apply frame.retained old.focus.rootRecord _ fresh.focus.rootRecord _ same outside
  · rw [← oldTree]
    exact Multiset.mem_of_le (inventory_le_plug id old.focus old.ancestors) (root_mem_inventory id old.focus)
  · rw [← freshTree]
    exact Multiset.mem_of_le (inventory_le_plug id fresh.focus fresh.ancestors) (root_mem_inventory id fresh.focus)

/-- Lift an erased, proof-only occurrence and recover its stored cache.
This theorem neither searches the runtime tree nor allocates a finger. -/
theorem MetadataFrame.lift_ghost {identify : ρ → ι} {changed : List ι}
    {before after : Source α (ρ × μ)} (frame : MetadataFrame identify changed before after)
    (old : Cursor α (ρ × μ)) (oldTree : old.tree = before)
    (raw : Cursor α ρ) (rawTree : raw.tree = after.mapRecords Prod.fst)
    (same : identify raw.focus.rootRecord = identify old.focus.rootRecord.1)
    (outside : identify old.focus.rootRecord.1 ∉ changed) :
    ∃ actual : Cursor α (ρ × μ), actual.tree = after ∧ actual.mapRecords Prod.fst = raw ∧
      actual.focus.rootRecord.2 = old.focus.rootRecord.2 := by
  have located : locate (after.mapRecords Prod.fst) (address raw) = some raw := by
    rw [← rawTree]
    exact locate_cursor raw
  obtain ⟨actual,found,erases⟩ := lift_locate Prod.fst after (address raw) raw located
  have actualTree := locate_tree found
  refine ⟨actual,actualTree,erases,frame.cache_at old actual oldTree actualTree ?_ outside⟩
  have roots : identify actual.focus.rootRecord.1 = identify raw.focus.rootRecord := by
    simpa only [Cursor.mapRecords,Source.mapRecords_root] using
      congrArg (fun cursor : Cursor α ρ => identify cursor.focus.rootRecord) erases
  exact roots.trans same

/-- A proper retained payload cannot be the refreshed component root.
The hypothesis allows different enclosing packets at both occurrences. -/
theorem proper_payload_root_ne (identify : ρ → ι) (erase : ρ → τ)
    (child parent : Cursor α ρ) (sameTree : child.tree = parent.tree)
    (unique : (child.tree.inventory identify).Nodup)
    (payload : Source α τ) (enclosing : τ) (inside : List (Frame α τ))
    (proper : inside ≠ [])
    (childView : (child.focus.mapRecords erase).setRoot payload.rootRecord = payload)
    (parentView : parent.focus.mapRecords erase = plug (payload.setRoot enclosing) inside) :
    identify child.focus.rootRecord ≠ identify parent.focus.rootRecord := by
  intro same
  have equal := cursors_eq_of_label identify child parent sameTree unique same
  have childLeaves : child.focus.shape.leaves = payload.shape.leaves := by
    simpa only [source_setRoot_shape,Source.mapRecords_shape] using
      congrArg (fun tree : Source α τ => tree.shape.leaves) childView
  have parentLeaves : parent.focus.shape.leaves = (plug (payload.setRoot enclosing) inside).shape.leaves := by
    simpa only [Source.mapRecords_shape] using
      congrArg (fun tree : Source α τ => tree.shape.leaves) parentView
  have smaller := SubtreeMetadata.proper_leaves_lt (payload.setRoot enclosing) inside proper
  simp only [source_setRoot_shape] at smaller
  have equalSize := congrArg (fun cursor : Cursor α ρ => cursor.focus.shape.leaves.length) equal
  rw [childLeaves,parentLeaves] at equalSize
  omega

end TangoSquared.Paper20261030.HeadCacheFrame
