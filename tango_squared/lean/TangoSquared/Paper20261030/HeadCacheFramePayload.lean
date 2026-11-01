import TangoSquared.Paper20261030.HeadCacheFrame
import TangoSquared.Paper20261030.RetainedSubtreeHandoff

set_option autoImplicit false

/-! A retained payload determines a proof-only final cursor and its
unchanged cache. Physical inorder ids recover the root id even when its
enclosing packet changes. No parked finger for that payload is required.
-/

namespace TangoSquared.Paper20261030.HeadCacheFrame

open ColoredStorage SourcePointer Structural SourcePositions MultiSourceProgram SubtreeMetadata

variable {α ρ ι μ : Type*}

/-- Payload identity transport before any claim about its cache. This
separation lets a proper output occurrence prove that the physical root
was not among the roots whose cache was refreshed. -/
theorem retained_payload_ghost
    {before after : Source α ((ι × ρ) × μ)}
    (leafWord : before.shape.leaves = after.shape.leaves)
    (order : after.inorderLabels (fun record => record.1.1) = before.inorderLabels (fun record => record.1.1))
    (distinct : before.shape.leaves.Nodup)
    (old : Cursor α ((ι × ρ) × μ)) (oldTree : old.tree = before)
    (view : Cursor α ρ) (viewTree : view.tree = (after.mapRecords Prod.fst).mapRecords Prod.snd)
    (oldPacket freshPacket : ρ)
    (retained : ((old.focus.mapRecords Prod.fst).mapRecords Prod.snd).setRoot oldPacket =
      view.focus.setRoot freshPacket) :
    ∃ actual : Cursor α ((ι × ρ) × μ), actual.tree = after ∧
      (actual.mapRecords Prod.fst).mapRecords Prod.snd = view ∧
      actual.focus.rootRecord.1.1 = old.focus.rootRecord.1.1 ∧
      (replacePayload (old.mapRecords Prod.fst) oldPacket).focus =
        (replacePayload (actual.mapRecords Prod.fst) freshPacket).focus := by
  have located : locate ((after.mapRecords Prod.fst).mapRecords Prod.snd) (address view) = some view := by
    rw [← viewTree]
    exact locate_cursor view
  obtain ⟨raw,found,erases⟩ := lift_locate Prod.snd (after.mapRecords Prod.fst) (address view) view located
  have rawTree := locate_tree found
  have whole : (old.mapRecords Prod.fst).tree.shape.leaves = raw.tree.shape.leaves := by
    rw [Cursor.mapRecords_tree,oldTree,rawTree]
    simpa only [Source.mapRecords_shape] using leafWord
  have oldDistinct : (old.mapRecords Prod.fst).tree.shape.leaves.Nodup := by
    rw [Cursor.mapRecords_tree,oldTree,Source.mapRecords_shape]
    exact distinct
  have payload : ((old.mapRecords Prod.fst).focus.mapRecords Prod.snd).setRoot oldPacket =
      (raw.focus.mapRecords Prod.snd).setRoot freshPacket := by
    rw [← erases] at retained
    exact retained
  have rawOrder : (old.mapRecords Prod.fst).tree.inorderLabels Prod.fst = raw.tree.inorderLabels Prod.fst := by
    rw [Cursor.mapRecords_tree,oldTree,rawTree]
    simpa only [Source.inorderLabels_map,Function.comp_def] using order.symm
  have equal := focus_replacePayload_eq (old.mapRecords Prod.fst) raw oldPacket freshPacket
    whole oldDistinct payload rawOrder
  have rawId : raw.focus.rootRecord.1 = old.focus.rootRecord.1.1 := by
    have roots := congrArg (fun tree : Source α (ι × ρ) => tree.rootRecord.1) equal
    have root_set (tree : Source α (ι × ρ)) (fresh : ι × ρ) : (tree.setRoot fresh).rootRecord = fresh := by
      cases tree <;> rfl
    simpa only [replacePayload,root_set,Cursor.mapRecords,Source.mapRecords_root] using roots.symm
  have rawLocated : locate (after.mapRecords Prod.fst) (address raw) = some raw := by
    rw [← rawTree]
    exact locate_cursor raw
  obtain ⟨actual,actualFound,actualErases⟩ := lift_locate Prod.fst after (address raw) raw rawLocated
  refine ⟨actual,locate_tree actualFound,by rw [actualErases]; exact erases,?_,?_⟩
  · have roots : actual.focus.rootRecord.1.1 = raw.focus.rootRecord.1 := by
      simpa only [Cursor.mapRecords,Source.mapRecords_root] using
        congrArg (fun current : Cursor α (ι × ρ) => current.focus.rootRecord.1) actualErases
    exact roots.trans rawId
  · rw [actualErases]
    exact equal

theorem MetadataFrame.retained_payload {changed : List ι}
    {before after : Source α ((ι × ρ) × μ)}
    (frame : MetadataFrame Prod.fst changed before after)
    (leafWord : before.shape.leaves = after.shape.leaves)
    (order : after.inorderLabels (fun record => record.1.1) = before.inorderLabels (fun record => record.1.1))
    (distinct : before.shape.leaves.Nodup)
    (old : Cursor α ((ι × ρ) × μ)) (oldTree : old.tree = before)
    (view : Cursor α ρ) (viewTree : view.tree = (after.mapRecords Prod.fst).mapRecords Prod.snd)
    (oldPacket freshPacket : ρ)
    (retained : ((old.focus.mapRecords Prod.fst).mapRecords Prod.snd).setRoot oldPacket =
      view.focus.setRoot freshPacket)
    (outside : old.focus.rootRecord.1.1 ∉ changed) :
    ∃ actual : Cursor α ((ι × ρ) × μ), actual.tree = after ∧
      (actual.mapRecords Prod.fst).mapRecords Prod.snd = view ∧
      actual.focus.rootRecord.1.1 = old.focus.rootRecord.1.1 ∧
      actual.focus.rootRecord.2 = old.focus.rootRecord.2 ∧
      (replacePayload (old.mapRecords Prod.fst) oldPacket).focus =
        (replacePayload (actual.mapRecords Prod.fst) freshPacket).focus := by
  have located : locate ((after.mapRecords Prod.fst).mapRecords Prod.snd) (address view) = some view := by
    rw [← viewTree]
    exact locate_cursor view
  obtain ⟨raw,found,erases⟩ := lift_locate Prod.snd (after.mapRecords Prod.fst) (address view) view located
  have rawTree := locate_tree found
  have whole : (old.mapRecords Prod.fst).tree.shape.leaves = raw.tree.shape.leaves := by
    rw [Cursor.mapRecords_tree,oldTree,rawTree]
    simpa only [Source.mapRecords_shape] using leafWord
  have oldDistinct : (old.mapRecords Prod.fst).tree.shape.leaves.Nodup := by
    rw [Cursor.mapRecords_tree,oldTree,Source.mapRecords_shape]
    exact distinct
  have payload : ((old.mapRecords Prod.fst).focus.mapRecords Prod.snd).setRoot oldPacket =
      (raw.focus.mapRecords Prod.snd).setRoot freshPacket := by
    rw [← erases] at retained
    exact retained
  have rawOrder : (old.mapRecords Prod.fst).tree.inorderLabels Prod.fst = raw.tree.inorderLabels Prod.fst := by
    rw [Cursor.mapRecords_tree,oldTree,rawTree]
    simpa only [Source.inorderLabels_map,Function.comp_def] using order.symm
  have equal := focus_replacePayload_eq (old.mapRecords Prod.fst) raw oldPacket freshPacket
    whole oldDistinct payload rawOrder
  have rawId : raw.focus.rootRecord.1 = old.focus.rootRecord.1.1 := by
    have roots := congrArg (fun tree : Source α (ι × ρ) => tree.rootRecord.1) equal
    have root_set (tree : Source α (ι × ρ)) (fresh : ι × ρ) : (tree.setRoot fresh).rootRecord = fresh := by
      cases tree <;> rfl
    simpa only [replacePayload,root_set,Cursor.mapRecords,Source.mapRecords_root] using roots.symm
  obtain ⟨actual,actualTree,actualErases,cache⟩ := frame.lift_ghost old oldTree raw rawTree rawId outside
  refine ⟨actual,actualTree,by rw [actualErases]; exact erases,?_,cache,?_⟩
  · have roots : actual.focus.rootRecord.1.1 = raw.focus.rootRecord.1 := by
      simpa only [Cursor.mapRecords,Source.mapRecords_root] using
        congrArg (fun current : Cursor α (ι × ρ) => current.focus.rootRecord.1) actualErases
    exact roots.trans rawId
  · rw [actualErases]
    exact equal

/-- A source operation's single refreshed root cannot overwrite a
proper retained payload cache. The exclusion is derived from physical
uniqueness and the proper output occurrence, not assumed as a frame. -/
theorem MetadataFrame.retained_proper_payload
    {before after : Source α ((ι × ρ) × μ)} (changed : ι)
    (frame : MetadataFrame Prod.fst [changed] before after)
    (leafWord : before.shape.leaves = after.shape.leaves)
    (order : after.inorderLabels (fun record => record.1.1) = before.inorderLabels (fun record => record.1.1))
    (distinct : before.shape.leaves.Nodup)
    (unique : (after.inventory (fun record => record.1.1)).Nodup)
    (old : Cursor α ((ι × ρ) × μ)) (oldTree : old.tree = before)
    (view : Cursor α ρ) (viewTree : view.tree = (after.mapRecords Prod.fst).mapRecords Prod.snd)
    (oldPacket freshPacket : ρ)
    (retained : ((old.focus.mapRecords Prod.fst).mapRecords Prod.snd).setRoot oldPacket =
      view.focus.setRoot freshPacket)
    (parent : Cursor α ((ι × ρ) × μ)) (parentTree : parent.tree = after)
    (parentId : parent.focus.rootRecord.1.1 = changed)
    (inside : List (Frame α ρ)) (proper : inside ≠ [])
    (parentView : (parent.focus.mapRecords Prod.fst).mapRecords Prod.snd = plug view.focus inside) :
    ∃ actual : Cursor α ((ι × ρ) × μ), actual.tree = after ∧
      (actual.mapRecords Prod.fst).mapRecords Prod.snd = view ∧
      actual.focus.rootRecord.1.1 = old.focus.rootRecord.1.1 ∧
      old.focus.rootRecord.1.1 ≠ changed ∧
      actual.focus.rootRecord.2 = old.focus.rootRecord.2 ∧
      (replacePayload (old.mapRecords Prod.fst) oldPacket).focus =
        (replacePayload (actual.mapRecords Prod.fst) freshPacket).focus := by
  obtain ⟨actual,actualTree,actualErases,identity,payloadEqual⟩ :=
    retained_payload_ghost leafWord order distinct old oldTree view viewTree oldPacket freshPacket retained
  have childLeaves : actual.focus.shape.leaves = view.focus.shape.leaves := by
    simpa only [Cursor.mapRecords,Source.mapRecords_shape] using
      congrArg (fun current : Cursor α ρ => current.focus.shape.leaves) actualErases
  have parentLeaves : parent.focus.shape.leaves = (plug view.focus inside).shape.leaves := by
    simpa only [Source.mapRecords_shape] using
      congrArg (fun tree : Source α ρ => tree.shape.leaves) parentView
  have excluded : old.focus.rootRecord.1.1 ≠ changed := by
    intro same
    have sameId := identity.trans (same.trans parentId.symm)
    have sameCursor := cursors_eq_of_label (fun record => record.1.1) actual parent
      (actualTree.trans parentTree.symm) (actualTree.symm ▸ unique) sameId
    have sameSize := congrArg (fun current : Cursor α ((ι × ρ) × μ) => current.focus.shape.leaves.length) sameCursor
    have smaller := proper_leaves_lt view.focus inside proper
    rw [childLeaves,parentLeaves] at sameSize
    omega
  refine ⟨actual,actualTree,actualErases,identity,excluded,?_,payloadEqual⟩
  exact frame.cache_at old actual oldTree actualTree identity (by simpa only [List.mem_singleton] using excluded)

end TangoSquared.Paper20261030.HeadCacheFrame
