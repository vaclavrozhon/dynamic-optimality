import TangoSquared.Paper20261030.HeadCacheFramePayload

set_option autoImplicit false

/-! A proper retained payload protects every physical identifier inside
it, hence every nested descendant cache, not only the immediate payload
root. All occurrence witnesses below are ghost cursors.
-/

namespace TangoSquared.Paper20261030.HeadCacheFrame

open ColoredStorage SourcePointer Structural SourcePositions SubtreeMetadata

variable {α ρ ι μ : Type*}

/-- Caches on a specified ghost set of physical identifiers are retained.
The predicate can describe all vertices of several retained payloads. -/
structure Protects (identify : ρ → ι) (guarded : ι → Prop)
    (before after : Source α (ρ × μ)) : Prop where
  ids : after.inventory (identify ∘ Prod.fst) = before.inventory (identify ∘ Prod.fst)
  retained : ∀ old, old ∈ before.inventory id → guarded (identify old.1) →
    ∀ fresh, fresh ∈ after.inventory id → identify fresh.1 = identify old.1 → fresh.2 = old.2

theorem Protects.trans {identify : ρ → ι} {guarded : ι → Prop}
    {before middle after : Source α (ρ × μ)}
    (front : Protects identify guarded before middle) (back : Protects identify guarded middle after) :
    Protects identify guarded before after := by
  refine ⟨back.ids.trans front.ids,?_⟩
  intro old oldPresent preserved fresh freshPresent same
  have middleMember : identify old.1 ∈ middle.inventory (identify ∘ Prod.fst) := by
    rw [front.ids]
    exact label_of_record identify before old oldPresent
  obtain ⟨intermediate,intermediatePresent,intermediateId⟩ :=
    record_of_label identify middle (identify old.1) middleMember
  have frontCache := front.retained old oldPresent preserved intermediate intermediatePresent intermediateId
  have backCache := back.retained intermediate intermediatePresent (intermediateId.symm ▸ preserved)
    fresh freshPresent (same.trans intermediateId.symm)
  exact backCache.trans frontCache

theorem Protects.mono {identify : ρ → ι} {guarded smaller : ι → Prop}
    {before after : Source α (ρ × μ)} (frame : Protects identify guarded before after)
    (subset : ∀ ident, smaller ident → guarded ident) : Protects identify smaller before after :=
  ⟨frame.ids,fun old present preserved fresh freshPresent same =>
    frame.retained old present (subset _ preserved) fresh freshPresent same⟩

theorem Protects.union {identify : ρ → ι} {first second : ι → Prop}
    {before after : Source α (ρ × μ)} (left : Protects identify first before after)
    (right : Protects identify second before after) :
    Protects identify (fun ident => first ident ∨ second ident) before after := by
  refine ⟨left.ids,?_⟩
  intro old present preserved fresh freshPresent same
  rcases preserved with guardedLeft | guardedRight
  · exact left.retained old present guardedLeft fresh freshPresent same
  · exact right.retained old present guardedRight fresh freshPresent same

theorem Protects.cache_at {identify : ρ → ι} {guarded : ι → Prop}
    {before after : Source α (ρ × μ)} (frame : Protects identify guarded before after)
    (old fresh : Cursor α (ρ × μ)) (oldTree : old.tree = before) (freshTree : fresh.tree = after)
    (same : identify fresh.focus.rootRecord.1 = identify old.focus.rootRecord.1)
    (preserved : guarded (identify old.focus.rootRecord.1)) :
    fresh.focus.rootRecord.2 = old.focus.rootRecord.2 := by
  apply frame.retained old.focus.rootRecord _ preserved fresh.focus.rootRecord _ same
  · rw [← oldTree]
    exact Multiset.mem_of_le (inventory_le_plug id old.focus old.ancestors) (root_mem_inventory id old.focus)
  · rw [← freshTree]
    exact Multiset.mem_of_le (inventory_le_plug id fresh.focus fresh.ancestors) (root_mem_inventory id fresh.focus)

theorem MetadataFrame.protect {identify : ρ → ι} {changed : List ι} {guarded : ι → Prop}
    {before after : Source α (ρ × μ)} (frame : MetadataFrame identify changed before after)
    (excluded : ∀ ident, guarded ident → ident ∉ changed) : Protects identify guarded before after :=
  ⟨frame.ids,fun old present preserved fresh freshPresent same =>
    frame.retained old present fresh freshPresent same (excluded _ preserved)⟩

theorem cursor_of_record (tree : Source α ρ) (record : ρ) (member : record ∈ tree.inventory id) :
    ∃ current : Cursor α ρ, current.tree = tree ∧ current.focus.rootRecord = record := by
  induction tree with
  | leaf key value =>
    have same : record = value := by simpa only [Source.inventory_leaf,id_eq,Multiset.mem_singleton] using member
    exact ⟨⟨.leaf key value,[]⟩,rfl,same.symm⟩
  | fork value left right ihl ihr =>
    simp only [Source.inventory_fork,id_eq,Multiset.mem_add,Multiset.mem_singleton] at member
    rcases member with (same | onLeft) | onRight
    · exact ⟨⟨.fork value left right,[]⟩,rfl,same.symm⟩
    · obtain ⟨current,treeEq,rootEq⟩ := ihl onLeft
      refine ⟨⟨current.focus,current.ancestors ++ [.left value right]⟩,?_,rootEq⟩
      change plug current.focus (current.ancestors ++ [.left value right]) = _
      rw [plug_append]
      change Source.fork value current.tree right = _
      rw [treeEq]
    · obtain ⟨current,treeEq,rootEq⟩ := ihr onRight
      refine ⟨⟨current.focus,current.ancestors ++ [.right left value]⟩,?_,rootEq⟩
      change plug current.focus (current.ancestors ++ [.right left value]) = _
      rw [plug_append]
      change Source.fork value left current.tree = _
      rw [treeEq]

theorem root_not_mem_smaller_focus (identify : ρ → ι) (child parent : Cursor α ρ)
    (sameTree : child.tree = parent.tree) (unique : (child.tree.inventory identify).Nodup)
    (smaller : child.focus.shape.leaves.length < parent.focus.shape.leaves.length) :
    identify parent.focus.rootRecord ∉ child.focus.inventory identify := by
  intro member
  simp only [Source.inventory] at member
  obtain ⟨record,recordPresent,recordId⟩ := Multiset.mem_map.mp member
  have recordMember : record ∈ child.focus.inventory id := by
    simpa only [Source.inventory,Multiset.map_id] using recordPresent
  obtain ⟨inside,insideTree,insideRoot⟩ := cursor_of_record child.focus record recordMember
  let actual : Cursor α ρ := ⟨inside.focus,inside.ancestors ++ child.ancestors⟩
  have actualTree : actual.tree = child.tree := by
    change plug inside.focus (inside.ancestors ++ child.ancestors) = _
    rw [plug_append]
    change plug inside.tree child.ancestors = _
    rw [insideTree]
    rfl
  have sameId : identify actual.focus.rootRecord = identify parent.focus.rootRecord :=
    (congrArg identify insideRoot).trans recordId
  have equal := cursors_eq_of_label identify actual parent (actualTree.trans sameTree)
    (actualTree.symm ▸ unique) sameId
  have atMost := leaves_le_plug inside.focus inside.ancestors
  change inside.focus.shape.leaves.length ≤ inside.tree.shape.leaves.length at atMost
  rw [insideTree] at atMost
  have lengths := congrArg (fun current : Cursor α ρ => current.focus.shape.leaves.length) equal
  change inside.focus.shape.leaves.length = parent.focus.shape.leaves.length at lengths
  omega

theorem root_not_mem_disjoint_focus (identify : ρ → ι) (child other : Cursor α ρ)
    (sameTree : child.tree = other.tree) (unique : (child.tree.inventory identify).Nodup)
    (separate : ∀ key, key ∈ child.focus.shape.leaves → key ∈ other.focus.shape.leaves → False) :
    identify other.focus.rootRecord ∉ child.focus.inventory identify := by
  intro member
  simp only [Source.inventory] at member
  obtain ⟨record,recordPresent,recordId⟩ := Multiset.mem_map.mp member
  have recordMember : record ∈ child.focus.inventory id := by
    simpa only [Source.inventory,Multiset.map_id] using recordPresent
  obtain ⟨inside,insideTree,insideRoot⟩ := cursor_of_record child.focus record recordMember
  let actual : Cursor α ρ := ⟨inside.focus,inside.ancestors ++ child.ancestors⟩
  have actualTree : actual.tree = child.tree := by
    change plug inside.focus (inside.ancestors ++ child.ancestors) = _
    rw [plug_append]
    change plug inside.tree child.ancestors = _
    rw [insideTree]
    rfl
  have sameId : identify actual.focus.rootRecord = identify other.focus.rootRecord :=
    (congrArg identify insideRoot).trans recordId
  have equal := cursors_eq_of_label identify actual other (actualTree.trans sameTree)
    (actualTree.symm ▸ unique) sameId
  have leaves : inside.focus.shape.leaves = other.focus.shape.leaves := by
    have actualLeaves := congrArg (fun current : Cursor α ρ => current.focus.shape.leaves) equal
    change inside.focus.shape.leaves = other.focus.shape.leaves at actualLeaves
    exact actualLeaves
  have inclusion : ∀ key ∈ inside.focus.shape.leaves, key ∈ child.focus.shape.leaves := by
    intro key present
    rw [← insideTree]
    change key ∈ (plug inside.focus inside.ancestors).shape.leaves
    rw [leaves_decomposition]
    exact List.mem_append_left _ (List.mem_append_right _ present)
  cases word : inside.focus.shape.leaves with
  | nil =>
    have length := inside.focus.inorderLabels_length (fun _ => ())
    rw [word,List.length_nil] at length
    omega
  | cons key rest =>
    have present : key ∈ inside.focus.shape.leaves := by rw [word]; exact List.mem_cons_self
    exact separate key (inclusion key present) (leaves ▸ present)

theorem retained_payload_ids (old actual : Cursor α ((ι × ρ) × μ)) (oldPacket freshPacket : ρ)
    (equal : (replacePayload (old.mapRecords Prod.fst) oldPacket).focus =
      (replacePayload (actual.mapRecords Prod.fst) freshPacket).focus) :
    actual.focus.inventory (fun record => record.1.1) = old.focus.inventory (fun record => record.1.1) := by
  have inventory := congrArg (Source.inventory Prod.fst) equal
  have oldIds := Source.inventory_setRoot Prod.fst (old.focus.mapRecords Prod.fst)
    ((old.focus.mapRecords Prod.fst).rootRecord.1,oldPacket) rfl
  have actualIds := Source.inventory_setRoot Prod.fst (actual.focus.mapRecords Prod.fst)
    ((actual.focus.mapRecords Prod.fst).rootRecord.1,freshPacket) rfl
  change ((old.focus.mapRecords Prod.fst).setRoot _).inventory Prod.fst =
    ((actual.focus.mapRecords Prod.fst).setRoot _).inventory Prod.fst at inventory
  simp only [Cursor.mapRecords] at inventory
  rw [oldIds,actualIds] at inventory
  simpa only [mapRecords_inventory,Function.comp_def] using inventory.symm

/-- Geometric separation from an operated root: the payload is smaller
than that component, or their original-key leaves are disjoint. -/
def PayloadSeparated (payload : Source α ρ) (root : Cursor α ((ι × ρ) × μ)) : Prop :=
  payload.shape.leaves.length < root.focus.shape.leaves.length ∨
    ∀ key, key ∈ payload.shape.leaves → key ∈ root.focus.shape.leaves → False

/-- A two-component phase protects an entire retained payload. Each
changed root is an actual final component root; proper containment or
disjointness supplies its exclusion. This avoids exposing an unexplained
list of cache exceptions to the global invariant. -/
theorem MetadataFrame.protect_retained_payload_pair
    {before after : Source α ((ι × ρ) × μ)}
    (first second : Cursor α ((ι × ρ) × μ)) (firstTree : first.tree = after) (secondTree : second.tree = after)
    (frame : MetadataFrame Prod.fst [first.focus.rootRecord.1.1,second.focus.rootRecord.1.1] before after)
    (leafWord : before.shape.leaves = after.shape.leaves)
    (order : after.inorderLabels (fun record => record.1.1) = before.inorderLabels (fun record => record.1.1))
    (distinct : before.shape.leaves.Nodup)
    (unique : (after.inventory (fun record => record.1.1)).Nodup)
    (old : Cursor α ((ι × ρ) × μ)) (oldTree : old.tree = before)
    (view : Cursor α ρ) (viewTree : view.tree = (after.mapRecords Prod.fst).mapRecords Prod.snd)
    (oldPacket freshPacket : ρ)
    (retained : ((old.focus.mapRecords Prod.fst).mapRecords Prod.snd).setRoot oldPacket =
      view.focus.setRoot freshPacket)
    (firstSeparated : PayloadSeparated view.focus first)
    (secondSeparated : PayloadSeparated view.focus second) :
    Protects Prod.fst (fun ident => ident ∈ old.focus.inventory (fun record => record.1.1)) before after := by
  obtain ⟨actual,actualTree,actualErases,_,payloadEqual⟩ :=
    retained_payload_ghost leafWord order distinct old oldTree view viewTree oldPacket freshPacket retained
  have childLeaves : actual.focus.shape.leaves = view.focus.shape.leaves := by
    simpa only [Cursor.mapRecords,Source.mapRecords_shape] using
      congrArg (fun current : Cursor α ρ => current.focus.shape.leaves) actualErases
  have excludes (root : Cursor α ((ι × ρ) × μ)) (rootTree : root.tree = after)
      (separated : PayloadSeparated view.focus root) :
      root.focus.rootRecord.1.1 ∉ old.focus.inventory (fun record => record.1.1) := by
    have output : root.focus.rootRecord.1.1 ∉ actual.focus.inventory (fun record => record.1.1) := by
      rcases separated with smaller | disjoint
      · apply root_not_mem_smaller_focus (fun record => record.1.1) actual root
          (actualTree.trans rootTree.symm) (actualTree.symm ▸ unique)
        rw [childLeaves]
        exact smaller
      · apply root_not_mem_disjoint_focus (fun record => record.1.1) actual root
          (actualTree.trans rootTree.symm) (actualTree.symm ▸ unique)
        rw [childLeaves]
        exact disjoint
    rw [retained_payload_ids old actual oldPacket freshPacket payloadEqual] at output
    exact output
  apply frame.protect
  intro ident guarded changed
  simp only [List.mem_cons,List.not_mem_nil,or_false] at changed
  rcases changed with firstId | secondId
  · exact excludes first firstTree firstSeparated (firstId ▸ guarded)
  · exact excludes second secondTree secondSeparated (secondId ▸ guarded)

/-- Every physical vertex of the retained payload lies outside the
single cache refresh. In particular, this includes roots of arbitrarily
many descendant components without adding any runtime fingers. -/
theorem MetadataFrame.protect_proper_payload_inventory
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
    changed ∉ old.focus.inventory (fun record => record.1.1) ∧
      Protects Prod.fst (fun ident => ident ∈ old.focus.inventory (fun record => record.1.1)) before after := by
  obtain ⟨actual,actualTree,actualErases,_,payloadEqual⟩ :=
    retained_payload_ghost leafWord order distinct old oldTree view viewTree oldPacket freshPacket retained
  have childLeaves : actual.focus.shape.leaves = view.focus.shape.leaves := by
    simpa only [Cursor.mapRecords,Source.mapRecords_shape] using
      congrArg (fun current : Cursor α ρ => current.focus.shape.leaves) actualErases
  have parentLeaves : parent.focus.shape.leaves = (plug view.focus inside).shape.leaves := by
    simpa only [Source.mapRecords_shape] using
      congrArg (fun tree : Source α ρ => tree.shape.leaves) parentView
  have smaller : actual.focus.shape.leaves.length < parent.focus.shape.leaves.length := by
    rw [childLeaves,parentLeaves]
    exact proper_leaves_lt view.focus inside proper
  have excluded := root_not_mem_smaller_focus (fun record => record.1.1) actual parent
    (actualTree.trans parentTree.symm) (actualTree.symm ▸ unique) smaller
  rw [parentId,retained_payload_ids old actual oldPacket freshPacket payloadEqual] at excluded
  refine ⟨excluded,frame.protect ?_⟩
  intro ident guarded member
  have equality := List.mem_singleton.mp member
  exact excluded (equality ▸ guarded)

end TangoSquared.Paper20261030.HeadCacheFrame
