import ChaCha.Paper20261030.GlobalPrimaryOccurrences
import ChaCha.Paper20261030.HeadCacheFramePayload

set_option autoImplicit false

/-! Stored component headers are transported to ghost canonical output
occurrences. For a source operation that refreshes one root, a proper
output occurrence proves the root-id exclusion; it is not an assumption.
These lemmas do not move or allocate any runtime finger. -/

namespace ChaCha.Paper20261030.GlobalPrimaryRepresentation

open ColoredStorage SourcePointer Structural SourcePositions MultiSourceProgram

variable {α η : Type*} [DecidableEq α] [DecidableEq η]

theorem StoredAt.normalized (data : ComponentData α η) (current : Cursor α (Cell η))
    (stored : StoredAt data current) :
    ((current.focus.mapRecords Prod.fst).mapRecords Prod.snd).setRoot data.config.tree.rootRecord =
      data.config.tree := by
  obtain ⟨saved,view⟩ := stored.2
  rw [view]
  cases data.config.tree <;> rfl

theorem StoredAt.transport {before after : Source α (Cell η)} {changed : List Nat}
    (data : ComponentData α η) (old : Cursor α (Cell η)) (oldTree : old.tree = before)
    (stored : StoredAt data old)
    (occurrence : ErasedOccurrence data ((after.mapRecords Prod.fst).mapRecords Prod.snd))
    (frame : HeadCacheFrame.MetadataFrame Prod.fst changed before after)
    (leafWord : before.shape.leaves = after.shape.leaves)
    (order : after.inorderLabels (fun record => record.1.1) = before.inorderLabels (fun record => record.1.1))
    (distinct : before.shape.leaves.Nodup) (outside : old.focus.rootRecord.1.1 ∉ changed) :
    ∃ actual : Cursor α (Cell η), actual.tree = after ∧ StoredAt data actual ∧
      actual.focus.rootRecord.1.1 = old.focus.rootRecord.1.1 := by
  obtain ⟨saved,ancestors,whole⟩ := occurrence
  let view : Cursor α (Packet η) := ⟨data.config.tree.setRoot (saved ++ data.config.tree.rootRecord),ancestors⟩
  have viewTree : view.tree = (after.mapRecords Prod.fst).mapRecords Prod.snd := whole.symm
  have normalized : view.focus.setRoot data.config.tree.rootRecord = data.config.tree := by
    change (data.config.tree.setRoot _).setRoot _ = _
    cases data.config.tree <;> rfl
  obtain ⟨actual,actualTree,erases,identity,cache,_⟩ := frame.retained_payload leafWord order distinct
    old oldTree view viewTree data.config.tree.rootRecord data.config.tree.rootRecord
    ((stored.normalized data old).trans normalized.symm) outside
  refine ⟨actual,actualTree,⟨cache.trans stored.1,saved,?_⟩,identity⟩
  exact congrArg Cursor.focus erases

/-- Proper containment in the operated component excludes its refreshed
root. This is the directly usable singleton-phase cache frame. -/
theorem StoredAt.transport_proper {before after : Source α (Cell η)}
    (data : ComponentData α η) (old : Cursor α (Cell η)) (oldTree : old.tree = before)
    (stored : StoredAt data old) (parent : Cursor α (Cell η)) (parentTree : parent.tree = after)
    (saved : Packet η) (inside : List (Frame α (Packet η))) (proper : inside ≠ [])
    (parentView : (parent.focus.mapRecords Prod.fst).mapRecords Prod.snd =
      plug (data.config.tree.setRoot (saved ++ data.config.tree.rootRecord)) inside)
    (frame : HeadCacheFrame.MetadataFrame Prod.fst [parent.focus.rootRecord.1.1] before after)
    (leafWord : before.shape.leaves = after.shape.leaves)
    (order : after.inorderLabels (fun record => record.1.1) = before.inorderLabels (fun record => record.1.1))
    (distinct : before.shape.leaves.Nodup) (unique : (after.inventory (fun record => record.1.1)).Nodup) :
    ∃ actual : Cursor α (Cell η), actual.tree = after ∧ StoredAt data actual ∧
      actual.focus.rootRecord.1.1 = old.focus.rootRecord.1.1 ∧
      old.focus.rootRecord.1.1 ≠ parent.focus.rootRecord.1.1 := by
  let rawParent := (parent.mapRecords Prod.fst).mapRecords Prod.snd
  let view : Cursor α (Packet η) :=
    ⟨data.config.tree.setRoot (saved ++ data.config.tree.rootRecord),inside ++ rawParent.ancestors⟩
  have viewTree : view.tree = (after.mapRecords Prod.fst).mapRecords Prod.snd := by
    change plug _ (inside ++ rawParent.ancestors) = _
    rw [plug_append,← parentView]
    change rawParent.tree = _
    rw [Cursor.mapRecords_tree,Cursor.mapRecords_tree,parentTree]
  have normalized : view.focus.setRoot data.config.tree.rootRecord = data.config.tree := by
    change (data.config.tree.setRoot _).setRoot _ = _
    cases data.config.tree <;> rfl
  obtain ⟨actual,actualTree,erases,identity,excluded,cache,_⟩ := frame.retained_proper_payload
    parent.focus.rootRecord.1.1 leafWord order distinct unique old oldTree view viewTree
    data.config.tree.rootRecord data.config.tree.rootRecord ((stored.normalized data old).trans normalized.symm)
    parent parentTree rfl inside proper parentView
  refine ⟨actual,actualTree,⟨cache.trans stored.1,saved,?_⟩,identity,excluded⟩
  exact congrArg Cursor.focus erases

end ChaCha.Paper20261030.GlobalPrimaryRepresentation
