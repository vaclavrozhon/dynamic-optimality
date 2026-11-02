import ChaCha.Paper20261030.HeadCacheFramePayload

set_option autoImplicit false

/-! The actual cursor reached by a local route receives the old payload
cache. The old payload occurrence is ghost data, so no parked incoming
finger is required as an input to the runtime controller. -/

namespace ChaCha.Paper20261030.HeadCacheFrame

open ColoredStorage SourcePointer SourcePositions

variable {α ρ ι μ : Type*}

theorem cursors_eq_of_erased {σ : Type*} (erase : ρ → σ) (first second : Cursor α ρ)
    (sameTree : first.tree = second.tree) (sameView : first.mapRecords erase = second.mapRecords erase) :
    first = second := by
  apply eq_of_tree_address first second sameTree
  have addressEq := congrArg address sameView
  simpa only [address_mapRecords] using addressEq

/-- Payload transport identifies the ghost reconstructed occurrence with
an independently reached actual cursor, using its erased address. -/
theorem MetadataFrame.retained_reached_payload
    {before after : Source α ((ι × ρ) × μ)} (changed : ι)
    (frame : MetadataFrame Prod.fst [changed] before after)
    (leafWord : before.shape.leaves = after.shape.leaves)
    (order : after.inorderLabels (fun record => record.1.1) = before.inorderLabels (fun record => record.1.1))
    (distinct : before.shape.leaves.Nodup)
    (unique : (after.inventory (fun record => record.1.1)).Nodup)
    (old : Cursor α ((ι × ρ) × μ)) (oldTree : old.tree = before)
    (reached : Cursor α ((ι × ρ) × μ)) (reachedTree : reached.tree = after)
    (oldPacket freshPacket : ρ)
    (retained : ((old.focus.mapRecords Prod.fst).mapRecords Prod.snd).setRoot oldPacket =
      ((reached.focus.mapRecords Prod.fst).mapRecords Prod.snd).setRoot freshPacket)
    (parent : Cursor α ((ι × ρ) × μ)) (parentTree : parent.tree = after)
    (parentId : parent.focus.rootRecord.1.1 = changed)
    (inside : List (Frame α ρ)) (proper : inside ≠ [])
    (parentView : (parent.focus.mapRecords Prod.fst).mapRecords Prod.snd =
      plug ((reached.focus.mapRecords Prod.fst).mapRecords Prod.snd) inside) :
    reached.focus.rootRecord.1.1 = old.focus.rootRecord.1.1 ∧
      old.focus.rootRecord.1.1 ≠ changed ∧
      reached.focus.rootRecord.2 = old.focus.rootRecord.2 ∧
      (SubtreeMetadata.replacePayload (old.mapRecords Prod.fst) oldPacket).focus =
        (SubtreeMetadata.replacePayload (reached.mapRecords Prod.fst) freshPacket).focus := by
  let view := (reached.mapRecords Prod.fst).mapRecords Prod.snd
  have viewTree : view.tree = (after.mapRecords Prod.fst).mapRecords Prod.snd := by
    rw [Cursor.mapRecords_tree,Cursor.mapRecords_tree,reachedTree]
  obtain ⟨actual,actualTree,actualErases,identity,excluded,cache,payload⟩ :=
    MetadataFrame.retained_proper_payload changed frame leafWord order distinct unique old oldTree
      view viewTree oldPacket freshPacket retained parent parentTree parentId inside proper parentView
  have actualSame : actual = reached := by
    apply eq_of_tree_address actual reached (actualTree.trans reachedTree.symm)
    have same := congrArg address actualErases
    simpa only [view,address_mapRecords] using same
  subst actual
  exact ⟨identity,excluded,cache,payload⟩

end ChaCha.Paper20261030.HeadCacheFrame
