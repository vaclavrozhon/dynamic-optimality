import TangoSquared.Paper20261030.GlobalPrimaryPairProtection

set_option autoImplicit false

/-! A head phase with the actual two final root writes preserves the
complete global representation. The cache protection needed by the
general composed-frame theorem is derived here from the output layout.
Multi-phase programs can instead compose the individual protections. -/

namespace TangoSquared.Paper20261030.GlobalPrimaryRepresentation

open ColoredStorage SourcePointer Structural MultiSourceProgram
open PreferredProjection PrimaryWings Secondary SecondaryDecomposition

variable {α η F : Type*} [DecidableEq α] [DecidableEq η]

theorem Maintained.head_pair_outputs [DecidableEq F] {height d : Nat} {markerId headerKey : Nat}
    {rank : α → Int} {reference : DepthTree 0 height} {primary successor : PrefRouter α}
    {x : α} (step : PrefRouter.HeadStep x d primary successor)
    {perfect : primary.Perfect height} {memory : MemoryKey → Bool} {data : α → ComponentData α η}
    {before after : Configuration F α (Cell η)}
    (valid : Maintained markerId headerKey rank reference primary perfect memory data before)
    (dormant active : ComponentData α η) (nextMemory : MemoryKey → Bool)
    (logical : LogicalInvariant reference successor (step.perfect perfect) nextMemory
      (Function.update (Function.update data primary.terminal dormant) successor.terminal active))
    (nested : Nested headerKey rank successor
      (Function.update (Function.update data primary.terminal dormant) successor.terminal active))
    (root : (after.tree.mapRecords Prod.fst).mapRecords Prod.snd = active.config.tree)
    (activeCache : after.tree.rootRecord.2 = some active.header)
    (dormantRoot : Cursor α (Cell η)) (dormantTree : dormantRoot.tree = after.tree)
    (dormantStored : StoredAt dormant dormantRoot)
    (physical : CanonicalComponentUniqueness.Valid markerId (after.mapRecords Prod.fst).tree)
    (reserved : markerId ∉ (after.mapRecords Prod.fst).tree.inventory Prod.fst)
    (wellFormed : WellFormed after)
    (order : after.tree.inorderLabels (fun record => record.1.1) = before.tree.inorderLabels (fun record => record.1.1))
    (frame : HeadCacheFrame.MetadataFrame Prod.fst
      [after.tree.rootRecord.1.1,dormantRoot.focus.rootRecord.1.1] before.tree after.tree) :
    Maintained markerId headerKey rank reference successor (step.perfect perfect) nextMemory
      (Function.update (Function.update data primary.terminal dormant) successor.terminal active) after := by
  let updated := Function.update (Function.update data primary.terminal dormant) successor.terminal active
  have different := step.endpoints_ne valid.distinct
  have distinct : successor.leaves.Nodup := by rw [step.leaves]; exact valid.distinct
  obtain ⟨common,old,incoming,side,length,oldEnd,_,_,afterWord⟩ := head_exit_decomposition step
  let exit : Exit α := ⟨!side,old⟩
  have present : portAt 0 (exits successor) d = some exit := by
    rw [afterWord,← length,PrimaryWings.portAt_boundary]
  have rootView : (after.tree.mapRecords Prod.fst).mapRecords Prod.snd =
      (updated successor.terminal).config.tree := by
    simpa only [updated,Function.update_self] using root
  have afterLeaves : after.tree.shape.leaves = successor.leaves := by
    have shapes := congrArg (fun tree : Source α (Packet η) => tree.shape.leaves) rootView
    simp only [Source.mapRecords_shape] at shapes
    exact shapes.trans (nested.original_keys reference (step.perfect perfect) distinct nextMemory updated logical .root)
  have leafWord : before.tree.shape.leaves = after.tree.shape.leaves := by
    rw [valid.original_keys,afterLeaves,step.leaves]
  have beforeDistinct : before.tree.shape.leaves.Nodup := valid.original_keys.symm ▸ valid.distinct
  have unique : (after.tree.inventory (fun record => record.1.1)).Nodup := by
    simpa only [Configuration.mapRecords,mapRecords_inventory,Function.comp_def] using physical.2.2
  have secondStored : StoredAt (updated exit.subtree.terminal) dormantRoot := by
    change StoredAt (updated old.terminal) dormantRoot
    simpa only [updated,← oldEnd,Function.update_of_ne different,Function.update_self] using dormantStored
  have protection := nested.protect_pair logical distinct exit present rootView dormantRoot dormantTree secondStored
    frame leafWord order beforeDistinct unique (Or.inr ⟨rfl,oldEnd.symm⟩)
    (fun rooted notOld notNext => ⟨_,rooted.head_other step notOld notNext⟩)
    (fun key notOld notNext => head_data_untouched data _ _ key dormant active notOld notNext)
  exact valid.head_outputs step dormant active nextMemory logical nested root activeCache dormantRoot dormantTree
    dormantStored physical reserved wellFormed order protection

end TangoSquared.Paper20261030.GlobalPrimaryRepresentation
