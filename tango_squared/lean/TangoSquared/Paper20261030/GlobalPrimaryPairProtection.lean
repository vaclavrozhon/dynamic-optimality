import TangoSquared.Paper20261030.GlobalPrimaryProtectedUpdate
import TangoSquared.Paper20261030.GlobalPrimarySeparation

set_option autoImplicit false

/-! A concrete two-root source phase protects every untouched component.
The two changed physical ids are actual output roots: the whole active
component and one immediate primary exit. Proper containment or disjoint
original-key leaf sets derive every required exclusion. -/

namespace TangoSquared.Paper20261030.GlobalPrimaryRepresentation

open ColoredStorage SourcePointer Structural SourcePositions SubtreeMetadata MultiSourceProgram
open PreferredProjection PrimaryWings Secondary SecondaryDecomposition

variable {α η : Type*} [DecidableEq α] [DecidableEq η]

/-- The topology hypotheses describe only the two endpoint replacements.
For an unchanged primary shape, `transfer` is the identity; for a head
exchange it is `ComponentRoot.head_other`. Neither case assumes cache
preservation or successful completion of an access. -/
theorem Nested.protect_pair {height headerKey depth : Nat} {rank : α → Int}
    {reference : DepthTree 0 height} {oldPrimary primary : PrefRouter α}
    {perfect : primary.Perfect height} {memory : MemoryKey → Bool}
    {oldData data : α → ComponentData α η} {before after : Source α (Cell η)} {next : α}
    (nested : Nested headerKey rank primary data)
    (logical : LogicalInvariant reference primary perfect memory data)
    (distinct : primary.leaves.Nodup) (exit : Exit α)
    (present : portAt 0 (exits primary) depth = some exit)
    (root : (after.mapRecords Prod.fst).mapRecords Prod.snd = (data primary.terminal).config.tree)
    (second : Cursor α (Cell η)) (secondTree : second.tree = after)
    (secondStored : StoredAt (data exit.subtree.terminal) second)
    (frame : HeadCacheFrame.MetadataFrame Prod.fst [after.rootRecord.1.1,second.focus.rootRecord.1.1] before after)
    (leafWord : before.shape.leaves = after.shape.leaves)
    (order : after.inorderLabels (fun record => record.1.1) = before.inorderLabels (fun record => record.1.1))
    (beforeDistinct : before.shape.leaves.Nodup)
    (unique : (after.inventory (fun record => record.1.1)).Nodup)
    (endpoints : (primary.terminal = oldPrimary.terminal ∧ exit.subtree.terminal = next) ∨
      (primary.terminal = next ∧ exit.subtree.terminal = oldPrimary.terminal))
    (transfer : ∀ {start subtree}, ComponentRoot oldPrimary start subtree →
      subtree.terminal ≠ oldPrimary.terminal → subtree.terminal ≠ next →
      ∃ freshStart, ComponentRoot primary freshStart subtree)
    (unchanged : ∀ key, key ≠ oldPrimary.terminal → key ≠ next → data key = oldData key) :
    HeadCacheFrame.Protects Prod.fst (UntouchedIds oldPrimary oldData before next) before after := by
  have wholeLeaves : after.shape.leaves = primary.leaves := by
    have shapes := congrArg (fun tree : Source α (Packet η) => tree.shape.leaves) root
    simp only [Source.mapRecords_shape] at shapes
    exact shapes.trans (nested.original_keys reference perfect distinct memory data logical .root)
  have secondRoot : ComponentRoot primary (depth+1) exit.subtree := by
    simpa only [Nat.zero_add] using ComponentRoot.child (.root : ComponentRoot primary 0 primary) present
  have secondLeaves : second.focus.shape.leaves = exit.subtree.leaves :=
    (secondStored.leaves _ _).trans
      (nested.original_keys reference perfect distinct memory data logical secondRoot)
  refine ⟨frame.ids,?_⟩
  intro oldRecord oldMember covered freshRecord freshMember same
  obtain ⟨start,subtree,oldRoot,notOld,notNext,current,currentTree,currentStored,identity⟩ := covered
  obtain ⟨freshStart,freshRoot⟩ := transfer oldRoot notOld notNext
  have notActive : subtree.terminal ≠ primary.terminal := by
    rcases endpoints with ⟨activeEq,_⟩ | ⟨activeEq,_⟩
    · rwa [activeEq]
    · rwa [activeEq]
  have notExit : subtree.terminal ≠ exit.subtree.terminal := by
    rcases endpoints with ⟨_,exitEq⟩ | ⟨_,exitEq⟩
    · rwa [exitEq]
    · rwa [exitEq]
  have unchangedData := unchanged subtree.terminal notOld notNext
  obtain ⟨saved,ancestors,occurs⟩ := nested.erased_occurs reference perfect distinct memory data logical freshRoot
  let view : Cursor α (Packet η) :=
    ⟨(data subtree.terminal).config.tree.setRoot (saved ++ (data subtree.terminal).config.tree.rootRecord),ancestors⟩
  have viewTree : view.tree = (after.mapRecords Prod.fst).mapRecords Prod.snd := occurs.symm.trans root.symm
  have viewLeaves : view.focus.shape.leaves = subtree.leaves := by
    change ((data subtree.terminal).config.tree.setRoot _).shape.leaves = _
    rw [source_setRoot_shape]
    exact nested.original_keys reference perfect distinct memory data logical freshRoot
  have normalized : view.focus.setRoot (data subtree.terminal).config.tree.rootRecord =
      (data subtree.terminal).config.tree := by
    change ((data subtree.terminal).config.tree.setRoot _).setRoot _ = _
    cases (data subtree.terminal).config.tree <;> rfl
  have retained : ((current.focus.mapRecords Prod.fst).mapRecords Prod.snd).setRoot
      (data subtree.terminal).config.tree.rootRecord =
        view.focus.setRoot (data subtree.terminal).config.tree.rootRecord := by
    rw [normalized,unchangedData]
    exact currentStored.normalized _ _
  have firstSeparated : HeadCacheFrame.PayloadSeparated view.focus (⟨after,[]⟩ : Cursor α (Cell η)) := by
    apply Or.inl
    change view.focus.shape.leaves.length < after.shape.leaves.length
    rw [viewLeaves,wholeLeaves]
    exact freshRoot.proper_leaves_lt notActive
  have secondSeparated : HeadCacheFrame.PayloadSeparated view.focus second := by
    unfold HeadCacheFrame.PayloadSeparated
    rw [viewLeaves,secondLeaves]
    exact freshRoot.separated_from_exit distinct exit present notActive notExit
  have protection := frame.protect_retained_payload_pair ⟨after,[]⟩ second rfl secondTree leafWord order
    beforeDistinct unique current currentTree view viewTree (data subtree.terminal).config.tree.rootRecord
    (data subtree.terminal).config.tree.rootRecord retained firstSeparated secondSeparated
  apply protection.retained oldRecord oldMember ?_ freshRecord freshMember same
  rw [identity]
  exact root_mem_inventory _ _

end TangoSquared.Paper20261030.GlobalPrimaryRepresentation
