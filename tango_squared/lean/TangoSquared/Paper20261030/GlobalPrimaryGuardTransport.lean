import TangoSquared.Paper20261030.GlobalPrimaryProtectedUpdate

set_option autoImplicit false

/-! The protected endpoint-root identifiers remain the same identifiers
after a local phase. This permits physical cache frames stated at
successive actual trees to compose using `Protects.mono` and
`Protects.trans`. The proof transports canonical ghost occurrences;
it does not add fingers to the runtime configuration. -/

namespace TangoSquared.Paper20261030.GlobalPrimaryRepresentation

open ColoredStorage SourcePointer Structural MultiSourceProgram
open PreferredProjection PrimaryWings Secondary SecondaryDecomposition

variable {α η : Type*} [DecidableEq α] [DecidableEq η]

theorem Nested.untouched_ids_transport {height headerKey : Nat} {rank : α → Int}
    {reference : DepthTree 0 height} {oldPrimary primary : PrefRouter α}
    {perfect : primary.Perfect height} {memory : MemoryKey → Bool}
    {oldData data : α → ComponentData α η} {before after : Source α (Cell η)} {oldNext next : α}
    (nested : Nested headerKey rank primary data)
    (logical : LogicalInvariant reference primary perfect memory data)
    (distinct : primary.leaves.Nodup)
    (root : (after.mapRecords Prod.fst).mapRecords Prod.snd = (data primary.terminal).config.tree)
    (frame : HeadCacheFrame.Protects Prod.fst (UntouchedIds oldPrimary oldData before oldNext) before after)
    (leafWord : before.shape.leaves = after.shape.leaves)
    (order : after.inorderLabels (fun record => record.1.1) = before.inorderLabels (fun record => record.1.1))
    (beforeDistinct : before.shape.leaves.Nodup)
    (endpoints : (primary.terminal = oldPrimary.terminal ∧ next = oldNext) ∨
      (primary.terminal = oldNext ∧ next = oldPrimary.terminal))
    (transfer : ∀ {start subtree}, ComponentRoot oldPrimary start subtree →
      subtree.terminal ≠ oldPrimary.terminal → subtree.terminal ≠ oldNext →
      ∃ freshStart, ComponentRoot primary freshStart subtree)
    (unchanged : ∀ key, key ≠ oldPrimary.terminal → key ≠ oldNext → data key = oldData key) :
    ∀ ident, UntouchedIds oldPrimary oldData before oldNext ident →
      UntouchedIds primary data after next ident := by
  intro ident covered
  obtain ⟨start,subtree,oldRoot,notOld,notNext,current,currentTree,currentStored,identity⟩ := covered
  obtain ⟨freshStart,freshRoot⟩ := transfer oldRoot notOld notNext
  have notActive : subtree.terminal ≠ primary.terminal := by
    rcases endpoints with ⟨activeEq,_⟩ | ⟨activeEq,_⟩
    · rwa [activeEq]
    · rwa [activeEq]
  have notOther : subtree.terminal ≠ next := by
    rcases endpoints with ⟨_,nextEq⟩ | ⟨_,nextEq⟩
    · rwa [nextEq]
    · rwa [nextEq]
  have unchangedData := unchanged subtree.terminal notOld notNext
  have occurrence : ErasedOccurrence (oldData subtree.terminal)
      ((after.mapRecords Prod.fst).mapRecords Prod.snd) := by
    rw [root]
    rw [← unchangedData]
    exact nested.erased_occurs reference perfect distinct memory data logical freshRoot
  have guarded : UntouchedIds oldPrimary oldData before oldNext current.focus.rootRecord.1.1 :=
    ⟨start,subtree,oldRoot,notOld,notNext,current,currentTree,currentStored,rfl⟩
  obtain ⟨actual,actualTree,stored,sameId⟩ := currentStored.transport_protected (oldData subtree.terminal)
    current currentTree occurrence frame guarded leafWord order beforeDistinct
  refine ⟨freshStart,subtree,freshRoot,notActive,notOther,actual,actualTree,?_,identity.trans sameId.symm⟩
  rw [unchangedData]
  exact stored

end TangoSquared.Paper20261030.GlobalPrimaryRepresentation
