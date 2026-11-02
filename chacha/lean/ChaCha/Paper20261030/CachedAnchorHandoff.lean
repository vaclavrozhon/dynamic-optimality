import ChaCha.Paper20261030.CachedRootMetadataAssociation
import ChaCha.Paper20261030.CursorRepresentationShapes

set_option autoImplicit false

namespace ChaCha.Paper20261030.MultiSourceSingleCursor

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram

variable {α ρ τ F : Type*} [DecidableEq F]

theorem Represents.mapRecords (erase : ρ → τ) {finger : F} {current : Cursor α ρ}
    {config : Configuration F α ρ} (positioned : Represents finger current config) :
    Represents finger (current.mapRecords erase) (config.mapRecords erase) := by
  constructor
  · change config.tree.mapRecords erase = (current.mapRecords erase).tree
    rw [positioned.1,Cursor.mapRecords_tree]
  · simpa only [Configuration.mapRecords,address_mapRecords] using positioned.2

end ChaCha.Paper20261030.MultiSourceSingleCursor

/-! Lifting a reached payload through the cache field. Once its physical
identifier is retained and differs from the refreshed component root,
the actual reached cache is exactly its original cache. -/

namespace ChaCha.Paper20261030.CachedRootOperation

open ColoredStorage SourcePointer Structural MultiSourceProgram

variable {α ρ ι μ F : Type*} [DecidableEq F]

theorem retained_anchor (identify : ρ → ι) (changed : ι)
    (before after : Configuration F α (ρ × μ)) (kept : RetainedMetadata identify changed before.tree after.tree)
    (finger : F) (current : Cursor α (ρ × μ))
    (positioned : MultiSourceSingleCursor.Represents finger current before)
    (target : Cursor α ρ) (returned : MultiSourceSingleCursor.Represents finger target (after.mapRecords Prod.fst))
    (sameId : identify target.focus.rootRecord = identify current.focus.rootRecord.1)
    (different : identify target.focus.rootRecord ≠ changed) :
    ∃ actual : Cursor α (ρ × μ), MultiSourceSingleCursor.Represents finger actual after ∧
      actual.mapRecords Prod.fst = target ∧ actual.focus.rootRecord.2 = current.focus.rootRecord.2 := by
  obtain ⟨actual,located,erases⟩ := MultiSourceSingleCursor.lift_represents Prod.fst finger target after returned
  have oldMember : current.focus.rootRecord ∈ before.tree.inventory id := by
    rw [positioned.1]
    exact Multiset.mem_of_le (inventory_le_plug id current.focus current.ancestors) (root_mem_inventory id current.focus)
  have freshMember : actual.focus.rootRecord ∈ after.tree.inventory id := by
    rw [located.1]
    exact Multiset.mem_of_le (inventory_le_plug id actual.focus actual.ancestors) (root_mem_inventory id actual.focus)
  have actualId : identify actual.focus.rootRecord.1 = identify target.focus.rootRecord := by
    simpa only [Cursor.mapRecords,Source.mapRecords_root] using
      congrArg (fun cursor : Cursor α ρ => identify cursor.focus.rootRecord) erases
  exact ⟨actual,located,erases,kept _ oldMember _ freshMember (actualId.trans sameId)
    (fun equal => different (sameId.trans equal))⟩

end ChaCha.Paper20261030.CachedRootOperation
