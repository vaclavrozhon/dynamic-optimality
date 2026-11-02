import ChaCha.Paper20261030.MultiSourceRecordMap
import ChaCha.Paper20261030.MultiSourceService

/-! A reached leaf after record erasure is the same actual key leaf.
Appending the physical read therefore provides service even when extra
primary metadata decorates every vertex.
-/

namespace ChaCha.Paper20261030.ReadCompletionController

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram

variable {α ρ τ F σ : Type*} [DecidableEq F]

theorem serve_mapped (source : Program σ F ρ) (finger : F) {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost) (eraseRecord : ρ → τ)
    (key : α) (record : τ) (position : List Bool) (outside : List (Frame α τ))
    (present : after.fingers finger = some position)
    (reached : locate (after.tree.mapRecords eraseRecord) position = some ⟨.leaf key record,outside⟩) :
    ∃ actualRecord, Serves (program source finger) key (some state) before none after
      (reads++[(finger,actualRecord)]) (cost+1) := by
  obtain ⟨current,found,same⟩ := lift_locate eraseRecord after.tree position _ reached
  have erasedFocus := congrArg Cursor.focus same
  have focus : current.focus = .leaf key current.focus.rootRecord := by
    cases shape : current.focus with
    | leaf value data =>
      have equal : value = key := (show value = key ∧ eraseRecord data = record from by
        simpa only [Cursor.mapRecords,shape,Source.mapRecords,Source.leaf.injEq] using erasedFocus).1
      simp only [equal,Source.rootRecord]
    | fork data left right =>
      simp only [Cursor.mapRecords,shape,Source.mapRecords,reduceCtorEq] at erasedFocus
  have located : locate after.tree position = some ⟨.leaf key current.focus.rootRecord,current.ancestors⟩ := by
    rw [found]
    congr 1
    exact congrArg (fun tree => Cursor.mk tree current.ancestors) focus
  exact ⟨current.focus.rootRecord,serve source finger run key current.focus.rootRecord position current.ancestors present located⟩

end ChaCha.Paper20261030.ReadCompletionController
