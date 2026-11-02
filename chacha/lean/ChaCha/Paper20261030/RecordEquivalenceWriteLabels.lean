import ChaCha.Paper20261030.MultiSourceRecordEquivalence
import ChaCha.Paper20261030.MultiSourceWriteLabels

set_option autoImplicit false

/-! Record representation changes preserve the checked write labels. -/

namespace ChaCha.Paper20261030.MultiSourceRecordEquivalence

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram

variable {α ρ τ ι F σ : Type*} [DecidableEq F]

theorem stable (encode : ρ ≃ τ) (label : ρ → ι) (code : Instruction σ F ρ)
    (config : Configuration F α ρ) (safe : MultiSourceWriteLabels.Stable label code config) :
    MultiSourceWriteLabels.Stable (label ∘ encode.symm) (instruction encode code) (config.mapRecords encode) := by
  cases code with
  | halt | read | nav | copy => trivial
  | write finger fresh next =>
    intro position current present reached
    obtain ⟨original,found,same⟩ := lift_locate encode config.tree position current reached
    rw [← same]
    simpa only [Function.comp_def,Cursor.mapRecords,Source.mapRecords_root,Equiv.symm_apply_apply] using
      safe position original present found

theorem compile_write_labels (encode : ρ ≃ τ) (label : ρ → ι) {source : Program σ F ρ} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : MultiSourceWriteLabels.Run label source state before last after reads cost) :
    MultiSourceWriteLabels.Run (label ∘ encode.symm) (program encode source)
      state (before.mapRecords encode) last (after.mapRecords encode) (reads.map (observation encode)) cost := by
  induction run with
  | halt stopped => exact .halt (congrArg (instruction encode) stopped)
  | next first safe rest ih =>
    simpa only [List.map_append,Option.toList_map] using
      MultiSourceWriteLabels.Run.next (compile_step encode first) (stable encode label _ _ safe) ih

end ChaCha.Paper20261030.MultiSourceRecordEquivalence
