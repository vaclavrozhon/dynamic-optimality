import ChaCha.Paper20261030.ForestWriteLabels
import ChaCha.Paper20261030.MultiSourceWriteLabels
import ChaCha.Paper20261030.ForestConnectorPositions

set_option autoImplicit false

/-! The actual reached record in the common connector tree is the
selected projection's current record. Hence assembly retains the
per-write label guarantee, with the original program and cost. -/

namespace ChaCha.Paper20261030.ForestConnector

open ColoredStorage SourcePointer

variable {α ρ ι C σ : Type*} [DecidableEq C]

theorem stable (label : ρ → ι) (source : ForestLocalProgram.Program σ C ρ) (state : σ)
    (forest : ProjectionForest.State C α ρ) (layout : Source C Unit) (covers : Covers layout forest)
    (config : MultiSourceProgram.Configuration C α (List ρ)) (assembled : assemble forest layout = some config)
    (safe : ForestWriteLabels.Stable label (source state) forest) :
    MultiSourceWriteLabels.Stable (List.map label) (program source state) config := by
  cases code : source state with
  | halt | read | nav => simp only [program,code,MultiSourceWriteLabels.Stable]
  | write q fresh next =>
    simp only [program,code,MultiSourceWriteLabels.Stable]
    intro position current present reached
    cases location : forest q with
    | none => rw [assemble_absent forest layout config assembled q location] at present; cases present
    | some original =>
      obtain ⟨pos,outside,finger,located⟩ := assemble_cursor forest layout config assembled q (covers q original location) original location
      have samePos := Option.some.inj (present.symm.trans finger)
      subst pos
      have same := Option.some.inj (reached.symm.trans located)
      subst current
      have checked := safe
      simp only [code,ForestWriteLabels.Stable] at checked
      exact checked original location

theorem compile_write_labels (label : ρ → ι) (source : ForestLocalProgram.Program σ C ρ) {state last : σ}
    {before after : ProjectionForest.State C α ρ} {reads cost}
    (execution : ForestWriteLabels.Run label source state before last after reads cost)
    (layout : Source C Unit) (distinct : (colors layout).Nodup) (covers : Covers layout before)
    (config : MultiSourceProgram.Configuration C α (List ρ)) (assembled : assemble before layout = some config) :
    ∃ target, assemble after layout = some target ∧
      MultiSourceWriteLabels.Run (List.map label) (program source) state config last target reads cost := by
  induction execution generalizing config with
  | halt stopped => exact ⟨config,assembled,.halt (by simp only [program,stopped])⟩
  | next first safe rest ih =>
    obtain ⟨middle,middleRep,actual⟩ := step source first layout distinct config assembled (fun q _ current present => covers q current present)
    obtain ⟨target,targetRep,tail⟩ := ih (covers.after first) middle middleRep
    exact ⟨target,targetRep,.next actual (stable label source _ _ layout covers config assembled safe) tail⟩

end ChaCha.Paper20261030.ForestConnector
