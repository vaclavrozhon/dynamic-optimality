import TangoSquared.Paper20261030.ForestWriteLabels
import TangoSquared.Paper20261030.ForestMirrorProgram

set_option autoImplicit false

/-! Mirroring changes directions, but preserves the reached record and
therefore the per-write label guarantee. -/

namespace TangoSquared.Paper20261030.ForestMirrorController

open ColoredStorage SourcePointer ForestLocalProgram

variable {α ρ ι C σ : Type*} [DecidableEq C]

theorem stable (label : ρ → ι) (orientation : C → Bool) (source : Program σ C ρ)
    (state : σ) (forest : ProjectionForest.State C α ρ)
    (checked : ForestWriteLabels.Stable label (source state) forest) :
    ForestWriteLabels.Stable label (program orientation source state) (transform orientation forest) := by
  cases code : source state with
  | halt | read | nav => simp only [program,code,ForestWriteLabels.Stable]
  | write q fresh next =>
    simp only [program,code,ForestWriteLabels.Stable]
    intro current present
    cases location : forest q with
    | none => simp only [transform,location,Option.map_none,reduceCtorEq] at present
    | some original =>
      have equal : turn (orientation q) original = current := by
        simpa only [transform,location,Option.map_some,Option.some.injEq] using present
      rw [← equal,turn_root]
      exact (show ∀ actual, forest q = some actual → fresh.map label = actual.focus.rootRecord.map label from
        by simpa only [code,ForestWriteLabels.Stable] using checked) original location

theorem compile_write_labels (label : ρ → ι) (orientation : C → Bool) (source : Program σ C ρ)
    {state last : σ} {before after : ProjectionForest.State C α ρ} {reads cost}
    (execution : ForestWriteLabels.Run label source state before last after reads cost) :
    ForestWriteLabels.Run label (program orientation source) state (transform orientation before)
      last (transform orientation after) reads cost := by
  induction execution with
  | halt stopped => exact .halt (by simp only [program,stopped])
  | next first checked rest ih => exact .next (step orientation source first) (stable label orientation source _ _ checked) ih

end TangoSquared.Paper20261030.ForestMirrorController
