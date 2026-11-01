import TangoSquared.Paper20261030.ForestConnectorStep
import TangoSquared.Paper20261030.ForestLeafInvariant

/-! Complete forest execution in one shared tree at unchanged cost.
A fixed, distinct connector layout covers all initially present colors.
Every later operation preserves the set of present colors, so instruction
scope and stationary-finger correctness follow without extra hypotheses.
The charged construction of the initial connector/finger configuration
and the single-finger BST simulation are separate obligations.
-/

namespace TangoSquared.Paper20261030.ForestConnector

open ColoredStorage SourcePointer

variable {α ρ C σ : Type*} [DecidableEq C]

def Covers (layout : Source C Unit) (forest : ProjectionForest.State C α ρ) : Prop :=
  ∀ q current, forest q = some current → q ∈ colors layout

theorem Covers.after {source : ForestLocalProgram.Program σ C ρ} {state next : σ}
    {before after : ProjectionForest.State C α ρ} {entry} {layout : Source C Unit}
    (covers : Covers layout before) (execution : ForestLocalProgram.Step source state before next after entry) : Covers layout after := by
  intro q current present
  cases location : before q with
  | none =>
    have word := execution.leaves q
    simp only [ForestLocalProgram.leafWord,location,present,Option.map_none,Option.map_some,reduceCtorEq] at word
  | some old => exact covers q old location

theorem Covers.run {source : ForestLocalProgram.Program σ C ρ} {state last : σ}
    {before after : ProjectionForest.State C α ρ} {reads cost} {layout : Source C Unit}
    (covers : Covers layout before) (execution : ForestLocalProgram.Run source state before last after reads cost) :
    Covers layout after := by
  induction execution with
  | halt => exact covers
  | next first rest ih => exact ih (covers.after first)

theorem compile_run (source : ForestLocalProgram.Program σ C ρ) {state last : σ}
    {before after : ProjectionForest.State C α ρ} {reads cost}
    (execution : ForestLocalProgram.Run source state before last after reads cost)
    (layout : Source C Unit) (distinct : (colors layout).Nodup) (covers : Covers layout before)
    (config : MultiSourceProgram.Configuration C α (List ρ)) (represented : assemble before layout = some config) :
    ∃ target, assemble after layout = some target ∧ MultiSourceProgram.Run (program source) state config last target reads cost := by
  induction execution generalizing config with
  | halt stopped => exact ⟨config,represented,.halt (by simp only [program,stopped])⟩
  | next first rest ih =>
    obtain ⟨middle,middleRep,firstStep⟩ := step source first layout distinct config represented (fun q _ current present => covers q current present)
    obtain ⟨target,targetRep,lastRun⟩ := ih (covers.after first) middle middleRep
    exact ⟨target,targetRep,.next firstStep lastRun⟩

end TangoSquared.Paper20261030.ForestConnector
