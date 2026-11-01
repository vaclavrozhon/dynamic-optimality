import TangoSquared.Paper20261030.MultiSourceAugment
import TangoSquared.Paper20261030.MultiSourceRecordEquivalence

set_option autoImplicit false

/-! The existing metadata-preserving compiler in the physical packet
controller's immutable-id-first convention. Each payload write first
reads the reached id. The id is then retained, with at most two actual
instructions per original instruction. -/

namespace TangoSquared.Paper20261030.MultiSourceImmutable

open ColoredStorage SourcePointer MultiSourceProgram MultiSourceRecordEquivalence

variable {α ρ ι F σ : Type*} [DecidableEq F]

abbrev State (σ F ρ ι : Type*) := MultiSourceAugment.State σ F ρ ι

def program (source : Program σ F ρ) : Program (State σ F ρ ι) F (ι × ρ) :=
  MultiSourceRecordEquivalence.program (Equiv.prodComm ρ ι) (MultiSourceAugment.program source)

theorem compile_run {source : Program σ F ρ} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost)
    (config : Configuration F α (ι × ρ)) (erases : config.mapRecords Prod.snd = before) :
    ∃ target actualReads actualCost,
      Run (program source) (.ready state) config (.ready last) target actualReads actualCost ∧
      target.mapRecords Prod.snd = after ∧
      target.tree.inventory Prod.fst = config.tree.inventory Prod.fst ∧ actualCost ≤ 2*cost := by
  have swappedErases : (config.mapRecords Prod.swap).mapRecords Prod.fst = before := by
    rw [map_comp]
    exact erases
  obtain ⟨target,observed,budget,actual,targetErases,ids,bound⟩ :=
    MultiSourceAugment.compile_run run (config.mapRecords Prod.swap) swappedErases
  have compiled := MultiSourceRecordEquivalence.compile_run (Equiv.prodComm ρ ι) actual
  have unswap : (config.mapRecords Prod.swap).mapRecords (Equiv.prodComm ρ ι) = config := by
    rw [map_comp]
    exact map_id config
  rw [unswap] at compiled
  refine ⟨target.mapRecords (Equiv.prodComm ρ ι),_,budget,compiled,?_,?_,bound⟩
  · rw [map_comp]
    exact targetErases
  · simpa only [Configuration.mapRecords,mapRecords_inventory,Function.comp_def,Equiv.prodComm_apply,Prod.swap] using ids

end TangoSquared.Paper20261030.MultiSourceImmutable
