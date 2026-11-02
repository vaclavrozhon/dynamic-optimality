import ChaCha.Paper20261030.MultiSourceAugmentWriteLabels
import ChaCha.Paper20261030.MultiSourceImmutable
import ChaCha.Paper20261030.MultiSourceRecordEquivalence

set_option autoImplicit false

/-! Immutable ids remain related to the labels stored inside each
payload. This is a pointwise property of actual physical vertices. -/

namespace ChaCha.Paper20261030.SourceRecordPredicate

open ColoredStorage

theorem mapRecords {α ρ τ : Type*} (predicate : τ → Prop) (f : ρ → τ) (source : Source α ρ) :
    Holds predicate (source.mapRecords f) ↔ Holds (fun record => predicate (f record)) source := by
  induction source <;> simp_all only [Source.mapRecords,leaf,fork]

end ChaCha.Paper20261030.SourceRecordPredicate

namespace ChaCha.Paper20261030.MultiSourceImmutable

open ColoredStorage SourcePointer MultiSourceProgram MultiSourceRecordEquivalence

variable {α ρ ι κ F σ : Type*} [DecidableEq F]

theorem compile_run_predicate (label : ρ → κ) (relation : ι → κ → Prop) {source : Program σ F ρ} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : MultiSourceWriteLabels.Run label source state before last after reads cost)
    (config : Configuration F α (ι × ρ)) (erases : config.mapRecords Prod.snd = before)
    (valid : SourceRecordPredicate.Holds (fun record => relation record.1 (label record.2)) config.tree) :
    ∃ target actualReads actualCost,
      Run (program source) (.ready state) config (.ready last) target actualReads actualCost ∧
      target.mapRecords Prod.snd = after ∧
      target.tree.inventory Prod.fst = config.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (fun record => relation record.1 (label record.2)) target.tree ∧ actualCost ≤ 2*cost := by
  have swappedErases : (config.mapRecords Prod.swap).mapRecords Prod.fst = before := by
    rw [map_comp]
    exact erases
  obtain ⟨target,observed,budget,actual,targetErases,ids,targetValid,bound⟩ :=
    MultiSourceAugment.compile_run_predicate label relation run (config.mapRecords Prod.swap) swappedErases
      ((SourceRecordPredicate.mapRecords _ Prod.swap config.tree).mpr valid)
  have compiled := MultiSourceRecordEquivalence.compile_run (Equiv.prodComm ρ ι) actual
  have unswap : (config.mapRecords Prod.swap).mapRecords (Equiv.prodComm ρ ι) = config := by
    rw [map_comp]
    exact map_id config
  rw [unswap] at compiled
  refine ⟨target.mapRecords (Equiv.prodComm ρ ι),_,budget,compiled,?_,?_,?_,bound⟩
  · rw [map_comp]
    exact targetErases
  · simpa only [Configuration.mapRecords,mapRecords_inventory,Function.comp_def,Equiv.prodComm_apply,Prod.swap] using ids

  · exact (SourceRecordPredicate.mapRecords _ (Equiv.prodComm ρ ι) target.tree).mpr targetValid

end ChaCha.Paper20261030.MultiSourceImmutable
