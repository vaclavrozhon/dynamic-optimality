import ChaCha.Paper20261030.SourceInorderMetadataPairs
import ChaCha.Paper20261030.MultiSourceAugmentMetadataLabels
import ChaCha.Paper20261030.MultiSourceRunDeterminism

set_option autoImplicit false

/-! The cache wrapper retains metadata at the same immutable physical
identifier. The source's exact identifier order and the metadata
compiler's exact metadata order preserve their paired inventory. The
result applies to the actual run by determinism, with no new controller. -/

namespace ChaCha.Paper20261030.MultiSourceAugment

open ColoredStorage SourcePointer MultiSourceProgram

variable {α ρ ι μ F σ : Type*} [DecidableEq F]

theorem paired_inventory (identify : ρ → ι) {source : Program σ F ρ} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost)
    (order : after.tree.inorderLabels identify = before.tree.inorderLabels identify)
    (config : Configuration F α (ρ × μ)) (erases : config.mapRecords Prod.fst = before)
    {target : Configuration F α (ρ × μ)} {observed total}
    (actual : Run (program source) (.ready state) config (.ready last) target observed total) :
    target.tree.inventory (fun record => (identify record.1,record.2)) =
      config.tree.inventory (fun record => (identify record.1,record.2)) := by
  obtain ⟨checkedTarget,actualReads,actualCost,checked,targetErases,_,_⟩ := compile_metadata_run run config erases
  have same := checked.run.deterministic actual
  rw [← same.2.1]
  have initialTree : config.tree.mapRecords Prod.fst = before.tree := congrArg Configuration.tree erases
  have finalTree : checkedTarget.tree.mapRecords Prod.fst = after.tree := congrArg Configuration.tree targetErases
  apply Source.paired_inventory (identify ∘ Prod.fst) Prod.snd config.tree checkedTarget.tree
  · rw [← Source.inorderLabels_map,← Source.inorderLabels_map,initialTree,finalTree]
    exact order
  · exact checked.inorderLabels Prod.snd

end ChaCha.Paper20261030.MultiSourceAugment
