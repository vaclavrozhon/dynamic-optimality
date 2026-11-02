import ChaCha.Paper20261030.MultiSourceNestedExecution
import ChaCha.Paper20261030.MultiSourceImmutableWriteLabels
import ChaCha.Paper20261030.MultiSourceNestedImmutable

set_option autoImplicit false

/-! Running a component beneath an unchanged outer context, with
immutable vertex ids and additional physical fingers. The original
component controller sees only payloads; the compiler preserves the
global physical-id inventory. No outer tree is a runtime parameter. -/

namespace ChaCha.Paper20261030.MultiSourceNestedImmutable

open ColoredStorage SourcePointer MultiSourceProgram MultiSourceRegisterExtension

variable {α ρ ι κ F G σ : Type*} [DecidableEq F] [DecidableEq G]

theorem execute_predicate (label : ρ → κ) (relation : ι → κ → Prop) (source : Program σ F ρ) {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : MultiSourceWriteLabels.Run label source state before last after reads cost)
    (component : Configuration F α (ι × ρ)) (erases : component.mapRecords Prod.snd = before)
    (outside : List (Frame α (ι × ρ))) (global : Configuration (Sum F G) α (ι × ρ))
    (represented : project global = component.extend outside) (valid : WellFormed global)
    (invariant : SourceRecordPredicate.Holds (fun record => relation record.1 (label record.2)) global.tree) :
    ∃ (finalComponent : Configuration F α (ι × ρ)), ∃ target observed total,
      Run (program source) (.ready state) global (.ready last) target observed total ∧
      finalComponent.mapRecords Prod.snd = after ∧
      project target = finalComponent.extend outside ∧
      target.tree = plug finalComponent.tree outside ∧
      target.tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (fun record => relation record.1 (label record.2)) target.tree ∧
      WellFormed target ∧ total ≤ 2*cost := by
  have initialTree : global.tree = plug component.tree outside :=
    (congrArg Configuration.tree represented).trans (component.extend_tree outside)
  have globalValid := invariant
  rw [initialTree] at globalValid
  have localValid : SourceRecordPredicate.Holds (fun record => relation record.1 (label record.2)) component.tree := by
    intro record member
    exact globalValid record (Multiset.mem_of_le (Structural.inventory_le_plug id component.tree outside) member)
  obtain ⟨finalComponent,localReads,localCost,compiled,finalErases,ids,finalInvariant,bound⟩ :=
    MultiSourceImmutable.compile_run_predicate label relation run component erases localValid
  obtain ⟨target,actual,finalRep,tree,_,finalValid⟩ :=
    MultiSourceNestedExecution.execute _ compiled outside global represented valid
  refine ⟨finalComponent,target,_,localCost,actual,finalErases,finalRep,tree,
    ?_,?_,finalValid,bound⟩
  · rw [tree,initialTree]
    exact plug_inventory_congr Prod.fst ids outside
  · rw [tree]
    exact SourceRecordPredicate.context _ component.tree finalComponent.tree outside (fun _ => finalInvariant) globalValid

end ChaCha.Paper20261030.MultiSourceNestedImmutable
