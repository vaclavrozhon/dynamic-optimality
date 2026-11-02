import ChaCha.Paper20261030.MultiSourceNestedExecution
import ChaCha.Paper20261030.MultiSourceImmutable

set_option autoImplicit false

/-! Running a component beneath an unchanged outer context, with
immutable vertex ids and additional physical fingers. The original
component controller sees only payloads; the compiler preserves the
global physical-id inventory. No outer tree is a runtime parameter. -/

namespace ChaCha.Paper20261030.MultiSourceNestedImmutable

open ColoredStorage SourcePointer MultiSourceProgram MultiSourceRegisterExtension

variable {α ρ ι F G σ : Type*} [DecidableEq F] [DecidableEq G]

def program (source : Program σ F ρ) :
    Program (MultiSourceImmutable.State σ F ρ ι) (Sum F G) (ι × ρ) :=
  MultiSourceRegisterExtension.program (MultiSourceImmutable.program source)

theorem execute (source : Program σ F ρ) {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost)
    (component : Configuration F α (ι × ρ)) (erases : component.mapRecords Prod.snd = before)
    (outside : List (Frame α (ι × ρ))) (global : Configuration (Sum F G) α (ι × ρ))
    (represented : project global = component.extend outside) (valid : WellFormed global) :
    ∃ (finalComponent : Configuration F α (ι × ρ)), ∃ target observed total,
      Run (program source) (.ready state) global (.ready last) target observed total ∧
      finalComponent.mapRecords Prod.snd = after ∧
      project target = finalComponent.extend outside ∧
      target.tree = plug finalComponent.tree outside ∧
      target.tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      WellFormed target ∧ total ≤ 2*cost := by
  obtain ⟨finalComponent,localReads,localCost,compiled,finalErases,ids,bound⟩ :=
    MultiSourceImmutable.compile_run run component erases
  obtain ⟨target,actual,finalRep,tree,_,finalValid⟩ :=
    MultiSourceNestedExecution.execute _ compiled outside global represented valid
  have initialTree : global.tree = plug component.tree outside :=
    (congrArg Configuration.tree represented).trans (component.extend_tree outside)
  exact ⟨finalComponent,target,_,localCost,actual,finalErases,finalRep,tree,
    by rw [tree,initialTree]; exact plug_inventory_congr Prod.fst ids outside,
    finalValid,bound⟩

end ChaCha.Paper20261030.MultiSourceNestedImmutable
