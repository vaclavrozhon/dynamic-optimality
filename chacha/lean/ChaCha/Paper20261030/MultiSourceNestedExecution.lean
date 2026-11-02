import ChaCha.Paper20261030.MultiSourceContextRun
import ChaCha.Paper20261030.MultiSourceRegisterExtension
import ChaCha.Paper20261030.MultiSourceSingleCursor
import ChaCha.Paper20261030.SourceLocatedAddress

set_option autoImplicit false

/-!
# Component execution in a larger tree with additional fingers

The component's ordinary registers occupy the left summand. Additional
registers may already point to other components, ancestors, or retained
payloads. They undergo the physical model's usual rotation transport.
The surrounding context is unchanged. Neither addresses nor contexts
are passed to the running controller, and the cost is unchanged.
-/

namespace ChaCha.Paper20261030.MultiSourceNestedExecution

open ColoredStorage SourcePointer MultiSourceProgram MultiSourceRegisterExtension

variable {α ρ F G σ : Type*} [DecidableEq F] [DecidableEq G]

theorem position (component : Configuration F α ρ) (outside : List (Frame α ρ))
    (global : Configuration (Sum F G) α ρ) (represented : project global = component.extend outside)
    (finger : F) (current : Cursor α ρ) (localRep : MultiSourceSingleCursor.Represents finger current component) :
    MultiSourceSingleCursor.Represents (.inl finger) (current.extend outside) global := by
  constructor
  · have tree : global.tree = plug component.tree outside :=
      (congrArg Configuration.tree represented).trans (component.extend_tree outside)
    rw [tree,localRep.1]
    exact (plug_append current.focus current.ancestors outside).symm
  · have present := (congrArg (fun config => config.fingers finger) represented).trans
      (component.extend_finger outside finger)
    simpa only [project,localRep.2,Option.map_some,SourcePositions.address_extend] using present

theorem execute (source : Program σ F ρ) {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost)
    (outside : List (Frame α ρ))
    (global : Configuration (Sum F G) α ρ)
    (represented : project global = before.extend outside) (valid : WellFormed global) :
    ∃ target, Run (program source) state global last target (reads.map observation) cost ∧
      project target = after.extend outside ∧
      target.tree = plug after.tree outside ∧
      (∀ finger, target.fingers (.inl finger) = (after.fingers finger).map
        (fun position => outside.reverse.map SourcePositions.direction ++ position)) ∧
      WellFormed target := by
  obtain ⟨target,actual,finalRep,finalValid⟩ :=
    MultiSourceRegisterExtension.execute source (run.extend outside) global represented valid
  refine ⟨target,actual,finalRep,?_,?_,finalValid⟩
  · exact (congrArg Configuration.tree finalRep).trans (after.extend_tree outside)
  · intro finger
    exact (congrArg (fun config => config.fingers finger) finalRep).trans (after.extend_finger outside finger)

end ChaCha.Paper20261030.MultiSourceNestedExecution
