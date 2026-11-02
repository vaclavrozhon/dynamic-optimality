import ChaCha.Paper20261030.MultiSourceRegisterExtension
import ChaCha.Paper20261030.MultiSourceFingerLabels
import ChaCha.Paper20261030.MultiSourceScalarInvariant

set_option autoImplicit false

/-! Renaming component registers preserves checked write labels.
Additional registers are never moved or overwritten by the controller. -/

namespace ChaCha.Paper20261030.MultiSourceRegisterExtension

open ColoredStorage SourcePointer MultiSourceProgram

variable {α ρ ι F G σ : Type*} [DecidableEq F] [DecidableEq G]

theorem stable (label : ρ → ι) (code : Instruction σ F ρ) (before : Configuration F α ρ)
    (global : Configuration (Sum F G) α ρ) (represented : project global = before)
    (safe : MultiSourceWriteLabels.Stable label code before) :
    MultiSourceWriteLabels.Stable label (instruction code) global := by
  cases code with
  | halt | read | nav | copy => trivial
  | write finger fresh next =>
    intro position current present reached
    have tree : global.tree = before.tree := congrArg Configuration.tree represented
    have atFinger : global.fingers (.inl finger) = before.fingers finger :=
      congrArg (fun config => config.fingers finger) represented
    exact safe position current (atFinger.symm.trans present) (by rw [← tree]; exact reached)

theorem compile_write_labels (label : ρ → ι) {source : Program σ F ρ} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : MultiSourceWriteLabels.Run label source state before last after reads cost)
    (global : Configuration (Sum F G) α ρ) (represented : project global = before) :
    ∃ target, MultiSourceWriteLabels.Run label (program source) state global last target
      (reads.map observation) cost ∧ project target = after := by
  induction run generalizing global with
  | halt stopped => exact ⟨global,.halt (by simp only [program,stopped,instruction]),represented⟩
  | next first safe rest ih =>
    obtain ⟨middle,step,middleRep⟩ := compile_step source first global represented
    obtain ⟨target,body,targetRep⟩ := ih middle middleRep
    refine ⟨target,?_,targetRep⟩
    simpa only [List.map_append,Option.toList_map] using
      MultiSourceWriteLabels.Run.next step (stable label _ _ global represented safe) body

theorem keeps_extra (source : Program σ F ρ) (extra : G) (state : σ) :
    KeepsFinger (.inr extra) (program (G := G) source state) := by
  cases code : source state <;> simp only [program,code,instruction,KeepsFinger,ne_eq,reduceCtorEq,not_false_eq_true]

theorem keeps_copy_extra (source : Program σ F ρ) (extra : G) (state : σ) :
    KeepsCopy (.inr extra) (program (G := G) source state) := by
  cases code : source state <;> simp only [program,code,instruction,KeepsCopy,ne_eq,reduceCtorEq,not_false_eq_true]

end ChaCha.Paper20261030.MultiSourceRegisterExtension
