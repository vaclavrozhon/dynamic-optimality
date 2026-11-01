import TangoSquared.Paper20261030.CheckedStructuralCompiler
import TangoSquared.Paper20261030.ImmutableStructuralCompiler

/-! The immutable source compiler discharges all write-stability and
instruction-readiness obligations. Only distinct initial identifiers are
assumed. No correctness invariant about future metadata is supplied by
the caller of `checked_compile_run`.
-/

namespace TangoSquared.Paper20261030.ImmutableSource

open ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ ι σ : Type*}

theorem write_stable (source : Program σ ρ) (state next : State σ ρ ι)
    (current : Cursor α (ι × ρ)) (fresh : ι × ρ)
    (valid : Valid state current) (instruction : program source state = .write fresh next) :
    fresh.1 = current.focus.rootRecord.1 := by
  cases state with
  | ready state => cases h : source state <;> simp_all [program]
  | writing id payload next =>
    simp only [program,Instruction.write.injEq] at instruction
    obtain ⟨rfl,rfl⟩ := instruction
    exact valid

end TangoSquared.Paper20261030.ImmutableSource

namespace TangoSquared.Paper20261030.ImmutableStructural

open ColoredStorage SourcePointer SourceLocalProgram Structural PackedReadiness

variable {α ρ ι C σ : Type*} [DecidableEq ι] [LinearOrder C] [Fintype C]

theorem checked_tagged_run (source : Program σ ρ) (color : α → C)
    {initial last : ImmutableSource.State σ ρ ι} {before after : Cursor α (ι × ρ)} {reads cost}
    (run : Run (ImmutableSource.program source) initial before last after reads cost)
    (valid : ImmutableSource.Valid initial before) (unique : (before.tree.inventory Prod.fst).Nodup) :
    ∃ actualReads actualCost,
      CheckedRun Prod.fst color (program source) (.ready initial) (cursor Prod.fst color before)
        (.ready last) (cursor Prod.fst color after) actualReads actualCost ∧ actualCost ≤ 19*cost := by
  induction run with
  | halt stopped => exact ⟨[],0,.halt (by simp only [program,Compiler.program,stopped]),by omega⟩
  | next first rest ih =>
    obtain ⟨middleValid,inventory⟩ := ImmutableSource.step_invariant first valid
    have middleUnique := unique
    rw [inventory] at middleUnique
    obtain ⟨firstReads,firstCost,compiled,firstBound⟩ := Compiler.checked_step Prod.fst color first
      (fun fresh next instruction => ImmutableSource.write_stable source _ next _ fresh valid instruction) unique
    obtain ⟨lastReads,lastCost,tail,lastBound⟩ := ih middleValid middleUnique
    exact ⟨_,_,compiled.then_run tail,by omega⟩

theorem checked_compile_run (source : Program σ ρ) (color : α → C)
    {initial last : σ} {before after : Cursor α ρ} {reads cost}
    (run : Run source initial before last after reads cost)
    (decorated : Cursor α (ι × ρ)) (erases : decorated.mapRecords Prod.snd = before)
    (unique : (decorated.tree.inventory Prod.fst).Nodup) :
    ∃ target actualReads actualCost,
      CheckedRun Prod.fst color (program source) (ready initial) (cursor Prod.fst color decorated)
        (ready last) (cursor Prod.fst color target) actualReads actualCost ∧
      target.mapRecords Prod.snd = after ∧
      target.tree.inventory Prod.fst = decorated.tree.inventory Prod.fst ∧ actualCost ≤ 38*cost := by
  obtain ⟨target,taggedReads,taggedCost,taggedRun,targetErases,taggedBound⟩ :=
    ImmutableSource.compile_run source run decorated erases
  obtain ⟨actualReads,actualCost,actualRun,actualBound⟩ := checked_tagged_run source color taggedRun trivial unique
  exact ⟨target,actualReads,actualCost,actualRun,targetErases,
    (ImmutableSource.run_invariant taggedRun trivial).2.symm,by omega⟩

end TangoSquared.Paper20261030.ImmutableStructural
