import TangoSquared.Paper20261030.SourceProgramComposition

/-! Sequential composition of local source programs. A halted first
phase executes the second phase's first instruction immediately: changing
the phase introduces neither an uncharged observation nor an extra move.
-/

namespace TangoSquared.Paper20261030.SourceLocalProgram.Sequential

open ColoredStorage SourcePointer

variable {α ρ σ τ : Type*}

def program (first : Program σ ρ) (last : Program τ ρ) (start : τ) : Program (Sum σ τ) ρ
  | .inl state => match first state with
    | .halt => (last start).mapState Sum.inr
    | instruction => instruction.mapState Sum.inl
  | .inr state => (last state).mapState Sum.inr

theorem first_code (first : Program σ ρ) (last : Program τ ρ) (start : τ) (state : σ)
    (active : first state ≠ .halt) :
    program first last start (.inl state) = (first state).mapState Sum.inl := by
  cases code : first state with
  | halt => exact False.elim (active code)
  | read | nav | write => simp only [program,code]

theorem run {first : Program σ ρ} {last : Program τ ρ} {start stop : σ} {next done : τ}
    {before middle after : Cursor α ρ} {firstReads lastReads firstCost lastCost}
    (front : Run first start before stop middle firstReads firstCost) (stopped : first stop = .halt)
    (back : Run last next middle done after lastReads lastCost) (positive : 0 < lastCost)
    (finished : last done = .halt) :
    Run (program first last next) (.inl start) before (.inr done) after
      (firstReads++lastReads) (firstCost+lastCost) := by
  have firstSteps := front.map_prefix (target := program first last next) Sum.inl (first_code first last next)
  have lastSteps := back.map_prefix (target := program first last next) Sum.inr (fun _ _ => rfl)
  have continueSteps := lastSteps.change_start (replacement := .inl stop) positive (by
    simp only [program,stopped])
  exact (firstSteps.append continueSteps).run (by simp only [program,finished,Instruction.mapState])

end TangoSquared.Paper20261030.SourceLocalProgram.Sequential
