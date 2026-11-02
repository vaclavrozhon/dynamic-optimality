import ChaCha.Paper20261030.GapSourceProgramCompiler

/-! Correctness of the local auxiliary-to-source compiler. Its input is
an actual local program run. Marked port trees remain opaque and unchanged;
the output has the exact source-controller state and encoded tree, with
at most seven source operations per auxiliary instruction. -/

namespace ChaCha.Paper20261030.GapSource.Controller

open ColoredStorage SourcePointer SourceLocalProgram Auxiliary DynamicOptimality MTR

variable {α κ ρ σ : Type*}

theorem read_prefix {source : LocalProgram.Program σ κ ρ} {state : σ} {next : LocalProgram.View κ ρ → σ}
    (instruction : source state = .read next) (ports : Nat → Source α (MarkedRecord κ ρ))
    (marked : ∀ i, boundary (ports i).rootRecord = true) (base : Nat)
    (logical : Metadata.Cursor κ (fun _ => ρ)) (view : LocalProgram.View κ ρ)
    (observed : LocalProgram.observe logical = some view) :
    ∃ reads, Steps (code source) (.ready state) (encodedCursor ports base logical)
      (.ready (next view)) (encodedCursor ports base logical) reads 7 := by
  obtain ⟨reads,run⟩ := read_cursor ports marked base logical view observed
  have compiled := run.map_prefix (finishRead source state) (read_code source state)
  have started := compiled.change_start (replacement := .ready state) (by decide)
    (by simp only [finishRead,code,instruction])
  exact ⟨reads,by simpa only [finishRead,instruction] using started⟩

def Update.instruction (operation : Update ρ) (next : σ) : LocalProgram.Instruction σ κ ρ :=
  match operation with
  | .value fresh => .write fresh next
  | .size fresh => .writeSize fresh next

theorem write_prefix {source : LocalProgram.Program σ κ ρ} {state next : σ} (operation : Update ρ)
    (instruction : source state = operation.instruction next) (ports : Nat → Source α (MarkedRecord κ ρ)) (base : Nat)
    (left right : RawTree (Record κ ρ)) (entry : Record κ ρ) (rest) :
    ∃ reads, Steps (code source) (.ready state) (encodedCursor ports base ⟨.node left entry right,rest⟩)
      (.ready next) (encodedCursor ports base ⟨.node left (operation.apply entry) right,rest⟩) reads 2 := by
  obtain ⟨reads,run⟩ := write_cursor ports base operation left right entry rest
  have compiled := run.map_prefix (finishWrite next) (write_code source next)
  have started := compiled.change_start (replacement := .ready state) (by decide)
    (by cases operation <;> simp only [finishWrite,code,instruction,Update.instruction])
  exact ⟨reads,started⟩

theorem compile_step {source : LocalProgram.Program σ κ ρ} {state next : σ}
    {before after : Metadata.Cursor κ (fun _ => ρ)} {entry}
    (step : LocalProgram.Step source state before next after entry)
    (ports : Nat → Source α (MarkedRecord κ ρ)) (marked : ∀ i, boundary (ports i).rootRecord = true) (base : Nat) :
    ∃ reads cost, Steps (code source) (.ready state) (encodedCursor ports base before)
      (.ready next) (encodedCursor ports base after) reads cost ∧ cost ≤ 7 := by
  cases step with
  | @read next cursor view instruction observed =>
    obtain ⟨reads,run⟩ := read_prefix instruction ports marked base before view observed
    exact ⟨reads,7,run,le_rfl⟩
  | nav instruction moved =>
    have move : Step (code source) (.ready state) (encodedCursor ports base before)
        (.ready next) (encodedCursor ports base after) none :=
      .nav (by simp only [code,instruction]) (move_cursor ports base moved)
    exact ⟨[],1,move.prefix,by decide⟩
  | @write next left right size key old fresh rest instruction =>
    obtain ⟨reads,run⟩ := write_prefix (.value fresh) instruction ports base left right (size,⟨key,old⟩) rest
    exact ⟨reads,2,run,by decide⟩
  | @writeSize next left right old fresh entry rest instruction =>
    obtain ⟨reads,run⟩ := write_prefix (.size fresh) instruction ports base left right (old,entry) rest
    exact ⟨reads,2,run,by decide⟩

theorem compile_run {source : LocalProgram.Program σ κ ρ} {state last : σ}
    {before after : Metadata.Cursor κ (fun _ => ρ)} {observations budget}
    (run : LocalProgram.Run source state before last after observations budget)
    (ports : Nat → Source α (MarkedRecord κ ρ)) (marked : ∀ i, boundary (ports i).rootRecord = true) (base : Nat) :
    ∃ reads cost, Run (code source) (.ready state) (encodedCursor ports base before)
      (.ready last) (encodedCursor ports base after) reads cost ∧ cost ≤ 7*budget := by
  induction run with
  | halt stopped => exact ⟨[],0,.halt (by simp only [code,stopped]),Nat.zero_le _⟩
  | next first rest ih =>
    obtain ⟨firstReads,firstCost,firstRun,firstBound⟩ := compile_step first ports marked base
    obtain ⟨lastReads,lastCost,lastRun,lastBound⟩ := ih
    exact ⟨_,_,firstRun.then_run lastRun,by omega⟩

end ChaCha.Paper20261030.GapSource.Controller
