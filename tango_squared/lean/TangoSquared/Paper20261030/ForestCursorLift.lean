import TangoSquared.Paper20261030.ForestProgramComposition

/-! Running a local list-record program directly at one color finger.
Unlike the singleton packet lift, the reached source record already is
the physical vertex's complete packed list. Every other finger stays put.
-/

namespace TangoSquared.Paper20261030.ForestCursorLift

open ColoredStorage SourcePointer

variable {α ρ C σ : Type*} [DecidableEq C]

inductive State (σ : Type*) where
  | running (state : σ)
  | error

def readNext (next : List ρ → Bool → σ) : ForestLocalProgram.View ρ → State σ
  | none => .error
  | some (records,leaf) => .running (next records leaf)

def program (q : C) (source : SourceLocalProgram.Program σ (List ρ)) : ForestLocalProgram.Program (State σ) C ρ
  | .running state => match source state with
    | .halt => .halt
    | .read next => .read q (readNext next)
    | .nav action next => .nav q action (.running next)
    | .write fresh next => .write q fresh (.running next)
  | .error => .halt

theorem step (q : C) {source : SourceLocalProgram.Program σ (List ρ)} {state next : σ}
    {before after : Cursor α (List ρ)} {entry}
    (execution : SourceLocalProgram.Step source state before next after entry)
    (forest : ProjectionForest.State C α ρ) (atCursor : forest q = some before) :
    ForestLocalProgram.Step (program q source) (.running state) forest (.running next)
      (Function.update forest q (some after)) (entry.map (fun records => (q,records))) := by
  cases execution with
  | read instruction =>
    rename_i nextRead
    have unchanged : Function.update forest q (some before) = forest := by rw [← atCursor,Function.update_eq_self]
    rw [unchanged]
    exact .readSome (next := readNext nextRead) (by simp only [program,instruction]) atCursor
  | nav instruction moved => exact .nav (by simp only [program,instruction]) atCursor moved
  | write instruction => exact .write (by simp only [program,instruction]) atCursor

theorem run (q : C) {source : SourceLocalProgram.Program σ (List ρ)} {state last : σ}
    {before after : Cursor α (List ρ)} {reads cost}
    (execution : SourceLocalProgram.Run source state before last after reads cost)
    (forest : ProjectionForest.State C α ρ) (atCursor : forest q = some before) :
    ForestLocalProgram.Run (program q source) (.running state) forest (.running last)
      (Function.update forest q (some after)) (reads.map (fun records => (q,records))) cost := by
  induction execution generalizing forest with
  | halt stopped =>
    rename_i haltedState haltedCursor
    have unchanged : Function.update forest q (some haltedCursor) = forest := by rw [← atCursor,Function.update_eq_self]
    rw [unchanged]
    exact .halt (by simp only [program,stopped])
  | next first rest ih =>
    have compiled := step q first forest atCursor
    have tail := ih (Function.update forest q _) (Function.update_self _ _ _)
    have joined := ForestLocalProgram.Run.next compiled tail
    simpa only [Function.update_idem,List.map_append,Option.toList_map] using joined

end TangoSquared.Paper20261030.ForestCursorLift
