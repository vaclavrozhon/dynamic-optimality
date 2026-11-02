import ChaCha.Paper20261030.ForestLocalProgram
import ChaCha.Paper20261030.SourceProgramRecordMap

/-! Running a source program at one specified forest finger. A physical
vertex stores one packet containing the source record; reads unpack that
packet and writes replace it. This lets the forest reuse the checked
structural and parent-observation controllers without adding an opaque
parent-read instruction. No other color finger changes.
-/

namespace ChaCha.Paper20261030.SourceForestLift

open ColoredStorage SourcePointer

variable {α ρ C σ : Type*} [DecidableEq C]

inductive State (σ : Type*) where
  | running (state : σ)
  | error

def readNext (next : ρ → Bool → σ) : ForestLocalProgram.View ρ → State σ
  | some ([record],leaf) => .running (next record leaf)
  | _ => .error

def program (q : C) (source : SourceLocalProgram.Program σ ρ) : ForestLocalProgram.Program (State σ) C ρ
  | .running state => match source state with
    | .halt => .halt
    | .read next => .read q (readNext next)
    | .nav action next => .nav q action (.running next)
    | .write fresh next => .write q [fresh] (.running next)
  | .error => .halt

def packet (source : Cursor α ρ) : Cursor α (List ρ) := source.mapRecords (fun record => [record])

theorem step (q : C) {source : SourceLocalProgram.Program σ ρ} {state next : σ}
    {before after : Cursor α ρ} {entry}
    (execution : SourceLocalProgram.Step source state before next after entry)
    (forest : ProjectionForest.State C α ρ) (atCursor : forest q = some (packet before)) :
    ForestLocalProgram.Step (program q source) (.running state) forest (.running next)
      (Function.update forest q (some (packet after))) (entry.map (fun record => (q,[record]))) := by
  cases execution with
  | read instruction =>
    rename_i nextRead
    have unchanged : Function.update forest q (some (packet before)) = forest := by
      rw [← atCursor,Function.update_eq_self]
    rw [unchanged]
    have actual := ForestLocalProgram.Step.readSome (program := program q source) (state := .running state)
      (next := readNext nextRead) (by simp only [program,instruction]) atCursor
    simpa only [packet,Cursor.mapRecords,Source.mapRecords_root,isLeaf_mapRecords,readNext,Option.map_some] using actual
  | nav instruction moved =>
    rename_i action
    have actualMove : SourceLocalProgram.navigate action (packet before) = some (packet after) := by
      rw [packet,← navigate_mapRecords,moved]
      rfl
    exact .nav (by simp only [program,instruction]) atCursor actualMove
  | write instruction =>
    rename_i fresh
    have actual := ForestLocalProgram.Step.write (program := program q source) (state := .running state) (fresh := [fresh]) (next := .running next)
      (by simp only [program,instruction]) atCursor
    simpa only [packet,Cursor.mapRecords,Source.mapRecords_setRoot,Option.map_none] using actual

theorem run (q : C) {source : SourceLocalProgram.Program σ ρ} {state last : σ}
    {before after : Cursor α ρ} {reads cost}
    (execution : SourceLocalProgram.Run source state before last after reads cost)
    (forest : ProjectionForest.State C α ρ) (atCursor : forest q = some (packet before)) :
    ForestLocalProgram.Run (program q source) (.running state) forest (.running last)
      (Function.update forest q (some (packet after))) (reads.map (fun record => (q,[record]))) cost := by
  induction execution generalizing forest with
  | halt stopped =>
    rename_i haltedState haltedCursor
    have unchanged : Function.update forest q (some (packet haltedCursor)) = forest := by
      rw [← atCursor,Function.update_eq_self]
    rw [unchanged]
    exact .halt (by simp only [program,stopped])
  | next first rest ih =>
    have compiled := step q first forest atCursor
    have tail := ih (Function.update forest q _) (Function.update_self _ _ _)
    have joined := ForestLocalProgram.Run.next compiled tail
    simpa only [Function.update_idem,List.map_append,Option.toList_map] using joined

end ChaCha.Paper20261030.SourceForestLift
