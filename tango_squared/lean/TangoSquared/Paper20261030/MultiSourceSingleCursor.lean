import TangoSquared.Paper20261030.MultiSourceValidity

/-! Running a single-cursor local kernel inside a shared multifinger
tree. Other fingers keep their vertices through rotations. The source
controller receives no addresses, and the compiled run has exactly the
same number of actual operations and the same observed records.
-/

namespace TangoSquared.Paper20261030.MultiSourceSingleCursor

open ColoredStorage SourcePointer SourcePositions
open MultiSourceProgram

variable {α ρ F σ : Type*} [DecidableEq F]

def program (source : SourceLocalProgram.Program σ ρ) (finger : F) : Program (Option σ) F ρ
  | none => .halt
  | some state => match source state with
    | .halt => .halt
    | .read next => .read finger (fun observed => observed.map (fun entry => next entry.1 entry.2))
    | .nav action next => .nav finger action (some next)
    | .write fresh next => .write finger fresh (some next)

def Represents (finger : F) (current : Cursor α ρ) (config : Configuration F α ρ) : Prop :=
  config.tree = current.tree ∧ config.fingers finger = some (address current)

theorem compile_step (source : SourceLocalProgram.Program σ ρ) (finger : F)
    {state next : σ} {before after : Cursor α ρ} {entry : Option ρ}
    (step : SourceLocalProgram.Step source state before next after entry)
    (config : Configuration F α ρ) (represented : Represents finger before config) :
    ∃ target, Step (program source finger) (some state) config (some next) target
      (entry.map (fun record => (finger,record))) ∧ Represents finger after target := by
  have reached : locate config.tree (address before) = some before := by
    rw [represented.1]; exact locate_cursor before
  cases step with
  | @read reader current instruction =>
    refine ⟨config,?_,represented⟩
    exact Step.readSome (program := program source finger) (state := some state)
      (next := fun observed => observed.map (fun entry => reader entry.1 entry.2))
      (by simp only [program,instruction]) represented.2 reached
  | nav instruction moved =>
    refine ⟨_,Step.nav (by simp only [program,instruction]) represented.2 reached moved,?_,?_⟩
    · rfl
    · simp only [moveResult,Function.update_self]
  | @write state next fresh instruction =>
    refine ⟨_,Step.write (fresh := fresh) (by simp only [program,instruction]) represented.2 reached,?_,?_⟩
    · rfl
    · exact represented.2

theorem compile_run (source : SourceLocalProgram.Program σ ρ) (finger : F)
    {state last : σ} {before after : Cursor α ρ} {reads : List ρ} {cost : Nat}
    (run : SourceLocalProgram.Run source state before last after reads cost)
    (config : Configuration F α ρ) (represented : Represents finger before config) :
    ∃ target, Run (program source finger) (some state) config (some last) target
      (reads.map (fun record => (finger,record))) cost ∧ Represents finger after target := by
  induction run generalizing config with
  | halt stopped => exact ⟨config,.halt (by simp only [program,stopped]),represented⟩
  | next first rest ih =>
    obtain ⟨middle,step,middleRep⟩ := compile_step source finger first config represented
    obtain ⟨target,body,targetRep⟩ := ih middle middleRep
    refine ⟨target,?_,targetRep⟩
    simpa only [List.map_append,Option.toList_map] using Run.next step body

end TangoSquared.Paper20261030.MultiSourceSingleCursor
