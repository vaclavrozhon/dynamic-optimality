import TangoSquared.Paper20261030.MultiSourceParkContinuation
import TangoSquared.Paper20261030.MultiSourceStationaryFingers

set_option autoImplicit false

/-! Copy a reached root to a working finger, follow a bounded connector
path, and read one stored record. The path will be supplied by already
read wing bits. All other fingers and every stored record are retained. -/

namespace TangoSquared.Paper20261030.PathRecordRead

open ColoredStorage SourcePointer SourcePositions

variable {α ρ τ F : Type*} [DecidableEq F]

inductive State (τ : Type*) where
  | walking (path : List Bool)
  | done (value : τ)

def source (decode : ρ → τ) : SourceLocalProgram.Program (State τ) ρ
  | .walking [] => .read (fun record _ => .done (decode record))
  | .walking (right::rest) => .nav (if right then .right else .left) (.walking rest)
  | .done _ => .halt

theorem source_run (decode : ρ → τ) (path : List Bool) (before after : Cursor α ρ)
    (reached : descend before path = some after) :
    SourceLocalProgram.Run (source decode) (.walking path) before (.done (decode after.focus.rootRecord)) after
      [after.focus.rootRecord] (path.length+1) := by
  induction path generalizing before with
  | nil =>
    have same : before = after := Option.some.inj reached
    subst before
    exact .next (.read rfl) (.halt rfl)
  | cons right rest ih =>
    cases moved : SourceLocalProgram.navigate (if right then .right else .left) before with
    | none => simp only [descend,moved,Option.bind_none,reduceCtorEq] at reached
    | some current =>
      simp only [descend,moved,Option.bind_some] at reached
      simpa only [List.length_cons,Option.toList_none,List.nil_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        SourceLocalProgram.Run.next (SourceLocalProgram.Step.nav
          (program := source decode) (state := .walking (right::rest)) rfl moved) (ih current reached)

theorem edgeOnly (decode : ρ → τ) : MultiSourceSingleCursor.EdgeOnly (source decode) := by
  intro state move next code
  cases state with
  | done => simp only [source,reduceCtorEq] at code
  | walking path => cases path with
    | nil => simp only [source,reduceCtorEq] at code
    | cons right rest =>
      cases right <;> simp only [source,Bool.false_eq_true,if_false,if_true,SourceLocalProgram.Instruction.nav.injEq] at code <;>
        cases code.1 <;> trivial

def program (origin work : F) (decode : ρ → τ) (path : List Bool) :=
  MultiSourceParkContinuation.program work origin
    (MultiSourceSingleCursor.program (source decode) work) (some (.walking path))

theorem execute (origin work : F) (decode : ρ → τ) (path : List Bool)
    (config : MultiSourceProgram.Configuration F α ρ) (before after : Cursor α ρ)
    (positioned : MultiSourceSingleCursor.Represents origin before config)
    (reached : descend before path = some after) :
    ∃ target,
      MultiSourceProgram.Run (program origin work decode path) none config
        (some (some (.done (decode after.focus.rootRecord)))) target [(work,after.focus.rootRecord)] (path.length+2) ∧
      target.tree = config.tree ∧
      MultiSourceSingleCursor.Represents work after target ∧
      (∀ finger, finger ≠ work → target.fingers finger = config.fingers finger) := by
  have copied := MultiSourceParkContinuation.parked work origin before config positioned
  obtain ⟨target,actual,located,others⟩ := MultiSourceSingleCursor.compile_edge_run (source decode) (edgeOnly decode) work
    (source_run decode path before after reached) (MultiSourceProgram.copyResult config work origin) copied
  have whole := MultiSourceParkContinuation.execute work origin _ _ _ config target actual
  refine ⟨target,?_,located.1.trans ((descend_tree reached).trans positioned.1.symm),located,?_⟩
  · simpa only [program,List.map_cons,List.map_nil,Nat.add_assoc] using whole
  · intro finger different
    exact (others finger different).trans (by simp only [MultiSourceProgram.copyResult,Function.update_of_ne different])

end TangoSquared.Paper20261030.PathRecordRead
