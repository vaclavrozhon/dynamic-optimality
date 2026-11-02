import ChaCha.Paper20261030.MultiSourceDownward
import ChaCha.Paper20261030.MultiSourceRecordMap

set_option autoImplicit false

/-! The bounded component-entry schedule works on records carrying
immutable ids as well as on their payload erasure. Its physical tree
is unchanged; the schedule only positions existing fingers. -/

namespace ChaCha.Paper20261030.MultiSourceDownward

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram

variable {α ρ τ F : Type*} [DecidableEq F]

theorem down_tree (right : Bool) (before after : Cursor α ρ)
    (moved : SourceLocalProgram.navigate (if right then .right else .left) before = some after) :
    after.tree = before.tree := by
  obtain ⟨focus,outside⟩ := before
  cases right <;> cases focus <;> simp [SourceLocalProgram.navigate] at moved
  all_goals subst after; rfl

theorem lift_execute (erase : ρ → τ) (schedule : Schedule F)
    (before : Configuration F α ρ) (after : Configuration F α τ)
    (evaluated : execute (before.mapRecords erase) schedule = some after) :
    ∃ target, execute before schedule = some target ∧ target.mapRecords erase = after ∧ target.tree = before.tree := by
  induction schedule generalizing before with
  | nil =>
    exact ⟨before,rfl,Option.some.inj evaluated,rfl⟩
  | cons first rest ih =>
    obtain ⟨finger,right⟩ := first
    cases present : before.fingers finger with
    | none => simp only [execute,Configuration.mapRecords,present,Option.bind_none,reduceCtorEq] at evaluated
    | some position =>
      cases reached : locate (before.tree.mapRecords erase) position with
      | none => simp only [execute,Configuration.mapRecords,present,reached,Option.bind_some,Option.bind_none,reduceCtorEq] at evaluated
      | some original =>
        cases moved : SourceLocalProgram.navigate (if right then .right else .left) original with
        | none => simp only [execute,Configuration.mapRecords,present,reached,moved,Option.bind_some,Option.bind_none,reduceCtorEq] at evaluated
        | some originalNext =>
          have tailEval : execute (moveResult (before.mapRecords erase) finger
              (if right then .right else .left) original originalNext) rest = some after := by
            simpa only [execute,Configuration.mapRecords,present,reached,moved,Option.bind_some] using evaluated
          obtain ⟨current,found,same⟩ := lift_locate erase before.tree position original reached
          rw [← same] at moved
          obtain ⟨next,advance,erased⟩ := lift_navigation erase (if right then .right else .left) current originalNext moved
          let middle := moveResult before finger (if right then .right else .left) current next
          have middleErases : middle.mapRecords erase =
              moveResult (before.mapRecords erase) finger (if right then .right else .left) original originalNext := by
            simp only [middle,moveResult_mapRecords,same,erased]
          obtain ⟨target,tailRun,finalErases,tree⟩ := ih middle (by rw [middleErases]; exact tailEval)
          refine ⟨target,?_,finalErases,?_⟩
          · simpa only [execute,present,found,advance,Option.bind_some] using tailRun
          · exact tree.trans ((down_tree right current next advance).trans (locate_tree found))

theorem lift_run (erase : ρ → τ) (schedule : Schedule F)
    (before : Configuration F α ρ) (after : Configuration F α τ)
    (evaluated : execute (before.mapRecords erase) schedule = some after) :
    ∃ target, Run program schedule before [] target [] schedule.length ∧
      target.mapRecords erase = after ∧ target.tree = before.tree := by
  obtain ⟨target,actual,erases,tree⟩ := lift_execute erase schedule before after evaluated
  exact ⟨target,execute_run schedule before target actual,erases,tree⟩

end ChaCha.Paper20261030.MultiSourceDownward
