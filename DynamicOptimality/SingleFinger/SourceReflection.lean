import DynamicOptimality.SingleFinger.SourceCounted
import ChaCha.Paper20261030.ForestMirrorProgram

/-! Reflect local programs and their counted schedules. Reflection is a
proof construction: the actual controller executes the reflected adjacent
moves on the original tree. It stores no reflected tree or subtree data.
-/

namespace DynamicOptimality.SingleFinger.SourceReflection

open ChaCha.Paper20261030 ColoredStorage SourcePointer SourceLocalProgram
open SourceCounted

variable {α ρ σ : Type*}

def instruction : Instruction σ ρ → Instruction σ ρ
  | .halt => .halt
  | .read next => .read next
  | .nav action next => .nav (mirrorMove action) next
  | .write fresh next => .write fresh next

def program (source : Program σ ρ) : Program σ ρ := fun state => instruction (source state)

theorem step {source : Program σ ρ} {state next : σ}
    {before after : Cursor α ρ} {entry}
    (execution : Step source state before next after entry) :
    Step (program source) state before.mirror next after.mirror entry := by
  cases execution with
  | read observed =>
    rename_i next
    have first := Step.read (program := program source) (state := state)
      (next := next) (cursor := before.mirror) (by simp only [program,observed,instruction])
    simpa only [Cursor.mirror,Source.mirror_root,isLeaf_mirror] using first
  | nav observed moved =>
    exact .nav (by simp only [program,observed,instruction]) (navigate_mirror _ moved)
  | write observed =>
    simpa only [Cursor.mirror,Source.mirror_setRoot] using
      (Step.write (program := program source) (state := state) (cursor := before.mirror)
        (by simp only [program,observed,instruction]))

theorem steps {source : Program σ ρ} {state last : σ}
    {before after : Cursor α ρ} {reads cost}
    (execution : Steps source state before last after reads cost) :
    Steps (program source) state before.mirror last after.mirror reads cost := by
  induction execution with
  | nil => exact .nil _ _
  | next first rest ih => exact .next (step first) ih

def schedule (commands : Schedule) : Schedule :=
  commands.map (fun (action,count) => (mirrorMove action,count))

theorem schedule_prepend (action : DynamicOptimality.LocalProgram.Move) (count : Nat) (rest : Schedule) :
    schedule (prepend action count rest) = prepend (mirrorMove action) count (schedule rest) := by
  cases count <;> rfl

theorem code_schedule (commands : Schedule) :
    SourceCounted.code (ρ := ρ) (schedule commands) =
      (program SourceCounted.code commands).mapState schedule := by
  induction commands with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨action,count⟩
    cases count with
    | zero => simpa only [schedule,List.map_cons,code,program] using ih
    | succ count =>
      change Instruction.nav (mirrorMove action) (prepend (mirrorMove action) count (schedule tail)) =
        Instruction.nav (mirrorMove action) (schedule (prepend action count tail))
      rw [schedule_prepend]

theorem counted {state last : Schedule} {before after : Cursor α ρ} {reads cost}
    (execution : Steps SourceCounted.code state before last after reads cost) :
    Steps SourceCounted.code (schedule state) before.mirror (schedule last) after.mirror reads cost := by
  exact (steps execution).mapState schedule (fun commands _ => code_schedule commands)

end DynamicOptimality.SingleFinger.SourceReflection
