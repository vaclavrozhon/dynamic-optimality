import ChaCha.Paper20261030.ForestProgramComposition
import ChaCha.Paper20261030.SourceMirror

/-! Executable mirroring of selected color projections. The direction
choice is fixed per color. Reads, writes, control states, observation words,
and costs are unchanged; child and rotation directions are exchanged.
Mirroring applies to the routing skeleton before payload attachment.
-/

namespace ChaCha.Paper20261030.SourceLocalProgram

open ColoredStorage SourcePointer
open DynamicOptimality.LocalProgram (Move)

variable {α ρ : Type*}

def mirrorMove : Move → Move
  | .left => .right
  | .right => .left
  | .up => .up
  | .rotateRight => .rotateLeft
  | .rotateLeft => .rotateRight

theorem isLeaf_mirror (source : Source α ρ) : isLeaf source.mirror = isLeaf source := by
  cases source <;> rfl

theorem navigate_mirror (action : Move) {before after : Cursor α ρ}
    (moved : navigate action before = some after) :
    navigate (mirrorMove action) before.mirror = some after.mirror := by
  rcases before with ⟨focus,outside⟩
  cases action with
  | left => cases focus with
    | leaf => simp [navigate] at moved
    | fork => cases Option.some.inj moved; rfl
  | right => cases focus with
    | leaf => simp [navigate] at moved
    | fork => cases Option.some.inj moved; rfl
  | up => cases outside with
    | nil => simp [navigate] at moved
    | cons frame rest => cases frame <;> cases Option.some.inj moved <;> rfl
  | rotateRight => cases focus with
    | leaf => simp [navigate] at moved
    | fork top l w => cases l with
      | leaf => simp [navigate] at moved
      | fork => cases Option.some.inj moved; rfl
  | rotateLeft => cases focus with
    | leaf => simp [navigate] at moved
    | fork p u r => cases r with
      | leaf => simp [navigate] at moved
      | fork => cases Option.some.inj moved; rfl

end ChaCha.Paper20261030.SourceLocalProgram

namespace ChaCha.Paper20261030.ForestMirrorController

open ColoredStorage SourcePointer ForestLocalProgram

variable {α ρ C σ : Type*} [DecidableEq C]

def turn (reversed : Bool) (current : Cursor α ρ) : Cursor α ρ := if reversed then current.mirror else current

def transform (orientation : C → Bool) (forest : ProjectionForest.State C α ρ) : ProjectionForest.State C α ρ :=
  fun q => (forest q).map (turn (orientation q))

def program (orientation : C → Bool) (source : Program σ C ρ) : Program σ C ρ := fun state =>
  match source state with
  | .halt => .halt
  | .read q next => .read q next
  | .nav q action next => .nav q (if orientation q then SourceLocalProgram.mirrorMove action else action) next
  | .write q fresh next => .write q fresh next

theorem transform_update (orientation : C → Bool) (forest : ProjectionForest.State C α ρ)
    (q : C) (current : Cursor α (List ρ)) :
    transform orientation (Function.update forest q (some current)) =
      Function.update (transform orientation forest) q (some (turn (orientation q) current)) := by
  funext other
  by_cases same : other = q
  · subst other; simp [transform]
  · simp only [transform,Function.update_of_ne same,Option.map_some]

theorem turn_root (reversed : Bool) (current : Cursor α ρ) :
    (turn reversed current).focus.rootRecord = current.focus.rootRecord := by
  cases reversed <;> simp only [turn,Bool.false_eq_true,if_false,ite_true,Cursor.mirror,Source.mirror_root]

theorem turn_leaf (reversed : Bool) (current : Cursor α ρ) :
    SourceLocalProgram.isLeaf (turn reversed current).focus = SourceLocalProgram.isLeaf current.focus := by
  cases reversed <;> simp only [turn,Bool.false_eq_true,if_false,ite_true,Cursor.mirror,SourceLocalProgram.isLeaf_mirror]

theorem turn_write (reversed : Bool) (current : Cursor α ρ) (fresh : ρ) :
    turn reversed ⟨current.focus.setRoot fresh,current.ancestors⟩ =
      ⟨(turn reversed current).focus.setRoot fresh,(turn reversed current).ancestors⟩ := by
  cases reversed <;> simp only [turn,Bool.false_eq_true,if_false,ite_true,Cursor.mirror,Source.mirror_setRoot]

theorem step (orientation : C → Bool) (source : Program σ C ρ) {state next : σ}
    {before after : ProjectionForest.State C α ρ} {entry}
    (execution : Step source state before next after entry) :
    Step (program orientation source) state (transform orientation before) next (transform orientation after) entry := by
  cases execution with
  | readNone instruction absent =>
    rename_i nextRead q
    exact .readNone (q := q) (by simp only [program,instruction]) (by simp only [transform,absent,Option.map_none])
  | readSome instruction present =>
    rename_i nextRead q current
    have actual := Step.readSome (program := program orientation source) (state := state)
      (next := nextRead) (by simp only [program,instruction])
      (show transform orientation before q = some (turn (orientation q) current) by
        simp only [transform,present,Option.map_some])
    simpa only [turn_root,turn_leaf] using actual
  | nav instruction present moved =>
    rename_i q current fresh action
    rw [transform_update]
    refine .nav (q := q) (before := turn (orientation q) current) (after := turn (orientation q) fresh)
      (action := if orientation q then SourceLocalProgram.mirrorMove action else action)
      (by simp only [program,instruction]) (by simp only [transform,present,Option.map_some]) ?_
    cases reversed : orientation q with
    | false => simpa only [turn,reversed,Bool.false_eq_true,if_false] using moved
    | true => simpa only [turn,reversed,ite_true] using SourceLocalProgram.navigate_mirror action moved
  | write instruction present =>
    rw [transform_update,turn_write]
    exact .write (by simp only [program,instruction]) (by simp only [transform,present,Option.map_some])

theorem compile_run (orientation : C → Bool) (source : Program σ C ρ) {state last : σ}
    {before after : ProjectionForest.State C α ρ} {reads cost}
    (execution : Run source state before last after reads cost) :
    Run (program orientation source) state (transform orientation before) last (transform orientation after) reads cost := by
  induction execution with
  | halt stopped => exact .halt (by simp only [program,stopped])
  | next first rest ih => exact .next (step orientation source first) ih

end ChaCha.Paper20261030.ForestMirrorController
