import ChaCha.Paper20261030.LocalIntervalRepairController

/-! A uniform local interval-repair program for the four boundary cases.
The two optional separator keys are scalar inputs, obtained by the local
departure queries. Missing boundaries require no split. At most two
boundary-wrapper states occur in the controller's fixed state type. -/

namespace ChaCha.Paper20261030.BoundaryObservations.IntervalRepairController

open ColoredStorage SourceLocalProgram GapSource.Controller

variable {α κ ρ σ : Type*} [Ord κ]

abbrev One (σ κ ρ : Type*) := BoundaryRepairController.State σ κ ρ
abbrev Two (σ κ ρ : Type*) := One (One σ κ ρ) κ ρ

inductive State (σ κ ρ : Type*) where
  | bare (state : σ)
  | prefix (state : One σ κ ρ)
  | suffix (state : One σ κ ρ)
  | middle (state : Two σ κ ρ)
  | done

def finishBare (repair : Program σ (MarkedRecord κ ρ)) (state : σ) : State σ κ ρ :=
  if BoundaryRepairController.halted (repair state) then .done else .bare state

def finishPrefix : One σ κ ρ → State σ κ ρ
  | .done => .done
  | state => .prefix state

def finishSuffix : One σ κ ρ → State σ κ ρ
  | .done => .done
  | state => .suffix state

def finishMiddle : Two σ κ ρ → State σ κ ρ
  | .done => .done
  | state => .middle state

def initial (lower upper : Option κ) (repair : Program σ (MarkedRecord κ ρ)) (start : σ) : State σ κ ρ :=
  match lower,upper with
  | none,none => finishBare repair start
  | none,some _ => .prefix (.marker .openOuter .start)
  | some _,none => .suffix (.marker .openOuter .start)
  | some _,some _ => .middle (.marker .openOuter .start)

def program (lower upper : Option κ) (repair : Program σ (MarkedRecord κ ρ)) (start : σ) :
    Program (State σ κ ρ) (MarkedRecord κ ρ)
  | .bare state => (repair state).mapState (finishBare repair)
  | .prefix state => match upper with
    | some hi => (BoundaryRepairController.program hi false repair start state).mapState finishPrefix
    | none => .halt
  | .suffix state => match lower with
    | some lo => (BoundaryRepairController.program lo true repair start state).mapState finishSuffix
    | none => .halt
  | .middle state => match lower,upper with
    | some lo,some hi => (BoundaryRepairController.program lo true
        (BoundaryRepairController.program hi false repair start) (.marker .openOuter .start) state).mapState finishMiddle
    | _,_ => .halt
  | .done => .halt

theorem bare_code (lower upper : Option κ) (repair : Program σ (MarkedRecord κ ρ)) (start state : σ)
    (active : repair state ≠ .halt) :
    program lower upper repair start (finishBare repair state) = (repair state).mapState (finishBare repair) := by
  unfold finishBare
  cases equation : repair state with
  | halt => exact False.elim (active equation)
  | read | nav | write => simp only [BoundaryRepairController.halted,Bool.false_eq_true,ite_false,program,equation]; rfl

theorem prefix_code (lower : Option κ) (hi : κ) (repair : Program σ (MarkedRecord κ ρ)) (start : σ) (state : One σ κ ρ)
    (active : BoundaryRepairController.program hi false repair start state ≠ .halt) :
    program lower (some hi) repair start (finishPrefix state) =
      (BoundaryRepairController.program hi false repair start state).mapState finishPrefix := by
  cases state with
  | done => exact False.elim (active rfl)
  | marker | splitting | down | repairing | up | joining => rfl

theorem suffix_code (lo : κ) (upper : Option κ) (repair : Program σ (MarkedRecord κ ρ)) (start : σ) (state : One σ κ ρ)
    (active : BoundaryRepairController.program lo true repair start state ≠ .halt) :
    program (some lo) upper repair start (finishSuffix state) =
      (BoundaryRepairController.program lo true repair start state).mapState finishSuffix := by
  cases state with
  | done => exact False.elim (active rfl)
  | marker | splitting | down | repairing | up | joining => rfl

theorem middle_code (lo hi : κ) (repair : Program σ (MarkedRecord κ ρ)) (start : σ) (state : Two σ κ ρ)
    (active : BoundaryRepairController.program lo true
      (BoundaryRepairController.program hi false repair start) (.marker .openOuter .start) state ≠ .halt) :
    program (some lo) (some hi) repair start (finishMiddle state) =
      (BoundaryRepairController.program lo true (BoundaryRepairController.program hi false repair start)
        (.marker .openOuter .start) state).mapState finishMiddle := by
  cases state with
  | done => exact False.elim (active rfl)
  | marker | splitting | down | repairing | up | joining => rfl

theorem bare_run (repair : Program σ (MarkedRecord κ ρ)) (start last : σ)
    (before after : SourcePointer.Cursor α (MarkedRecord κ ρ)) (reads cost)
    (run : Run repair start before last after reads cost) :
    Run (program none none repair start) (initial none none repair start) before .done after reads cost := by
  have compiled := run.map_prefix (finishBare repair) (bare_code none none repair start)
  have stopped := BoundaryRepairController.run_halted run
  have finish : finishBare repair last = .done := by simp only [finishBare,stopped,BoundaryRepairController.halted,ite_true]
  rw [finish] at compiled
  exact compiled.run rfl

theorem prefix_run (hi : κ) (repair : Program σ (MarkedRecord κ ρ)) (start : σ)
    (before after : SourcePointer.Cursor α (MarkedRecord κ ρ)) (reads cost)
    (run : Run (BoundaryRepairController.program hi false repair start) (.marker .openOuter .start) before .done after reads cost) :
    Run (program none (some hi) repair start) (initial none (some hi) repair start) before .done after reads cost :=
  (run.map_prefix finishPrefix (prefix_code none hi repair start)).run rfl

theorem suffix_run (lo : κ) (repair : Program σ (MarkedRecord κ ρ)) (start : σ)
    (before after : SourcePointer.Cursor α (MarkedRecord κ ρ)) (reads cost)
    (run : Run (BoundaryRepairController.program lo true repair start) (.marker .openOuter .start) before .done after reads cost) :
    Run (program (some lo) none repair start) (initial (some lo) none repair start) before .done after reads cost :=
  (run.map_prefix finishSuffix (suffix_code lo none repair start)).run rfl

theorem middle_run (lo hi : κ) (repair : Program σ (MarkedRecord κ ρ)) (start : σ)
    (before after : SourcePointer.Cursor α (MarkedRecord κ ρ)) (reads cost)
    (run : Run (BoundaryRepairController.program lo true (BoundaryRepairController.program hi false repair start)
      (.marker .openOuter .start)) (.marker .openOuter .start) before .done after reads cost) :
    Run (program (some lo) (some hi) repair start) (initial (some lo) (some hi) repair start) before .done after reads cost :=
  (run.map_prefix finishMiddle (middle_code lo hi repair start)).run rfl

end ChaCha.Paper20261030.BoundaryObservations.IntervalRepairController
