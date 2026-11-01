import TangoSquared.Paper20261030.MultiSourceWriteLabels
import TangoSquared.Paper20261030.MultiSourceRecordMap

set_option autoImplicit false

/-! An unused physical finger retains its vertex label through ordinary
rotation transport and label-preserving writes. This is the invariant
needed when an anchor is parked at another component during preparation. -/

namespace TangoSquared.Paper20261030.MultiSourceProgram

open ColoredStorage SourcePointer SourcePositions
open DynamicOptimality.LocalProgram (Move)

variable {α ρ ι F σ : Type*} [DecidableEq F]

def fingerLabel (label : ρ → ι) (config : Configuration F α ρ) (finger : F) : Option ι :=
  (config.fingers finger).bind (fun position => (recordAt config.tree position).map label)

theorem navigate_transport_record (action : Move) {before after : Cursor α ρ}
    (moved : SourceLocalProgram.navigate action before = some after) (position : List Bool) :
    recordAt after.tree (transport action before position) = recordAt before.tree position := by
  obtain ⟨focus,outside⟩ := before
  cases action with
  | left => cases focus with
    | leaf => simp [SourceLocalProgram.navigate] at moved
    | fork => cases Option.some.inj moved; rfl
  | right => cases focus with
    | leaf => simp [SourceLocalProgram.navigate] at moved
    | fork => cases Option.some.inj moved; rfl
  | up => cases outside with
    | nil => simp [SourceLocalProgram.navigate] at moved
    | cons frame rest => cases frame <;> cases Option.some.inj moved <;> rfl
  | rotateRight => cases focus with
    | leaf => simp [SourceLocalProgram.navigate] at moved
    | fork top l w => cases l with
      | leaf => simp [SourceLocalProgram.navigate] at moved
      | fork p u v =>
        cases Option.some.inj moved
        exact context_record outside rightAddress (rotate_right_record u v w p top) position
  | rotateLeft => cases focus with
    | leaf => simp [SourceLocalProgram.navigate] at moved
    | fork p u r => cases r with
      | leaf => simp [SourceLocalProgram.navigate] at moved
      | fork top v w =>
        cases Option.some.inj moved
        exact context_record outside leftAddress (rotate_left_record u v w p top) position

theorem recordAt_map (label : ρ → ι) (tree : Source α ρ) (position : List Bool) :
    recordAt (tree.mapRecords label) position = (recordAt tree position).map label := by
  rw [← locate_record,locate_mapRecords,Option.map_map,← locate_record,Option.map_map]
  simp only [Function.comp_def,Cursor.mapRecords,Source.mapRecords_root]

theorem fingerLabel_congr (label : ρ → ι) {before after : Configuration F α ρ} (finger : F)
    (tree : after.tree.mapRecords label = before.tree.mapRecords label)
    (position : after.fingers finger = before.fingers finger) :
    fingerLabel label after finger = fingerLabel label before finger := by
  unfold fingerLabel
  rw [position]
  congr 1
  funext address
  rw [← recordAt_map,← recordAt_map,tree]

theorem write_labels_tree (label : ρ → ι) (current : Cursor α ρ) (fresh : ρ)
    (same : label fresh = label current.focus.rootRecord) :
    (plug (current.focus.setRoot fresh) current.ancestors).mapRecords label = current.tree.mapRecords label := by
  rw [← plug_mapRecords,Source.mapRecords_setRoot,same,← Source.mapRecords_root label current.focus]
  have rootSame : (current.focus.mapRecords label).setRoot (current.focus.mapRecords label).rootRecord =
      current.focus.mapRecords label := by cases current.focus.mapRecords label <;> rfl
  rw [rootSame,plug_mapRecords]
  rfl

def KeepsFinger (finger : F) : Instruction σ F ρ → Prop
  | .nav moved _ _ => finger ≠ moved
  | .copy destination _ _ => finger ≠ destination
  | _ => True

theorem Step.finger_label (label : ρ → ι) (finger : F) {source : Program σ F ρ}
    {state next : σ} {before after : Configuration F α ρ} {entry}
    (step : Step source state before next after entry)
    (kept : KeepsFinger finger (source state))
    (stable : MultiSourceWriteLabels.Stable label (source state) before) :
    fingerLabel label after finger = fingerLabel label before finger := by
  cases step with
  | readNone | readSome => rfl
  | @nav moved position current next action state instruction present reached advance =>
    simp only [instruction,KeepsFinger] at kept
    simp only [fingerLabel,moveResult,Function.update_of_ne kept]
    cases atFinger : before.fingers finger with
    | none => rfl
    | some position =>
      simp only [Option.map_some,Option.bind_some,navigate_transport_record action advance,locate_tree reached]
  | @write moved position current fresh state instruction present reached =>
    simp only [instruction,MultiSourceWriteLabels.Stable] at stable
    have treeSame := write_labels_tree label current fresh (stable position current present reached)
    rw [locate_tree reached] at treeSame
    simp only [fingerLabel,writeResult]
    congr 1
    funext position
    rw [← recordAt_map,← recordAt_map,treeSame]
  | copy instruction =>
    simp only [instruction,KeepsFinger] at kept
    simp only [fingerLabel,copyResult,Function.update_of_ne kept]

end TangoSquared.Paper20261030.MultiSourceProgram

namespace TangoSquared.Paper20261030.MultiSourceWriteLabels

open MultiSourceProgram

variable {α ρ ι F σ : Type*} [DecidableEq F]

theorem Run.finger_label (label : ρ → ι) (finger : F) {source : Program σ F ρ}
    (kept : ∀ state, KeepsFinger finger (source state)) {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run label source state before last after reads cost) :
    fingerLabel label after finger = fingerLabel label before finger := by
  induction run with
  | halt => rfl
  | next first stable rest ih => exact ih.trans (first.finger_label label finger (kept _) stable)

end TangoSquared.Paper20261030.MultiSourceWriteLabels
