import TangoSquared.Paper20261030.LocalPackedRotation
import TangoSquared.Paper20261030.SourceProgramRecordMap

/-! The metadata inspected at each simulated source instruction.
Only the fields used by that instruction must be ready. In particular an
ascent uses the parent's child masks but not its child identifiers, which
may await the external-parent repair after a rotation. A checked execution
records these obligations at every instruction, not only at its endpoints.
This is an intermediate interface; the structural compiler must discharge it.
-/

namespace TangoSquared.Paper20261030.PackedReadiness

open ColoredStorage SourcePointer SourceLocalProgram Structural
open DynamicOptimality.LocalProgram (Move)

variable {α ρ η C σ : Type*} [DecidableEq η] [LinearOrder C] [Fintype C]

abbrev Record (ρ η C : Type*) := ρ × Fields η C

def Children (identifier : ρ → η) (color : α → C) : Source α (Record ρ η C) → Prop
  | .leaf _ _ => False
  | .fork record l r => record.2.children = some
      (Child.mk (identifier l.rootRecord.1) (l.support color),Child.mk (identifier r.rootRecord.1) (r.support color))

def Parent (identifier : ρ → η) (color : α → C) (current : Cursor α (Record ρ η C)) : Prop :=
  match current.ancestors with
  | [] => False
  | .left record sibling::_ =>
    current.focus.rootRecord.2.parent = some (identifier record.1) ∧
      ∃ leftId rightId, record.2.children = some
        (Child.mk leftId (current.focus.support color),Child.mk rightId (sibling.support color))
  | .right sibling record::_ =>
    current.focus.rootRecord.2.parent = some (identifier record.1) ∧
      ∃ leftId rightId, record.2.children = some
        (Child.mk leftId (sibling.support color),Child.mk rightId (current.focus.support color))

def Rotation (identifier : ρ → η) (color : α → C) (right : Bool) (current : Cursor α (Record ρ η C)) : Prop :=
  match right,current.focus with
  | true,.fork top (.fork p u v) w =>
    PackedRotationProgram.RootReady identifier color true u v w p top ∧
    PackedRotationProgram.PivotReady identifier color true u v w p top ∧
    p.2.parent = some (identifier top.1) ∧ ColorsCorrect (fun record => record.2.colors) color current.tree
  | false,.fork p u (.fork top v w) =>
    PackedRotationProgram.RootReady identifier color false u v w p top ∧
    PackedRotationProgram.PivotReady identifier color false u v w p top ∧
    top.2.parent = some (identifier p.1) ∧ ColorsCorrect (fun record => record.2.colors) color current.tree
  | _,_ => False

def Ready (identifier : ρ → η) (color : α → C) (instruction : Instruction σ (Record ρ η C))
    (current : Cursor α (Record ρ η C)) : Prop :=
  match instruction with
  | .halt => True
  | .read _ => current.focus.rootRecord.2.children.isNone = isLeaf current.focus
  | .write fresh _ => identifier fresh.1 = identifier current.focus.rootRecord.1
  | .nav action _ => match action with
    | .left | .right => Children identifier color current.focus
    | .up => Parent identifier color current
    | .rotateRight => Rotation identifier color true current
    | .rotateLeft => Rotation identifier color false current

inductive CheckedRun (identifier : ρ → η) (color : α → C) (program : Program σ (Record ρ η C)) :
    σ → Cursor α (Record ρ η C) → σ → Cursor α (Record ρ η C) → List (Record ρ η C) → Nat → Prop
  | halt {state current} (stopped : program state = .halt) : CheckedRun identifier color program state current state current [] 0
  | next {state middle last before current after entry reads cost}
      (step : Step program state before middle current entry)
      (ready : Ready identifier color (program state) before)
      (rest : CheckedRun identifier color program middle current last after reads cost) :
      CheckedRun identifier color program state before last after (entry.toList++reads) (cost+1)

theorem CheckedRun.run {identifier : ρ → η} {color : α → C} {program : Program σ (Record ρ η C)}
    {state last : σ} {before after : Cursor α (Record ρ η C)} {reads cost}
    (checked : CheckedRun identifier color program state before last after reads cost) :
    Run program state before last after reads cost := by
  induction checked with
  | halt stopped => exact .halt stopped
  | next step ready rest ih => exact .next step ih

theorem step_inventory (identifier : ρ → η) (color : α → C) {program : Program σ (Record ρ η C)}
    {state next : σ} {before after : Cursor α (Record ρ η C)} {entry}
    (step : Step program state before next after entry) (ready : Ready identifier color (program state) before) :
    before.tree.inventory (fun record => identifier record.1) = after.tree.inventory (fun record => identifier record.1) := by
  cases step with
  | read => rfl
  | nav instruction moved => exact navigate_inventory (fun record => identifier record.1) _ moved
  | write instruction =>
    rename_i fresh
    have same : identifier fresh.1 = identifier before.focus.rootRecord.1 := by simpa only [instruction,Ready] using ready
    exact (plug_inventory_congr (fun record => identifier record.1)
      (Source.inventory_setRoot (fun record => identifier record.1) before.focus fresh same) before.ancestors).symm

theorem CheckedRun.inventory {identifier : ρ → η} {color : α → C} {program : Program σ (Record ρ η C)}
    {state last : σ} {before after : Cursor α (Record ρ η C)} {reads cost}
    (checked : CheckedRun identifier color program state before last after reads cost) :
    before.tree.inventory (fun record => identifier record.1) = after.tree.inventory (fun record => identifier record.1) := by
  induction checked with
  | halt => rfl
  | next step ready rest ih => exact (step_inventory identifier color step ready).trans ih

end TangoSquared.Paper20261030.PackedReadiness
