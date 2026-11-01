import TangoSquared.Paper20261030.ProjectionForest
import TangoSquared.Paper20261030.SourceLocalProgram

/-! Local programs for the existing forest of color projections. One
finger is retained per color, including its parked position. An absent
finger is observable as an empty register; checking it is conservatively
charged one unit here and uses zero physical forest operations.
This is an intermediate constant-finger model, not a single-cursor BST.
-/

namespace TangoSquared.Paper20261030.ForestLocalProgram

open ColoredStorage SourcePointer
open DynamicOptimality.LocalProgram (Move)

variable {α ρ C σ : Type*} [DecidableEq C]

abbrev View (ρ : Type*) := Option (List ρ × Bool)

inductive Instruction (σ C ρ : Type*) where
  | halt
  | read (color : C) (next : View ρ → σ)
  | nav (color : C) (action : Move) (next : σ)
  | write (color : C) (records : List ρ) (next : σ)

abbrev Program (σ C ρ : Type*) := σ → Instruction σ C ρ

inductive Step (program : Program σ C ρ) :
    σ → ProjectionForest.State C α ρ → σ → ProjectionForest.State C α ρ → Option (C × List ρ) → Prop
  | readNone {state next forest q} (instruction : program state = .read q next) (absent : forest q = none) :
      Step program state forest (next none) forest none
  | readSome {state next forest q cursor} (instruction : program state = .read q next)
      (present : forest q = some cursor) :
      Step program state forest (next (some (cursor.focus.rootRecord,SourceLocalProgram.isLeaf cursor.focus)))
        forest (some (q,cursor.focus.rootRecord))
  | nav {state next forest q before after action} (instruction : program state = .nav q action next)
      (present : forest q = some before) (moved : SourceLocalProgram.navigate action before = some after) :
      Step program state forest next (Function.update forest q (some after)) none
  | write {state next forest q cursor fresh} (instruction : program state = .write q fresh next)
      (present : forest q = some cursor) :
      Step program state forest next
        (Function.update forest q (some ⟨cursor.focus.setRoot fresh,cursor.ancestors⟩)) none

inductive Run (program : Program σ C ρ) :
    σ → ProjectionForest.State C α ρ → σ → ProjectionForest.State C α ρ → List (C × List ρ) → Nat → Prop
  | halt {state forest} (instruction : program state = .halt) : Run program state forest state forest [] 0
  | next {state middle last before current after entry reads cost}
      (first : Step program state before middle current entry) (rest : Run program middle current last after reads cost) :
      Run program state before last after (entry.toList++reads) (cost+1)

theorem Step.trace {program : Program σ C ρ} {state next : σ}
    {before after : ProjectionForest.State C α ρ} {entry}
    (step : Step program state before next after entry) :
    ∃ cost, ProjectionForest.Trace before entry.toList after cost ∧ cost ≤ 1 := by
  cases step with
  | readNone => exact ⟨0,.nil _,by decide⟩
  | readSome instruction present => exact ⟨1,.read present (.nil _),le_rfl⟩
  | nav instruction present moved => exact ⟨1,.step present (SourceLocalProgram.navigate_sound moved) (.nil _),le_rfl⟩
  | write instruction present => exact ⟨1,.step present (.write _ _ _) (.nil _),le_rfl⟩

theorem Run.trace {program : Program σ C ρ} {state last : σ}
    {before after : ProjectionForest.State C α ρ} {reads cost}
    (run : Run program state before last after reads cost) :
    ∃ actualCost, ProjectionForest.Trace before reads after actualCost ∧ actualCost ≤ cost := by
  induction run with
  | halt => exact ⟨0,.nil _,le_rfl⟩
  | next first rest ih =>
    obtain ⟨firstCost,firstTrace,firstBound⟩ := first.trace
    obtain ⟨lastCost,lastTrace,lastBound⟩ := ih
    exact ⟨_,firstTrace.append lastTrace,by omega⟩

theorem Step.deterministic {program : Program σ C ρ} {state firstState lastState : σ}
    {before firstForest lastForest : ProjectionForest.State C α ρ} {firstRead lastRead}
    (first : Step program state before firstState firstForest firstRead)
    (last : Step program state before lastState lastForest lastRead) :
    firstState = lastState ∧ firstForest = lastForest ∧ firstRead = lastRead := by
  cases first <;> cases last <;> simp_all

end TangoSquared.Paper20261030.ForestLocalProgram
