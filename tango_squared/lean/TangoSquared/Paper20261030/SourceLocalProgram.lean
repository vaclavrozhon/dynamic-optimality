import TangoSquared.Paper20261030.SourcePointer
import DynamicOptimality.LocalProgram

/-! Local controllers on the existing nonempty leaf-oriented source tree.
A read returns only the current record and whether the focus is a leaf.
Programs cannot inspect a source subtree. This interface is the source
language for the ordinary-BST controller compiler. -/

namespace TangoSquared.Paper20261030.SourceLocalProgram

open ColoredStorage SourcePointer
open DynamicOptimality.LocalProgram (Move)

variable {α ρ σ : Type*}

def isLeaf : Source α ρ → Bool
  | .leaf _ _ => true
  | .fork _ _ _ => false

def navigate : Move → Cursor α ρ → Option (Cursor α ρ)
  | .left,⟨.fork record l r,rest⟩ => some ⟨l,.left record r::rest⟩
  | .right,⟨.fork record l r,rest⟩ => some ⟨r,.right l record::rest⟩
  | .up,⟨l,.left record r::rest⟩ => some ⟨.fork record l r,rest⟩
  | .up,⟨r,.right l record::rest⟩ => some ⟨.fork record l r,rest⟩
  | .rotateRight,⟨.fork q (.fork p u v) w,rest⟩ => some ⟨.fork p u (.fork q v w),rest⟩
  | .rotateLeft,⟨.fork p u (.fork q v w),rest⟩ => some ⟨.fork q (.fork p u v) w,rest⟩
  | _,_ => none

theorem navigate_sound {action : Move} {before after : Cursor α ρ}
    (equal : navigate action before = some after) : SourcePointer.Step before after := by
  rcases before with ⟨focus,rest⟩
  cases action with
  | left => cases focus with
    | leaf => simp [navigate] at equal
    | fork record l r => cases Option.some.inj equal; exact .left _ _ _ _
  | right => cases focus with
    | leaf => simp [navigate] at equal
    | fork record l r => cases Option.some.inj equal; exact .right _ _ _ _
  | up => cases rest with
    | nil => simp [navigate] at equal
    | cons first rest => cases first with
      | left record r => cases Option.some.inj equal; exact .upLeft _ _ _ _
      | right l record => cases Option.some.inj equal; exact .upRight _ _ _ _
  | rotateRight => cases focus with
    | leaf => simp [navigate] at equal
    | fork q l w => cases l with
      | leaf => simp [navigate] at equal
      | fork p u v => cases Option.some.inj equal; exact .rotateRight _ _ _ _ _ _
  | rotateLeft => cases focus with
    | leaf => simp [navigate] at equal
    | fork p u r => cases r with
      | leaf => simp [navigate] at equal
      | fork q v w => cases Option.some.inj equal; exact .rotateLeft _ _ _ _ _ _

inductive Instruction (σ ρ : Type*) where
  | halt
  | read (next : ρ → Bool → σ)
  | nav (action : Move) (next : σ)
  | write (fresh : ρ) (next : σ)

abbrev Program (σ ρ : Type*) := σ → Instruction σ ρ

inductive Step (program : Program σ ρ) : σ → Cursor α ρ → σ → Cursor α ρ → Option ρ → Prop
  | read {state next cursor} (instruction : program state = .read next) :
      Step program state cursor (next cursor.focus.rootRecord (isLeaf cursor.focus)) cursor (some cursor.focus.rootRecord)
  | nav {state next before after action} (instruction : program state = .nav action next)
      (moved : navigate action before = some after) : Step program state before next after none
  | write {state next cursor fresh} (instruction : program state = .write fresh next) :
      Step program state cursor next ⟨cursor.focus.setRoot fresh,cursor.ancestors⟩ none

inductive Run (program : Program σ ρ) : σ → Cursor α ρ → σ → Cursor α ρ → List ρ → Nat → Prop
  | halt {state cursor} (instruction : program state = .halt) : Run program state cursor state cursor [] 0
  | next {state middle last before current after entry reads cost}
      (first : Step program state before middle current entry) (rest : Run program middle current last after reads cost) :
      Run program state before last after (entry.toList++reads) (cost+1)

theorem Step.trace {program : Program σ ρ} {state next : σ} {before after : Cursor α ρ} {entry}
    (step : Step program state before next after entry) : SourcePointer.Trace before entry.toList after 1 := by
  cases step with
  | read => exact .read (.nil _)
  | nav instruction moved => exact .step (navigate_sound moved) (.nil _)
  | write => exact .step (.write _ _ _) (.nil _)

theorem Run.trace {program : Program σ ρ} {state last : σ} {before after : Cursor α ρ} {reads cost}
    (run : Run program state before last after reads cost) : SourcePointer.Trace before reads after cost := by
  induction run with
  | halt => exact .nil _
  | next first rest ih => simpa only [Nat.add_comm] using first.trace.append ih

theorem Step.deterministic {program : Program σ ρ} {state firstState lastState : σ}
    {before firstCursor lastCursor : Cursor α ρ} {firstRead lastRead}
    (first : Step program state before firstState firstCursor firstRead)
    (last : Step program state before lastState lastCursor lastRead) :
    firstState = lastState ∧ firstCursor = lastCursor ∧ firstRead = lastRead := by
  cases first <;> cases last <;> simp_all

end TangoSquared.Paper20261030.SourceLocalProgram
