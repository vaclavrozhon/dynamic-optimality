import DynamicOptimality.MetadataExecution

/-! Local programs over the shared decorated BST. The controller receives
only its registers and a read of the current node (including null-child
flags). It cannot inspect a subtree or jump to an arbitrary address.
Every read, write, adjacent move, and rotation costs one. -/

namespace DynamicOptimality.LocalProgram

open TangoSquared.MTR
open TangoSquared.Paper20261030.Auxiliary

variable {α ρ σ : Type*}

inductive Move where
  | left | right | up | rotateRight | rotateLeft

def navigate {κ : Type*} : Move → Pointer.Cursor κ → Option (Pointer.Cursor κ)
  | .left,⟨.node (.node a x b) y c,rest⟩ => some ⟨.node a x b,.left y c::rest⟩
  | .right,⟨.node a x (.node b y c),rest⟩ => some ⟨.node b y c,.right a x::rest⟩
  | .up,⟨a,.left x b::rest⟩ => some ⟨.node a x b,rest⟩
  | .up,⟨b,.right a x::rest⟩ => some ⟨.node a x b,rest⟩
  | .rotateRight,⟨.node (.node a x b) y c,rest⟩ => some ⟨.node a x (.node b y c),rest⟩
  | .rotateLeft,⟨.node a x (.node b y c),rest⟩ => some ⟨.node (.node a x b) y c,rest⟩
  | _,_ => none

theorem navigate_sound {κ : Type*} {action : Move} {before after : Pointer.Cursor κ}
    (equal : navigate action before = some after) : Pointer.Step before after := by
  rcases before with ⟨focus,rest⟩
  cases action with
  | left =>
    cases focus with
    | empty => simp [navigate] at equal
    | node left x right => cases left with
      | empty => simp [navigate] at equal
      | node a y b => cases Option.some.inj equal; exact .left _ _ _ _ _ _
  | right =>
    cases focus with
    | empty => simp [navigate] at equal
    | node left x right => cases right with
      | empty => simp [navigate] at equal
      | node b y c => cases Option.some.inj equal; exact .right _ _ _ _ _ _
  | up =>
    cases rest with
    | nil => simp [navigate] at equal
    | cons first rest => cases first with
      | left x b => cases Option.some.inj equal; exact .upLeft _ _ _ _
      | right a x => cases Option.some.inj equal; exact .upRight _ _ _ _
  | rotateRight =>
    cases focus with
    | empty => simp [navigate] at equal
    | node left x right => cases left with
      | empty => simp [navigate] at equal
      | node a y b => cases Option.some.inj equal; exact .rotateRight _ _ _ _ _ _
  | rotateLeft =>
    cases focus with
    | empty => simp [navigate] at equal
    | node left x right => cases right with
      | empty => simp [navigate] at equal
      | node b y c => cases Option.some.inj equal; exact .rotateLeft _ _ _ _ _ _

structure View (α ρ : Type*) where
  entry : NodeRecord α (fun _ => ρ)
  leftEmpty : Bool
  rightEmpty : Bool

def empty {κ : Type*} : RawTree κ → Bool
  | .empty => true
  | .node _ _ _ => false

def observe (cursor : Metadata.Cursor α (fun _ => ρ)) : Option (View α ρ) :=
  match cursor.focus with
  | .empty => none
  | .node left entry right => some ⟨entry,empty left,empty right⟩

theorem observe_root {cursor : Metadata.Cursor α (fun _ => ρ)} {view : View α ρ}
    (equal : observe cursor = some view) : cursor.focus.rootKey = some view.entry := by
  rcases cursor with ⟨focus,rest⟩
  cases focus with
  | empty => simp [observe] at equal
  | node left entry right => cases Option.some.inj equal; rfl

inductive Instruction (σ α ρ : Type*) where
  | halt
  | read (next : View α ρ → σ)
  | nav (action : Move) (next : σ)
  | write (fresh : ρ) (next : σ)
  | writeSize (fresh : Nat) (next : σ)

abbrev Program (σ α ρ : Type*) := σ → Instruction σ α ρ

inductive Step (program : Program σ α ρ) : σ → Metadata.Cursor α (fun _ => ρ) →
    σ → Metadata.Cursor α (fun _ => ρ) → Option (NodeRecord α (fun _ => ρ)) → Prop
  | read {state next cursor view} (instruction : program state = .read next)
      (observed : observe cursor = some view) : Step program state cursor (next view) cursor (some view.entry)
  | nav {state next before after action} (instruction : program state = .nav action next)
      (moved : navigate action before = some after) : Step program state before next after none
  | write {state next l r size key old fresh rest} (instruction : program state = .write fresh next) :
      Step program state ⟨.node l (size,⟨key,old⟩) r,rest⟩ next ⟨.node l (size,⟨key,fresh⟩) r,rest⟩ none
  | writeSize {state next l r old fresh entry rest} (instruction : program state = .writeSize fresh next) :
      Step program state ⟨.node l (old,entry) r,rest⟩ next ⟨.node l (fresh,entry) r,rest⟩ none

inductive Run (program : Program σ α ρ) : σ → Metadata.Cursor α (fun _ => ρ) →
    σ → Metadata.Cursor α (fun _ => ρ) → List (NodeRecord α (fun _ => ρ)) → Nat → Prop
  | halt {state cursor} (instruction : program state = .halt) : Run program state cursor state cursor [] 0
  | next {state middle last before current after entry reads cost}
      (first : Step program state before middle current entry)
      (rest : Run program middle current last after reads cost) :
      Run program state before last after (entry.toList++reads) (cost+1)

theorem Step.deterministic {program : Program σ α ρ} {state firstState lastState : σ}
    {before firstCursor lastCursor : Metadata.Cursor α (fun _ => ρ)} {firstRead lastRead}
    (first : Step program state before firstState firstCursor firstRead)
    (last : Step program state before lastState lastCursor lastRead) :
    firstState = lastState ∧ firstCursor = lastCursor ∧ firstRead = lastRead := by
  cases first <;> cases last <;> simp_all

theorem Step.not_halted {program : Program σ α ρ} {state next : σ}
    {before after : Metadata.Cursor α (fun _ => ρ)} {entry}
    (step : Step program state before next after entry) : program state ≠ .halt := by
  cases step <;> simp_all

theorem Run.deterministic {program : Program σ α ρ} {state firstState lastState : σ}
    {before firstCursor lastCursor : Metadata.Cursor α (fun _ => ρ)} {firstReads lastReads firstCost lastCost}
    (first : Run program state before firstState firstCursor firstReads firstCost)
    (last : Run program state before lastState lastCursor lastReads lastCost) :
    firstState = lastState ∧ firstCursor = lastCursor ∧ firstReads = lastReads ∧ firstCost = lastCost := by
  induction first generalizing lastState lastCursor lastReads lastCost with
  | halt stopped =>
    cases last with
    | halt => exact ⟨rfl,rfl,rfl,rfl⟩
    | next move rest => exact False.elim (move.not_halted stopped)
  | next move rest ih =>
    cases last with
    | halt stopped => exact False.elim (move.not_halted stopped)
    | next other more =>
      obtain ⟨rfl,rfl,rfl⟩ := move.deterministic other
      obtain ⟨rfl,rfl,rfl,rfl⟩ := ih more
      exact ⟨rfl,rfl,rfl,rfl⟩

theorem Step.trace {program : Program σ α ρ} {state next : σ} {before after : Metadata.Cursor α (fun _ => ρ)}
    {entry} (step : Step program state before next after entry) :
    Metadata.Trace before entry.toList after 1 := by
  cases step with
  | read instruction observed => exact .read (observe_root observed) (.nil _)
  | nav instruction moved => exact .step (.nav (navigate_sound moved)) (.nil _)
  | write => exact .step (.writeValue _ _ _ _ _ _ _) (.nil _)
  | writeSize => exact .step (.write _ _ _ _ _ _) (.nil _)

theorem Run.trace {program : Program σ α ρ} {state last : σ} {before after : Metadata.Cursor α (fun _ => ρ)}
    {reads cost} (run : Run program state before last after reads cost) : Metadata.Trace before reads after cost := by
  induction run with
  | halt => exact .nil _
  | next first rest ih => simpa only [Nat.add_comm] using first.trace.append ih

end DynamicOptimality.LocalProgram
