import TangoSquared.Paper20261030.SourceContextPositions

/-! Several fingers in one shared, record-decorated source tree.

The configuration's addresses describe physical pointer positions in the
semantics. A running local program receives only a reached record and a
leaf bit. It cannot inspect addresses, paths, or the tree. A rotation
changes the ghost addresses of other fingers so that they stay on their
vertices; it does not traverse those paths. This is an intermediate
constant-finger leaf-oriented model, not the final single-finger BST.
-/

namespace TangoSquared.Paper20261030.MultiSourceProgram

open ColoredStorage SourcePointer SourcePositions
open DynamicOptimality.LocalProgram (Move)

variable {α ρ F σ : Type*} [DecidableEq F]

structure Configuration (F α ρ : Type*) where
  tree : Source α ρ
  fingers : F → Option (List Bool)

def WellFormed (config : Configuration F α ρ) : Prop :=
  ∀ finger position, config.fingers finger = some position → ∃ current, locate config.tree position = some current

def transport (action : Move) (current : Cursor α ρ) : List Bool → List Bool :=
  match action with
  | .rotateRight => underContext current.ancestors rightAddress
  | .rotateLeft => underContext current.ancestors leftAddress
  | .left | .right | .up => id

def moveResult (config : Configuration F α ρ) (finger : F) (action : Move)
    (before after : Cursor α ρ) : Configuration F α ρ :=
  ⟨after.tree,Function.update (fun other => (config.fingers other).map (transport action before)) finger (some (address after))⟩

def writeResult (config : Configuration F α ρ) (current : Cursor α ρ) (fresh : ρ) : Configuration F α ρ :=
  ⟨plug (current.focus.setRoot fresh) current.ancestors,config.fingers⟩

def copyResult (config : Configuration F α ρ) (destination origin : F) : Configuration F α ρ :=
  ⟨config.tree,Function.update config.fingers destination (config.fingers origin)⟩

abbrev View (ρ : Type*) := Option (ρ × Bool)

inductive Instruction (σ F ρ : Type*) where
  | halt
  | read (finger : F) (next : View ρ → σ)
  | nav (finger : F) (action : Move) (next : σ)
  | write (finger : F) (fresh : ρ) (next : σ)
  | copy (destination origin : F) (next : σ)

abbrev Program (σ F ρ : Type*) := σ → Instruction σ F ρ

inductive Step (program : Program σ F ρ) :
    σ → Configuration F α ρ → σ → Configuration F α ρ → Option (F × ρ) → Prop
  | readNone {state config finger next}
      (instruction : program state = .read finger next) (absent : config.fingers finger = none) :
      Step program state config (next none) config none
  | readSome {state config finger position current next}
      (instruction : program state = .read finger next) (present : config.fingers finger = some position)
      (reached : locate config.tree position = some current) :
      Step program state config (next (some (current.focus.rootRecord,SourceLocalProgram.isLeaf current.focus))) config
        (some (finger,current.focus.rootRecord))
  | nav {state config finger position before after action next}
      (instruction : program state = .nav finger action next) (present : config.fingers finger = some position)
      (reached : locate config.tree position = some before)
      (moved : SourceLocalProgram.navigate action before = some after) :
      Step program state config next (moveResult config finger action before after) none
  | write {state config finger position current fresh next}
      (instruction : program state = .write finger fresh next) (present : config.fingers finger = some position)
      (reached : locate config.tree position = some current) :
      Step program state config next (writeResult config current fresh) none
  | copy {state config destination origin next} (instruction : program state = .copy destination origin next) :
      Step program state config next (copyResult config destination origin) none

inductive Run (program : Program σ F ρ) :
    σ → Configuration F α ρ → σ → Configuration F α ρ → List (F × ρ) → Nat → Prop
  | halt {state config} (stopped : program state = .halt) : Run program state config state config [] 0
  | next {state middle last before current after entry reads cost}
      (first : Step program state before middle current entry) (rest : Run program middle current last after reads cost) :
      Run program state before last after (entry.toList++reads) (cost+1)

theorem Step.deterministic {program : Program σ F ρ} {state firstState lastState : σ}
    {before firstConfig lastConfig : Configuration F α ρ} {firstRead lastRead}
    (first : Step program state before firstState firstConfig firstRead)
    (last : Step program state before lastState lastConfig lastRead) :
    firstState = lastState ∧ firstConfig = lastConfig ∧ firstRead = lastRead := by
  cases first <;> cases last <;> simp_all

theorem copy_wellFormed (config : Configuration F α ρ) (valid : WellFormed config) (destination origin : F) :
    WellFormed (copyResult config destination origin) := by
  intro finger position present
  by_cases same : finger = destination
  · subst finger
    exact valid origin position (by simpa only [copyResult,Function.update_self] using present)
  · exact valid finger position (by simpa only [copyResult,Function.update_of_ne same] using present)

end TangoSquared.Paper20261030.MultiSourceProgram
