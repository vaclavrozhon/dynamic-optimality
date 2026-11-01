import TangoSquared.Paper20261030.SourceProgramComposition

/-! Finite scripts whose edits read the reached record before writing
its locally computed replacement. Descriptors contain scalar control
data, such as a prefix length; a tree or prescribed record is not an
instruction. The interpreter keeps at most one pending record.
-/

namespace TangoSquared.Paper20261030.RecordEditScript

open ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ δ : Type*}

inductive Command (δ : Type*) where
  | edit (descriptor : δ)
  | move (action : DynamicOptimality.LocalProgram.Move)

inductive State (δ ρ : Type*) where
  | running (commands : List (Command δ))
  | writing (fresh : ρ) (commands : List (Command δ))

def program (edit : δ → ρ → ρ) : Program (State δ ρ) ρ
  | .running [] => .halt
  | .running (.edit descriptor :: rest) => .read (fun record _ => .writing (edit descriptor record) rest)
  | .running (.move action :: rest) => .nav action (.running rest)
  | .writing fresh rest => .write fresh (.running rest)

def appendState (tail : List (Command δ)) : State δ ρ → State δ ρ
  | .running commands => .running (commands++tail)
  | .writing fresh commands => .writing fresh (commands++tail)

theorem append_code (edit : δ → ρ → ρ) (tail : List (Command δ)) (state : State δ ρ)
    (active : program edit state ≠ .halt) :
    program edit (appendState tail state) = (program edit state).mapState (appendState tail) := by
  cases state with
  | writing => rfl
  | running commands => cases commands with
    | nil => exact False.elim (active rfl)
    | cons command rest => cases command <;> rfl

def Transforms (edit : δ → ρ → ρ) (commands : List (Command δ))
    (before after : Source α ρ) (cost : Nat) : Prop :=
  ∀ outside, ∃ reads, Run (program edit) (.running commands) ⟨before,outside⟩
    (.running []) ⟨after,outside⟩ reads cost

theorem Transforms.refl (edit : δ → ρ → ρ) (source : Source α ρ) : Transforms edit [] source source 0 :=
  fun _ => ⟨[],.halt rfl⟩

theorem Transforms.edit (edit : δ → ρ → ρ) (descriptor : δ) (source : Source α ρ) :
    Transforms edit [.edit descriptor] source (source.setRoot (edit descriptor source.rootRecord)) 2 := by
  intro outside
  refine ⟨[source.rootRecord],?_⟩
  refine .next (Step.read (program := program edit) (next := fun record _ => State.writing (edit descriptor record) []) rfl) ?_
  exact .next (Step.write (program := program edit) rfl) (.halt rfl)

theorem Transforms.append {edit : δ → ρ → ρ} {first last : List (Command δ)}
    {before middle after : Source α ρ} {firstCost lastCost}
    (front : Transforms edit first before middle firstCost) (back : Transforms edit last middle after lastCost) :
    Transforms edit (first++last) before after (firstCost+lastCost) := by
  intro outside
  obtain ⟨frontReads,frontRun⟩ := front outside
  obtain ⟨backReads,backRun⟩ := back outside
  exact ⟨_,(frontRun.map_prefix (appendState last) (append_code edit last)).then_run backRun⟩

def left (commands : List (Command δ)) : List (Command δ) := .move .left :: commands ++ [.move .up]
def right (commands : List (Command δ)) : List (Command δ) := .move .right :: commands ++ [.move .up]

theorem Transforms.left {edit : δ → ρ → ρ} {commands : List (Command δ)} {before after : Source α ρ} {cost}
    (body : Transforms edit commands before after cost) (record : ρ) (sibling : Source α ρ) :
    Transforms edit (left commands) (.fork record before sibling) (.fork record after sibling) (cost+2) := by
  intro outside
  obtain ⟨reads,run⟩ := body (.left record sibling :: outside)
  have down : SourceLocalProgram.Step (program edit) (.running (RecordEditScript.left commands)) ⟨.fork record before sibling,outside⟩
      (.running (commands++[.move .up])) ⟨before,.left record sibling :: outside⟩ none := .nav rfl rfl
  have up : Run (program edit) (.running [.move .up]) ⟨after,.left record sibling :: outside⟩
      (.running []) ⟨.fork record after sibling,outside⟩ [] 1 :=
    .next (Step.nav (program := program edit) (action := .up) (next := State.running []) rfl rfl) (.halt rfl)
  have actual := Run.next down ((run.map_prefix (appendState [.move .up]) (append_code edit [.move .up])).then_run up)
  exact ⟨reads,by simpa only [Option.toList_none,List.nil_append,List.append_nil,Nat.add_assoc] using actual⟩

theorem Transforms.right {edit : δ → ρ → ρ} {commands : List (Command δ)} {before after : Source α ρ} {cost}
    (body : Transforms edit commands before after cost) (record : ρ) (sibling : Source α ρ) :
    Transforms edit (right commands) (.fork record sibling before) (.fork record sibling after) (cost+2) := by
  intro outside
  obtain ⟨reads,run⟩ := body (.right sibling record :: outside)
  have down : SourceLocalProgram.Step (program edit) (.running (RecordEditScript.right commands)) ⟨.fork record sibling before,outside⟩
      (.running (commands++[.move .up])) ⟨before,.right sibling record :: outside⟩ none := .nav rfl rfl
  have up : Run (program edit) (.running [.move .up]) ⟨after,.right sibling record :: outside⟩
      (.running []) ⟨.fork record sibling after,outside⟩ [] 1 :=
    .next (Step.nav (program := program edit) (action := .up) (next := State.running []) rfl rfl) (.halt rfl)
  have actual := Run.next down ((run.map_prefix (appendState [.move .up]) (append_code edit [.move .up])).then_run up)
  exact ⟨reads,by simpa only [Option.toList_none,List.nil_append,List.append_nil,Nat.add_assoc] using actual⟩

def workingRecords : State δ ρ → Nat
  | .running _ => 0
  | .writing _ _ => 1

theorem working_records (state : State δ ρ) : workingRecords state ≤ 1 := by
  cases state <;> simp only [workingRecords] <;> omega

end TangoSquared.Paper20261030.RecordEditScript
