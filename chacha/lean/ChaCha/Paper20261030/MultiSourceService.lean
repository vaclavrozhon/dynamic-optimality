import ChaCha.Paper20261030.MultiSourceComposition

/-! Service means reading the requested actual leaf in the shared tree.
It is stronger than finding a matching value in a record log. The final
read wrapper adds exactly one charged observation at a designated finger.
-/

namespace ChaCha.Paper20261030.MultiSourceProgram

open ColoredStorage SourcePointer SourcePositions

variable {α ρ F σ : Type*} [DecidableEq F]

inductive Serves (program : Program σ F ρ) (key : α) :
    σ → Configuration F α ρ → σ → Configuration F α ρ → List (F × ρ) → Nat → Prop
  | read {state last before after finger position record outside next reads cost}
      (instruction : program state = .read finger next)
      (present : before.fingers finger = some position)
      (reached : locate before.tree position = some ⟨.leaf key record,outside⟩)
      (rest : Run program (next (some (record,true))) before last after reads cost) :
      Serves program key state before last after ((finger,record)::reads) (cost+1)
  | next {state middle last before current after entry reads cost}
      (first : Step program state before middle current entry)
      (rest : Serves program key middle current last after reads cost) :
      Serves program key state before last after (entry.toList++reads) (cost+1)

theorem Serves.run {program : Program σ F ρ} {key : α} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (service : Serves program key state before last after reads cost) : Run program state before last after reads cost := by
  induction service with
  | read instruction present reached rest => exact .next (.readSome instruction present reached) rest
  | next first rest ih => exact .next first ih

theorem Steps.then_serves {program : Program σ F ρ} {key : α} {state middle last : σ}
    {before current after : Configuration F α ρ} {firstReads lastReads firstCost lastCost}
    (first : Steps program state before middle current firstReads firstCost)
    (service : Serves program key middle current last after lastReads lastCost) :
    Serves program key state before last after (firstReads++lastReads) (firstCost+lastCost) := by
  induction first with
  | nil => simpa using service
  | next step rest ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using Serves.next step (ih service)

theorem Run.halted {program : Program σ F ρ} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run program state before last after reads cost) : program last = .halt := by
  induction run with
  | halt stopped => exact stopped
  | next first rest ih => exact ih

end ChaCha.Paper20261030.MultiSourceProgram

namespace ChaCha.Paper20261030.ReadCompletionController

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram

variable {α ρ F σ : Type*} [DecidableEq F]

def program (source : Program σ F ρ) (finger : F) : Program (Option σ) F ρ
  | none => .halt
  | some state => match source state with
    | .halt => .read finger (fun _ => none)
    | instruction => instruction.mapState some

theorem code (source : Program σ F ρ) (finger : F) (state : σ) (running : source state ≠ .halt) :
    program source finger (some state) = (source state).mapState some := by
  cases instruction : source state <;> simp_all [program]

theorem serve (source : Program σ F ρ) (finger : F) {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost) (key : α) (record : ρ)
    (position : List Bool) (outside : List (Frame α ρ))
    (present : after.fingers finger = some position)
    (reached : locate after.tree position = some ⟨.leaf key record,outside⟩) :
    Serves (program source finger) key (some state) before none after (reads++[(finger,record)]) (cost+1) := by
  have steps := run.map_prefix some (code source finger)
  have finalRead : Serves (program source finger) key (some last) after none after [(finger,record)] 1 :=
    .read (next := fun _ => none) (by simp only [program,run.halted]) present reached (.halt rfl)
  exact steps.then_serves finalRead

end ChaCha.Paper20261030.ReadCompletionController
