import ChaCha.Paper20261030.SourceProgramComposition
import ChaCha.Paper20261030.ProjectionLocal

/-! Read-only acquisition of bounded record packets. A command reads one
reached vertex and saves a specified slice of its record list. The command
sequence contains adjacent moves and scalar slice offsets, never trees.
-/

namespace ChaCha.Paper20261030.PacketReadController

open ColoredStorage SourcePointer SourceLocalProgram ProjectionLocal
open DynamicOptimality.LocalProgram (Move)

variable {α ρ : Type*}

inductive Command where
  | nav (move : Move)
  | sample (offset count : Nat)

structure State (ρ : Type*) where
  commands : List Command
  saved : List (List ρ)

def program : Program (State ρ) (List ρ)
  | ⟨[],_⟩ => .halt
  | ⟨.nav move::rest,saved⟩ => .nav move ⟨rest,saved⟩
  | ⟨.sample offset count::rest,saved⟩ =>
      .read (fun records _ => ⟨rest,saved++[(records.drop offset).take count]⟩)

def appendState (suffix : List Command) (state : State ρ) : State ρ :=
  ⟨state.commands++suffix,state.saved⟩

theorem append_code (suffix : List Command) (state : State ρ) (active : program state ≠ .halt) :
    program (appendState suffix state) = (program state).mapState (appendState suffix) := by
  rcases state with ⟨commands,saved⟩
  cases commands with
  | nil => exact False.elim (active rfl)
  | cons command rest => cases command <;> rfl

theorem append_runs {first last : List Command} {before middle after : Cursor α (List ρ)}
    {saved found final : List (List ρ)} {xs ys : List (List ρ)} {m n : Nat}
    (front : Run program ⟨first,saved⟩ before ⟨[],found⟩ middle xs m)
    (back : Run program ⟨last,found⟩ middle ⟨[],final⟩ after ys n) :
    Run program ⟨first++last,saved⟩ before ⟨[],final⟩ after (xs++ys) (m+n) :=
  (front.map_prefix (appendState last) (append_code last)).then_run back

def Collects (commands : List Command) (source : Source α (List ρ)) (packets : List (List ρ)) : Prop :=
  ∀ outside saved, ∃ reads, Run program ⟨commands,saved⟩ ⟨source,outside⟩
    ⟨[],saved++packets⟩ ⟨source,outside⟩ reads commands.length

theorem refl (source : Source α (List ρ)) : Collects [] source [] := by
  intro outside saved
  exact ⟨[],by simpa only [List.append_nil,List.length_nil] using (Run.halt (program := program) (state := ⟨[],saved⟩)
    (cursor := ⟨source,outside⟩) rfl)⟩

theorem sample (source : Source α (List ρ)) (offset count : Nat) :
    Collects [.sample offset count] source [(source.rootRecord.drop offset).take count] := by
  intro outside saved
  refine ⟨[source.rootRecord],?_⟩
  exact .next (program := program) (Step.read
    (next := fun records _ => State.mk [] (saved++[(records.drop offset).take count])) rfl) (.halt rfl)

theorem Collects.trans {first last : List Command} {source : Source α (List ρ)} {xs ys : List (List ρ)}
    (front : Collects first source xs) (back : Collects last source ys) :
    Collects (first++last) source (xs++ys) := by
  intro outside saved
  obtain ⟨readsA,runA⟩ := front outside saved
  obtain ⟨readsB,runB⟩ := back outside (saved++xs)
  exact ⟨_,by simpa only [List.length_append,List.append_assoc] using append_runs runA runB⟩

def left (commands : List Command) : List Command := .nav .left::commands++[.nav .up]
def right (commands : List Command) : List Command := .nav .right::commands++[.nav .up]

theorem nav {before after : Cursor α (List ρ)} (move : Move) (saved : List (List ρ))
    (moved : navigate move before = some after) :
    Run program ⟨[.nav move],saved⟩ before ⟨[],saved⟩ after [] 1 :=
  .next (program := program) (.nav rfl moved) (.halt rfl)

theorem Collects.left {commands : List Command} {source sibling : Source α (List ρ)}
    {records : List ρ} {packets : List (List ρ)} (body : Collects commands source packets) :
    Collects (left commands) (.fork records source sibling) packets := by
  intro outside saved
  obtain ⟨reads,run⟩ := body (.left records sibling::outside) saved
  have last := append_runs run (nav (before := ⟨source,.left records sibling::outside⟩) .up (saved++packets) rfl)
  have first : Step program ⟨PacketReadController.left commands,saved⟩ ⟨.fork records source sibling,outside⟩
      ⟨commands++[.nav .up],saved⟩ ⟨source,.left records sibling::outside⟩ none := .nav rfl rfl
  exact ⟨_,by simpa only [PacketReadController.left,List.length_cons,List.length_append,List.length_nil] using Run.next first last⟩

theorem Collects.right {commands : List Command} {source sibling : Source α (List ρ)}
    {records : List ρ} {packets : List (List ρ)} (body : Collects commands source packets) :
    Collects (right commands) (.fork records sibling source) packets := by
  intro outside saved
  obtain ⟨reads,run⟩ := body (.right sibling records::outside) saved
  have last := append_runs run (nav (before := ⟨source,.right sibling records::outside⟩) .up (saved++packets) rfl)
  have first : Step program ⟨PacketReadController.right commands,saved⟩ ⟨.fork records sibling source,outside⟩
      ⟨commands++[.nav .up],saved⟩ ⟨source,.right sibling records::outside⟩ none := .nav rfl rfl
  exact ⟨_,by simpa only [PacketReadController.right,List.length_cons,List.length_append,List.length_nil] using Run.next first last⟩

def ProjectedCollects (commands : List Command) (source : Projected α ρ) (packets : List (List ρ)) : Prop :=
  match source with
  | none => packets = []
  | some source => Collects commands source packets

end ChaCha.Paper20261030.PacketReadController
