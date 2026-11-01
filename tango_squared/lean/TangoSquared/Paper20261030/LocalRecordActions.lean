import TangoSquared.Paper20261030.SourceProgramComposition
import TangoSquared.Paper20261030.ProjectionLocal

/-! A small local instruction list for projected rotation kernels.
An action is an adjacent move, removal of the first record, or insertion
of a supplied bounded prefix. Every list edit first reads the actual
vertex. The rotation constructor supplies a fixed-length list determined
by observed color masks; it does not receive a tree or an execution trace.
-/

namespace TangoSquared.Paper20261030.LocalRecordActions

open ColoredStorage SourcePointer SourceLocalProgram
open DynamicOptimality.LocalProgram (Move)

variable {α ρ : Type*}

inductive Action (ρ : Type*) where
  | nav (move : Move)
  | pop
  | drop (count : Nat)
  | prepend (records : List ρ)

inductive State (ρ : Type*) where
  | ready (actions : List (Action ρ))
  | writing (records : List ρ) (rest : List (Action ρ))

def program : Program (State ρ) (List ρ)
  | .ready [] => .halt
  | .ready (.nav move::rest) => .nav move (.ready rest)
  | .ready (.pop::rest) => .read (fun records _ => .writing records.tail rest)
  | .ready (.drop count::rest) => .read (fun records _ => .writing (records.drop count) rest)
  | .ready (.prepend prefixRecords::rest) => .read (fun records _ => .writing (prefixRecords++records) rest)
  | .writing records rest => .write records (.ready rest)

def appendState (suffix : List (Action ρ)) : State ρ → State ρ
  | .ready actions => .ready (actions++suffix)
  | .writing records rest => .writing records (rest++suffix)

theorem append_code (suffix : List (Action ρ)) (state : State ρ) (active : program state ≠ .halt) :
    program (appendState suffix state) = (program state).mapState (appendState suffix) := by
  cases state with
  | writing => rfl
  | ready actions => cases actions with
    | nil => exact False.elim (active rfl)
    | cons action rest => cases action <;> rfl

theorem append_runs {first last : List (Action ρ)} {before middle after : Cursor α (List ρ)}
    {firstReads lastReads firstCost lastCost}
    (front : Run program (.ready first) before (.ready []) middle firstReads firstCost)
    (back : Run program (.ready last) middle (.ready []) after lastReads lastCost) :
    Run program (.ready (first++last)) before (.ready []) after (firstReads++lastReads) (firstCost+lastCost) :=
  (front.map_prefix (appendState last) (append_code last)).then_run back

theorem nav {before after : Cursor α (List ρ)} (move : Move) (moved : navigate move before = some after) :
    Run program (.ready [.nav move]) before (.ready []) after [] 1 :=
  .next (program := program) (.nav rfl moved) (.halt rfl)

theorem pop (focus : Source α (List ρ)) (outside : List (Frame α (List ρ))) :
    Run program (.ready [.pop]) ⟨focus,outside⟩ (.ready [])
      ⟨focus.setRoot focus.rootRecord.tail,outside⟩ [focus.rootRecord] 2 := by
  have first : Step program (.ready [.pop]) ⟨focus,outside⟩ (.writing focus.rootRecord.tail [])
      ⟨focus,outside⟩ (some focus.rootRecord) := .read (program := program)
        (next := fun (records : List ρ) _ => State.writing records.tail []) rfl
  exact .next first (.next (program := program) (.write rfl) (.halt rfl))

theorem prepend (records : List ρ) (focus : Source α (List ρ)) (outside : List (Frame α (List ρ))) :
    Run program (.ready [.prepend records]) ⟨focus,outside⟩ (.ready [])
      ⟨focus.setRoot (records++focus.rootRecord),outside⟩ [focus.rootRecord] 2 := by
  have first : Step program (.ready [.prepend records]) ⟨focus,outside⟩ (.writing (records++focus.rootRecord) [])
      ⟨focus,outside⟩ (some focus.rootRecord) := .read (program := program)
        (next := fun (old : List ρ) _ => State.writing (records++old) []) rfl
  exact .next first (.next (program := program) (.write rfl) (.halt rfl))

theorem drop (count : Nat) (focus : Source α (List ρ)) (outside : List (Frame α (List ρ))) :
    Run program (.ready [.drop count]) ⟨focus,outside⟩ (.ready [])
      ⟨focus.setRoot (focus.rootRecord.drop count),outside⟩ [focus.rootRecord] 2 := by
  have first : Step program (.ready [.drop count]) ⟨focus,outside⟩
      (.writing (focus.rootRecord.drop count) []) ⟨focus,outside⟩ (some focus.rootRecord) :=
    .read (program := program)
      (next := fun (records : List ρ) _ => State.writing (records.drop count) []) rfl
  exact .next first (.next (program := program) (.write rfl) (.halt rfl))

def Rearranges (actions : List (Action ρ)) (before after : Source α (List ρ)) (budget : Nat) : Prop :=
  ∀ outside : List (Frame α (List ρ)), ∃ reads cost,
    Run program (.ready actions) ⟨before,outside⟩ (.ready []) ⟨after,outside⟩ reads cost ∧ cost ≤ budget

theorem refl (source : Source α (List ρ)) (budget : Nat) : Rearranges [] source source budget :=
  fun _ => ⟨[],0,.halt rfl,Nat.zero_le _⟩

theorem Rearranges.mono {actions : List (Action ρ)} {before after : Source α (List ρ)} {m n : Nat}
    (execution : Rearranges actions before after m) (bound : m ≤ n) : Rearranges actions before after n := by
  intro outside
  obtain ⟨reads,cost,run,bounded⟩ := execution outside
  exact ⟨reads,cost,run,bounded.trans bound⟩

theorem Rearranges.trans {first last : List (Action ρ)} {a b c : Source α (List ρ)} {m n : Nat}
    (front : Rearranges first a b m) (back : Rearranges last b c n) : Rearranges (first++last) a c (m+n) := by
  intro outside
  obtain ⟨xs,x,runX,boundX⟩ := front outside
  obtain ⟨ys,y,runY,boundY⟩ := back outside
  exact ⟨xs++ys,x+y,append_runs runX runY,by omega⟩

def left (actions : List (Action ρ)) : List (Action ρ) := .nav .left :: actions ++ [.nav .up]
def right (actions : List (Action ρ)) : List (Action ρ) := .nav .right :: actions ++ [.nav .up]

theorem Rearranges.left {actions : List (Action ρ)} {a b sibling : Source α (List ρ)} {records : List ρ} {n : Nat}
    (body : Rearranges actions a b n) : Rearranges (left actions) (.fork records a sibling) (.fork records b sibling) (n+2) := by
  intro outside
  obtain ⟨reads,cost,run,bounded⟩ := body (.left records sibling::outside)
  have tail := append_runs run (nav (before := ⟨b,.left records sibling::outside⟩) .up rfl)
  have first : Step program (.ready (LocalRecordActions.left actions)) ⟨.fork records a sibling,outside⟩
      (.ready (actions++[.nav .up])) ⟨a,.left records sibling::outside⟩ none := .nav rfl rfl
  exact ⟨_,_,Run.next first tail,by omega⟩

theorem Rearranges.right {actions : List (Action ρ)} {a b sibling : Source α (List ρ)} {records : List ρ} {n : Nat}
    (body : Rearranges actions a b n) : Rearranges (right actions) (.fork records sibling a) (.fork records sibling b) (n+2) := by
  intro outside
  obtain ⟨reads,cost,run,bounded⟩ := body (.right sibling records::outside)
  have tail := append_runs run (nav (before := ⟨b,.right sibling records::outside⟩) .up rfl)
  have first : Step program (.ready (LocalRecordActions.right actions)) ⟨.fork records sibling a,outside⟩
      (.ready (actions++[.nav .up])) ⟨a,.right sibling records::outside⟩ none := .nav rfl rfl
  exact ⟨_,_,Run.next first tail,by omega⟩

end TangoSquared.Paper20261030.LocalRecordActions
