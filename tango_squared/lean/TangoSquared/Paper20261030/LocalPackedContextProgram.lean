import TangoSquared.Paper20261030.LocalPackedPrefix
import TangoSquared.Paper20261030.LocalRecordActions

/-! Running a local projected kernel in its actual packed ancestor
context. The program reads and detaches the ancestor prefix, runs the
fixed action list, and reads and restores the saved prefix at the new
projected root. Context acquisition adds exactly four commands.
-/

namespace TangoSquared.Paper20261030.PackedContextController

open ColoredStorage SourcePointer SourceLocalProgram ProjectionLocal
open LocalRecordActions (Action)

variable {α ρ C : Type*} [LinearOrder C]

inductive State (ρ : Type*) where
  | detaching (phase : PackedPrefixController.State ρ)
  | running (extras : List ρ) (phase : LocalRecordActions.State ρ)
  | done

def finishActions (extras : List ρ) : LocalRecordActions.State ρ → State ρ
  | .ready [] => .done
  | phase => .running extras phase

def finishPrefix (actions : List (Action ρ)) : PackedPrefixController.State ρ → State ρ
  | .done extras => finishActions extras (.ready (actions++[.prepend extras]))
  | phase => .detaching phase

def program (mask : ρ → Finset C) (inside : Finset C) (actions : List (Action ρ)) : Program (State ρ) (List ρ)
  | .detaching phase => (PackedPrefixController.program mask inside phase).mapState (finishPrefix actions)
  | .running extras phase => (LocalRecordActions.program phase).mapState (finishActions extras)
  | .done => .halt

theorem prefix_code (mask : ρ → Finset C) (inside : Finset C) (actions : List (Action ρ))
    (phase : PackedPrefixController.State ρ) (active : PackedPrefixController.program mask inside phase ≠ .halt) :
    program mask inside actions (finishPrefix actions phase) =
      (PackedPrefixController.program mask inside phase).mapState (finishPrefix actions) := by
  cases phase with
  | done => exact False.elim (active rfl)
  | start | writing => rfl

theorem action_code (mask : ρ → Finset C) (inside : Finset C) (actions : List (Action ρ))
    (extras : List ρ) (phase : LocalRecordActions.State ρ) (active : LocalRecordActions.program phase ≠ .halt) :
    program mask inside actions (finishActions extras phase) =
      (LocalRecordActions.program phase).mapState (finishActions extras) := by
  cases phase with
  | writing => rfl
  | ready actions => cases actions with
    | nil => exact False.elim (active rfl)
    | cons => rfl

theorem lift [DecidableEq α] (mask : ρ → Finset C) (color : α → C) (q : C)
    (before after : Source α ρ) (outside : List (Frame α ρ))
    (sameColors : before.support color = after.support color)
    (correct : ColorsCorrect mask color (plug before outside))
    (a b : Source α (List ρ)) (packedBefore : packed color q before = some a) (packedAfter : packed color q after = some b)
    (actions : List (Action ρ)) (budget : Nat) (kernel : LocalRecordActions.Rearranges actions a b budget)
    (physical : Cursor α (List ρ)) (represented : ColoredStorage.Represents color q ⟨before,outside⟩ physical) :
    ∃ target reads cost,
      Run (program mask (before.support color) actions) (.detaching .start) physical .done target reads cost ∧
      ColoredStorage.Represents color q ⟨after,outside⟩ target ∧ cost ≤ budget+4 := by
  obtain ⟨extras,rest,wholeBefore,wholeAfter,frames⟩ := packed_cursor_context color q sameColors packedBefore packedAfter outside
  have beforeRep := represents_of_context color q before outside packedBefore extras rest wholeBefore frames
  have afterRep := represents_of_context color q after outside packedAfter extras rest wholeAfter frames
  have equal := Represents.unique color q ⟨before,outside⟩ represented beforeRep
  have present : q ∈ before.support color := by
    by_contra missing
    have absent := (packed_none_iff color q before).mpr missing
    rw [packedBefore] at absent
    cases absent
  obtain ⟨found,stored,ancestors,foundPacking,storedContext,detach⟩ :=
    PackedPrefixController.detach mask color q ⟨before,outside⟩ correct present physical represented
  have sameTree : found = a := Option.some.inj (foundPacking.symm.trans packedBefore)
  subst found
  have contexts : (⟨prepend stored a,ancestors⟩ : Cursor α (List ρ)) = ⟨prepend extras a,rest⟩ := storedContext.symm.trans equal
  have sameAncestors : ancestors = rest := congrArg Cursor.ancestors contexts
  subst ancestors
  have rootEquality := congrArg (fun (current : Cursor α (List ρ)) => current.focus.rootRecord) contexts
  have rootAppend : ∀ xs : List ρ, (prepend xs a).rootRecord = xs++a.rootRecord := by intro xs; cases a <;> rfl
  change (prepend stored a).rootRecord = (prepend extras a).rootRecord at rootEquality
  rw [rootAppend,rootAppend] at rootEquality
  have samePrefix : stored = extras := List.append_cancel_right rootEquality
  subst stored
  have first := detach.map_prefix (finishPrefix actions) (prefix_code mask (before.support color) actions)
  obtain ⟨kernelReads,kernelCost,body,bounded⟩ := kernel rest
  have restored := LocalRecordActions.append_runs body (LocalRecordActions.prepend extras b rest)
  have last := restored.map_prefix (finishActions extras) (action_code mask (before.support color) actions extras)
  have whole := (first.append last).run rfl
  exact ⟨⟨prepend extras b,rest⟩,_,_,whole,afterRep,by omega⟩

end TangoSquared.Paper20261030.PackedContextController
