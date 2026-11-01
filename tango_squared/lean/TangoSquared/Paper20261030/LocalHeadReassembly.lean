import TangoSquared.Paper20261030.LocalDecoratedReassembly
import TangoSquared.Paper20261030.HeadBlockReassembly

/-! A fixed local program for the eight exposed original-key blocks of
SwitchHead. Its parameters are the old primary direction, eight presence
bits, and the record prefixes in the two fifteen-vertex contexts. It takes
at most 288 actual moves, rotations, reads, and writes, and returns to the
context root. In particular, no runtime tree or inverse history is used.

This is the reassembly kernel. The primary controller must still acquire
the finite packets locally and establish their structural-metadata meaning.
-/

namespace TangoSquared.Paper20261030.HeadBlocks.Local

open ColoredStorage SourcePointer SourceLocalProgram ProjectionLocal OrderedContext
open LocalProjectedRotation
open LocalRecordActions (Action)

variable {α ρ : Type*}

def actions (oldRight : Bool) (bits : Fin 8 → Bool)
    (oldRecords newRecords : List Bool → List ρ) : List (Action ρ) :=
  OrderedContext.Local.decoratedActions bits
    (recordContext oldRecords [] (before oldRight)) (recordContext newRecords [] (after oldRight))

theorem transforms (oldRight : Bool) (blocks : Fin 8 → Projected α ρ)
    (oldRecords newRecords : List Bool → List ρ) :
    Transforms (actions oldRight (fun key => (blocks key).isSome) oldRecords newRecords)
      (decorated blocks (recordContext oldRecords [] (before oldRight)))
      (decorated blocks (recordContext newRecords [] (after oldRight))) 288 := by
  have actual := OrderedContext.Local.decorated_run blocks
    (recordContext oldRecords [] (before oldRight)) (recordContext newRecords [] (after oldRight))
    (by rw [recordContext_shape,recordContext_shape]; exact block_order oldRight)
  simpa only [actions,recordContext_shape,block_count,Nat.reduceMul] using actual

theorem run (oldRight : Bool) (bits : Fin 8 → Bool) (blocks : Fin 8 → Projected α ρ)
    (known : ∀ key, bits key = (blocks key).isSome)
    (oldRecords newRecords : List Bool → List ρ) (initial final : Source α (List ρ))
    (oldTree : decorated blocks (recordContext oldRecords [] (before oldRight)) = some initial)
    (newTree : decorated blocks (recordContext newRecords [] (after oldRight)) = some final)
    (outside : List (Frame α (List ρ))) :
    ∃ reads cost, Run LocalRecordActions.program
      (.ready (actions oldRight bits oldRecords newRecords)) ⟨initial,outside⟩
      (.ready []) ⟨final,outside⟩ reads cost ∧ cost ≤ 288 := by
  have actual := transforms oldRight blocks oldRecords newRecords
  rw [oldTree,newTree] at actual
  have equal : bits = fun key => (blocks key).isSome := funext known
  rw [equal]
  exact actual outside

end TangoSquared.Paper20261030.HeadBlocks.Local
