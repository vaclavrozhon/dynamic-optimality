import ChaCha.Paper20261030.DecoratedContextReassembly

/-!
# Reassembling the eight unchanged original-key blocks of a head switch

The block indices are: 0 prefix-left, 1 old-tail-left, 2 old bottom,
3 old-tail-right, 4 incoming-tail-left, 5 incoming bottom,
6 incoming-tail-right, and 7 prefix-right. Right blocks are already the
mirrored routing projections with their original-key payloads attached.

Before the switch the incoming three-block component is nested at the
boundary exit; afterward the old three-block component is nested there.
Both possible primary directions give the same ordered block word on
each side. Empty blocks are allowed. All supplied connector-record
changes and the routing reassembly cost at most 288 actual steps.
-/

namespace ChaCha.Paper20261030.HeadBlocks

open ColoredStorage ProjectionLocal OrderedContext

abbrev Shape := Source (Fin 8) Unit

private def slot (i : Fin 8) : Shape := .leaf i ()
private def fork (l r : Shape) : Shape := .fork () l r

def oldTail : Shape := fork (fork (slot 1) (slot 2)) (slot 3)
def incomingTail : Shape := fork (fork (slot 4) (slot 5)) (slot 6)

def before : Bool → Shape
  | false => fork (fork (fork (slot 0) (slot 1)) (slot 2))
      (fork (fork (slot 3) incomingTail) (slot 7))
  | true => fork (fork (fork (slot 0) (fork incomingTail (slot 1))) (slot 2))
      (fork (slot 3) (slot 7))

def after : Bool → Shape
  | false => fork (fork (fork (slot 0) (fork oldTail (slot 4))) (slot 5))
      (fork (slot 6) (slot 7))
  | true => fork (fork (fork (slot 0) (slot 4)) (slot 5))
      (fork (fork (slot 6) oldTail) (slot 7))

theorem block_order (oldRight : Bool) : (before oldRight).shape.leaves = (after oldRight).shape.leaves := by
  cases oldRight <;> rfl

theorem block_count (oldRight : Bool) : (before oldRight).shape.leaves.length = 8 := by
  cases oldRight <;> rfl

variable {α ρ : Type*}

/-- Addresses identify only the constant-size exposed context. This
function supplies desired record prefixes; it is not a runtime pointer. -/
def recordContext (records : List Bool → List ρ) (address : List Bool) : Shape → Source (Fin 8) (List ρ)
  | .leaf key _ => .leaf key (records address)
  | .fork _ l r => .fork (records address)
      (recordContext records (address ++ [false]) l) (recordContext records (address ++ [true]) r)

theorem recordContext_shape (records : List Bool → List ρ) (address : List Bool) (t : Shape) :
    (recordContext records address t).shape = t.shape := by
  induction t generalizing address <;> simp_all [recordContext,Source.shape]

theorem head_reassembly (oldRight : Bool) (blocks : Fin 8 → Projected α ρ)
    (oldRecords newRecords : List Bool → List ρ) :
    Rearranges (decorated blocks (recordContext oldRecords [] (before oldRight)))
      (decorated blocks (recordContext newRecords [] (after oldRight))) 288 := by
  exact reassemble_decorated blocks _ _
    (by rw [recordContext_shape,recordContext_shape]; exact block_order oldRight) 8
    (by rw [recordContext_shape]; exact block_count oldRight)

end ChaCha.Paper20261030.HeadBlocks
