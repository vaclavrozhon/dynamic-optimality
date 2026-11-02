import ChaCha.Paper20261030.VirtualCursorSize
import ChaCha.Paper20261030.PackedForest
import ChaCha.Paper20261030.PackedPrimaryRepresentation

/-!
# The maintained virtual color cursor gives the complete physical header

The synchronized forest invariant supplies the actual virtual projection,
including its current cursor. At most two virtual depth leaves and the
three-color storage theorem give the checked constant-size header value.
This representation retains information omitted by a flat record list.
-/

namespace ChaCha.Paper20261030.ColoredStorage

open SourcePointer RouterProjection

variable {α ρ : Type*} [DecidableEq α]

local instance virtualCursorColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

def virtualCursor (color : α → Option Bool) (source : Cursor α ρ)
    (state : ProjectionForest.State (Option Bool) α ρ)
    (represented : ProjectionForest.Represents color source state)
    (small : virtualCount color source.tree ≤ 2) : VirtualCursor α ρ where
  actual := state none
  small := by
    intro actual present
    have valid := represented none
    rw [present] at valid
    have shape := packed_shape color none source.tree valid.1
    rw [shape,Router.leaves_prune]
    have predicates : (fun key => decide (color key = none)) = (fun key => (color key).isNone) := by
      funext key
      cases color key <;> rfl
    change (source.tree.shape.leaves.filter (fun key => decide (color key = none))).length ≤ 2
    rw [predicates]
    exact small
  bounded := by
    intro actual present
    have valid := represented none
    rw [present] at valid
    change actual.tree.toStored.Bounded 3
    rw [packed_toStored color none source.tree valid.1]
    simpa using pack_bounded_colors color none source.tree

theorem virtualCursor_actual (color : α → Option Bool) (source : Cursor α ρ)
    (state : ProjectionForest.State (Option Bool) α ρ)
    (represented : ProjectionForest.Represents color source state)
    (small : virtualCount color source.tree ≤ 2) :
    (virtualCursor color source state represented small).actual = state none := rfl

end ChaCha.Paper20261030.ColoredStorage

namespace ChaCha.Paper20261030.PackedPrimary

open ColoredStorage PreferredProjection

variable {α ρ : Type*} [DecidableEq α]

local instance virtualHeaderColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
def Input.virtualHeader {t : PrefRouter α} (input : Input t ρ) : VirtualCursor Nat ρ :=
  virtualCursor (color input.start t) ⟨input.source,[]⟩
    (ProjectionForest.roots (color input.start t) input.source)
    (ProjectionForest.represents_roots (color input.start t) input.source)
    (virtual_bound input.start t input.source input.ports input.size)

end ChaCha.Paper20261030.PackedPrimary
