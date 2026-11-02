import ChaCha.Paper20261030.CanonicalHeadSuccessor
import ChaCha.Paper20261030.CanonicalRetainedPortFacts

set_option autoImplicit false

/-! Explicit payload framing after balanced head restoration. Updating a
single boundary payload leaves every other depth unchanged. The exact
head-successor predicate then identifies the retained old prefix and
incoming suffix, independently of the balanced shape chosen afterward. -/

namespace ChaCha.Paper20261030.RestoredHeadPayloadFrame

open ColoredStorage SourcePointer Structural PhysicalPacketStaging RepairedPayloadLayouts

variable {β ρ ι η τ : Type*}

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem update_other (payload : Option Bool → Nat → τ) (color : Option Bool)
    (depth : Nat) (replacement : τ) (side : Option Bool) (key : Nat) (different : key ≠ depth) :
    Function.update payload color (Function.update (payload color) depth replacement) side key = payload side key := by
  by_cases same : side = color
  · subst side
    simp only [Function.update_self,Function.update_of_ne different]
  · rw [Function.update_of_ne same]

theorem ports_of_leaf_word {σ υ : Type*} (color : Nat → Option Bool) (side : Bool)
    (before : Source Nat σ) (after : Source Nat υ)
    (same : before.shape.leaves = after.shape.leaves) :
    ports (packed color (some side) before) = ports (packed color (some side) after) := by
  rw [CanonicalRetainedPortFacts.packed_ports,CanonicalRetainedPortFacts.packed_ports,same]

theorem off_boundary (activePayload incomingPayload preparedPayload :
      Option Bool → Nat → Source β (Packet Nat (HeadBoundary.Record ρ η (Option Bool)) ι))
    (head oldTail incomingTail : Bool → ProjectionLocal.Projected Nat (HeadBoundary.Record ρ η (Option Bool)))
    (direction : Bool) (depth : Nat) (records : HeadBoundary.Records ρ η (Option Bool))
    (dormantHeader : Packet Nat (HeadBoundary.Record ρ η (Option Bool)) ι)
    (oldBottom incomingTree dormantTree : Source β (Packet Nat (HeadBoundary.Record ρ η (Option Bool)) ι))
    (oldColor newColor : Option Bool) (side : Bool) (key : Nat) (different : key ≠ depth)
    (headBefore : key ∈ ports (head side) → key < depth)
    (tailAfter : key ∈ ports (incomingTail side) → depth < key)
    (good : CanonicalHeadSuccessor.Payload
      (Function.update activePayload oldColor (Function.update (activePayload oldColor) depth incomingTree))
      incomingPayload head oldTail incomingTail direction depth records dormantHeader oldBottom
      side key (preparedPayload (some side) key)) :
    Function.update preparedPayload newColor (Function.update (preparedPayload newColor) depth dormantTree) (some side) key =
      if key < depth then activePayload (some side) key else incomingPayload (some side) key := by
  rw [update_other preparedPayload newColor depth dormantTree (some side) key different]
  rcases CanonicalHeadSuccessor.off_boundary _ _ _ _ _ _ _ _ _ _ side key _ different good with old | incoming
  · rw [if_pos (headBefore old.1),old.2]
    exact update_other activePayload oldColor depth incomingTree (some side) key different
  · rw [if_neg (by have := tailAfter incoming.1; omega)]
    exact incoming.2

end ChaCha.Paper20261030.RestoredHeadPayloadFrame
