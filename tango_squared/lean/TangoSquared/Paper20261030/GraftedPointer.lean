import TangoSquared.PointerModel

/-!
# Pointer traces with arbitrary untouched hanging subtrees

An auxiliary skeleton's empty slots are numbered in inorder. `cursor`
fills them with a fixed array of payload trees and places the cursor at
the corresponding skeleton vertex. Every adjacent move, rotation, and
record visit lifts with exactly the same cost. None of the payload
interiors is traversed.
-/

namespace TangoSquared.Paper20261030.PointerGraft

open TangoSquared.MTR

variable {α : Type*}

def extend (c : Pointer.Cursor α) (outside : List (Pointer.Frame α)) : Pointer.Cursor α :=
  ⟨c.focus,c.ancestors ++ outside⟩

theorem step_extend {c d : Pointer.Cursor α} (h : Pointer.Step c d)
    (outside : List (Pointer.Frame α)) : Pointer.Step (extend c outside) (extend d outside) := by
  cases h
  · exact .left _ _ _ _ _ _
  · exact .right _ _ _ _ _ _
  · exact .upLeft _ _ _ _
  · exact .upRight _ _ _ _
  · exact .rotateRight _ _ _ _ _ _
  · exact .rotateLeft _ _ _ _ _ _

def offset : List (Pointer.Frame α) → Nat
  | [] => 0
  | .left _ _ :: rest => offset rest
  | .right l _ :: rest => l.size + 1 + offset rest

def frames (gaps : Nat → MTR.Tree α) (base focusSize : Nat) :
    List (Pointer.Frame α) → List (Pointer.Frame α)
  | [] => []
  | .left key r :: rest =>
    .left key (r.graft gaps (base + offset rest + focusSize + 1)) ::
      frames gaps base (focusSize + 1 + r.size) rest
  | .right l key :: rest =>
    .right (l.graft gaps (base + offset rest)) key ::
      frames gaps base (l.size + 1 + focusSize) rest

def cursor (gaps : Nat → MTR.Tree α) (base : Nat) (c : Pointer.Cursor α) : Pointer.Cursor α :=
  ⟨c.focus.graft gaps (base + offset c.ancestors),frames gaps base c.focus.size c.ancestors⟩

theorem plug_frames (gaps : Nat → MTR.Tree α) (base : Nat)
    (focus : MTR.Tree α) (ancestors : List (Pointer.Frame α)) :
    Pointer.plug (focus.graft gaps (base + offset ancestors)) (frames gaps base focus.size ancestors) =
      (Pointer.plug focus ancestors).graft gaps base := by
  induction ancestors generalizing focus with
  | nil => simp [offset,frames,Pointer.plug]
  | cons frame rest ih =>
    cases frame with
    | left key r =>
      simpa only [offset,frames,Pointer.plug,MTR.Tree.graft,MTR.Tree.size,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (.node focus key r)
    | right l key =>
      simpa only [offset,frames,Pointer.plug,MTR.Tree.graft,MTR.Tree.size,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (.node l key focus)

theorem cursor_tree (gaps : Nat → MTR.Tree α) (base : Nat) (c : Pointer.Cursor α) :
    (cursor gaps base c).tree = c.tree.graft gaps base :=
  plug_frames gaps base c.focus c.ancestors

theorem step {c d : Pointer.Cursor α} (h : Pointer.Step c d)
    (gaps : Nat → MTR.Tree α) (base : Nat) :
    Pointer.Step (cursor gaps base c) (cursor gaps base d) := by
  cases h <;> simp only [cursor,offset,frames,MTR.Tree.graft,MTR.Tree.size]
  all_goals simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  · exact .left _ _ _ _ _ _
  · exact .right _ _ _ _ _ _
  · exact .upLeft _ _ _ _
  · exact .upRight _ _ _ _
  · exact .rotateRight _ _ _ _ _ _
  · exact .rotateLeft _ _ _ _ _ _

theorem trace {c d : Pointer.Cursor α} {word : List α} {cost : Nat}
    (h : Pointer.Trace c word d cost) (gaps : Nat → MTR.Tree α) (base : Nat) :
    Pointer.Trace (cursor gaps base c) word (cursor gaps base d) cost := by
  induction h with
  | nil => exact .nil _
  | step move rest ih => exact .step (step move gaps base) ih
  | serve atKey rest ih => exact .serve (MTR.Tree.graft_rootKey _ _ _ atKey) ih

end TangoSquared.Paper20261030.PointerGraft
