import TangoSquared.VineTour

/-!
# A closed broadcast tour through a vine of anchors

One exterior key can be visited between consecutive anchor visits while the
anchors are scanned and the exact original tree is restored.  The construction
uses root and grandchild rotations and preserves arbitrary hanging subtrees.

This file proves only the actual marked rotation trace and its exact length.
It does not assert any owner-indexed flip count or history normalization.
-/

namespace TangoSquared.MTR

open Tree

variable {α : Type*}

/-- A right vine whose final right subtree is retained verbatim. -/
def rightVineWithTail : List α → Tree α → Tree α
  | [], tail => tail
  | x :: xs, tail => .node .empty x (rightVineWithTail xs tail)

/-- The next anchors lie between the current anchor and the broadcast key. -/
def broadcastCheckpoint (left : Tree α) (a : α) (xs : List α) (b : α)
    (gap right : Tree α) : Tree α :=
  .node left a (.node (rightVineWithTail xs gap) b right)

/-- Visit the broadcast key from each anchor, then restore the checkpoint. -/
def broadcastWord (a : α) : List α → α → List α
  | [], b => [b, a]
  | c :: cs, b => [b, a, c] ++ broadcastWord c cs b ++ [a, b, a]

theorem broadcastWord_length (a : α) (xs : List α) (b : α) :
    (broadcastWord a xs b).length = 6 * xs.length + 2 := by
  induction xs generalizing a with
  | nil => simp [broadcastWord]
  | cons c cs ih => simp [broadcastWord, ih]; omega

/-- Visiting a right child and then its former parent restores the tree. -/
theorem broadcast_pair (left middle right : Tree α) (a b : α) :
    MarkedTrace (.node left a (.node middle b right)) [b, a]
      (.node left a (.node middle b right)) 2 :=
  .rotate (.rootLeft left middle right a b)
    (.serve rfl (.rotate (.rootRight left middle right a b)
      (.serve rfl (.nil _))))

/-- Promote the next anchor from the left child of the broadcast key. -/
theorem broadcast_next (left tail right : Tree α) (a c b : α) :
    MarkedTrace (.node left a (.node (.node .empty c tail) b right)) [c]
      (.node (.node left a .empty) c (.node tail b right)) 2 :=
  .rotate (.rightRight left .empty tail right a c b)
    (.rotate (.rootLeft left .empty (.node tail b right) a c)
      (.serve rfl (.nil _)))

/-- The return requests restore the previous checkpoint in four rotations. -/
theorem broadcast_return (left tail right : Tree α) (a c b : α) :
    MarkedTrace (.node (.node left a .empty) c (.node tail b right)) [a, b, a]
      (.node left a (.node (.node .empty c tail) b right)) 4 :=
  .rotate (.rootRight left .empty (.node tail b right) a c)
    (.serve rfl (.rotate (.rightLeft left .empty tail right a c b)
      (.rotate (.rootLeft left (.node .empty c tail) right a b)
        (.serve rfl (.rotate (.rootRight left (.node .empty c tail) right a b)
          (.serve rfl (.nil _)))))))

/-- With `xs.length + 1` anchors, the complete closed tour uses exactly
`6 * xs.length + 2` requests and `8 * xs.length + 2` rotations. -/
theorem closed_broadcast_tour (left : Tree α) (a : α) (xs : List α) (b : α)
    (gap right : Tree α) :
    MarkedTrace (broadcastCheckpoint left a xs b gap right)
      (broadcastWord a xs b) (broadcastCheckpoint left a xs b gap right)
      (8 * xs.length + 2) := by
  induction xs generalizing left a with
  | nil => exact broadcast_pair left gap right a b
  | cons c cs ih =>
    have hp := broadcast_pair left (.node .empty c (rightVineWithTail cs gap))
      right a b
    have hn := broadcast_next left (rightVineWithTail cs gap) right a c b
    have hm := ih (.node left a .empty) c
    have hr := broadcast_return left (rightVineWithTail cs gap) right a c b
    have ht := ((hp.trans hn).trans hm).trans hr
    convert ht using 1 <;>
      simp [broadcastCheckpoint, rightVineWithTail, broadcastWord]
    omega

/-- Every empty slot may hold an arbitrary fixed inorder gap subtree. -/
theorem closed_broadcast_tour_with_gaps
    (left : Tree α) (a : α) (xs : List α) (b : α) (gap right : Tree α)
    (gaps : Nat → Tree α) (start : Nat) :
    MarkedTrace (graft (broadcastCheckpoint left a xs b gap right) gaps start)
      (broadcastWord a xs b)
      (graft (broadcastCheckpoint left a xs b gap right) gaps start)
      (8 * xs.length + 2) :=
  (closed_broadcast_tour left a xs b gap right).graft gaps start

end TangoSquared.MTR
