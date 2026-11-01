import TangoSquared.BSTExecution

/-!
# The two-spine potential for an extreme-prefix rebuild

This is a structural kernel on the existing BST graft operation. It proves
that the unchanged first and last frontiers cancel from the two-spine
potential. Rebuilding a nonempty extreme chain with a target whose left
and right spines have lengths at most two and three has amortized charge
at most four.

The connection from a primary owner in the physical compiler to such a
prefix rebuild remains a hand argument. This file does not certify owner
transport, the total number of owner entries, or competitiveness.
-/

namespace TangoSquared.MTR.Tree.BoundaryPotential

variable {α : Type*}

def leftSpine : Tree α → Nat
  | .empty => 0
  | .node l _ _ => leftSpine l + 1

def rightSpine : Tree α → Nat
  | .empty => 0
  | .node _ _ r => rightSpine r + 1

def potential (t : Tree α) : Nat := leftSpine t + rightSpine t

theorem leftSpine_graft (t : Tree α) (gaps : Nat → Tree α) (start : Nat) :
    leftSpine (graft t gaps start) = leftSpine t + leftSpine (gaps start) := by
  induction t generalizing start with
  | empty => simp [graft, leftSpine]
  | node l x r ihl ihr =>
      simp only [graft, leftSpine, ihl]
      omega

theorem rightSpine_graft (t : Tree α) (gaps : Nat → Tree α) (start : Nat) :
    rightSpine (graft t gaps start) =
      rightSpine t + rightSpine (gaps (start + size t)) := by
  induction t generalizing start with
  | empty => simp [graft, rightSpine, size]
  | node l x r ihl ihr =>
      simp only [graft, rightSpine, ihr, size, Nat.add_assoc]
      omega

theorem potential_graft (t : Tree α) (gaps : Nat → Tree α) (start : Nat) :
    potential (graft t gaps start) = potential t +
      leftSpine (gaps start) + rightSpine (gaps (start + size t)) := by
  rw [potential, leftSpine_graft, rightSpine_graft]
  simp only [potential]
  omega

def rightVine : List α → Tree α
  | [] => .empty
  | x :: xs => .node .empty x (rightVine xs)

def leftVine : List α → Tree α
  | [] => .empty
  | x :: xs => .node (leftVine xs) x .empty

theorem size_rightVine (xs : List α) : size (rightVine xs) = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rightVine, size, ih, Nat.add_comm]

theorem size_leftVine (xs : List α) : size (leftVine xs) = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [leftVine, size, ih]

theorem rightSpine_rightVine (xs : List α) :
    rightSpine (rightVine xs) = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rightVine, rightSpine, ih]

theorem leftSpine_leftVine (xs : List α) :
    leftSpine (leftVine xs) = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [leftVine, leftSpine, ih]

theorem rightVine_potential (x : α) (xs : List α) :
    potential (rightVine (x :: xs)) = size (rightVine (x :: xs)) + 1 := by
  rw [potential, rightSpine_rightVine, size_rightVine]
  simp [rightVine, leftSpine, Nat.add_comm]

theorem leftVine_potential (x : α) (xs : List α) :
    potential (leftVine (x :: xs)) = size (leftVine (x :: xs)) + 1 := by
  rw [potential, leftSpine_leftVine, size_leftVine]
  simp [leftVine, rightSpine]

/-- Exact cancellation of the unchanged extreme frontiers. The source
condition holds for either nonempty extreme chain. -/
theorem prefix_rebuild_identity (source target : Tree α)
    (gaps : Nat → Tree α) (start : Nat)
    (hs : potential source = size source + 1)
    (hsize : size target = size source) :
    size source + potential (graft target gaps start) + 1 =
      potential (graft source gaps start) + potential target := by
  rw [potential_graft, potential_graft, hsize, hs]
  omega

/-- The constant four is conditional on the target's two short extreme
spines; no claim about the compiler's ownership changes is used. -/
theorem prefix_rebuild_charge (source target : Tree α)
    (gaps : Nat → Tree α) (start : Nat)
    (hs : potential source = size source + 1)
    (hsize : size target = size source)
    (hl : leftSpine target ≤ 2) (hr : rightSpine target ≤ 3) :
    size source + potential (graft target gaps start) ≤
      potential (graft source gaps start) + 4 := by
  have hid := prefix_rebuild_identity source target gaps start hs hsize
  have ht : potential target ≤ 5 := by simp only [potential]; omega
  omega

end TangoSquared.MTR.Tree.BoundaryPotential
