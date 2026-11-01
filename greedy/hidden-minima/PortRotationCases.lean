import Splay.Tree.Rotation

/-!
Machine-checked local tree rewrites used in `port-projection-proof.md`.

This file verifies the common-fringe rotation cases, with arbitrary indexed
BSTs in every fringe position. It does NOT yet formalize the interval-minimum
port projection or its reduction to these cases. In particular, this is not
a formal proof of the complete canonical-refinement locality theorem.
-/

namespace GreedyMerge.PortCases

open Splay.Tree
open Splay.Tree.BST

/-- Exactly `n` ordinary rotations, at arbitrary depths. -/
inductive RotationSteps :
    (n : ℕ) → {lo hi : ℕ} → BST lo hi → BST lo hi → Prop
  | refl {lo hi : ℕ} (t : BST lo hi) : RotationSteps 0 t t
  | cons {n depth lo hi : ℕ} {a b c : BST lo hi}
      (first : RotationAt depth a b) (rest : RotationSteps n b c) :
      RotationSteps (n + 1) a c

namespace RotationSteps

theorem one {depth lo hi : ℕ} {a b : BST lo hi}
    (step : RotationAt depth a b) : RotationSteps 1 a b :=
  .cons step (.refl b)

theorem append {m n lo hi : ℕ} {a b c : BST lo hi}
    (first : RotationSteps m a b) (second : RotationSteps n b c) :
    RotationSteps (m + n) a c := by
  induction first with
  | refl _ => simpa using second
  | cons step rest ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using RotationSteps.cons step (ih second)

protected theorem symm {n lo hi : ℕ} {a b : BST lo hi}
    (steps : RotationSteps n a b) : RotationSteps n b a := by
  induction steps with
  | refl t => exact .refl t
  | cons step rest ih => exact ih.append (one step.symm)

theorem leftContext {n lo root hi : ℕ} {a b : BST lo root}
    (steps : RotationSteps n a b) (right : BST (root + 1) hi) :
    RotationSteps n (.node a right) (.node b right) := by
  induction steps with
  | refl _ => exact .refl _
  | cons step rest ih => exact .cons (.leftContext step right) (ih right)

theorem rightContext {n lo root hi : ℕ} (left : BST lo root)
    {a b : BST (root + 1) hi} (steps : RotationSteps n a b) :
    RotationSteps n (.node left a) (.node left b) := by
  induction n generalizing a with
  | zero => cases steps; exact .refl _
  | succ n ih =>
      cases steps with
      | cons step rest => exact .cons (.rightContext left step) (ih rest)

end RotationSteps

/-- Promoting the first port of the right group across one left-group port.
The right group's possible second port is contained in arbitrary fringe `c`. -/
theorem crossOnePort {lo p q hi : ℕ}
    (a : BST lo p) (b : BST (p + 1) q) (c : BST (q + 1) hi) :
    RotationSteps 1 (.node a (.node b c)) (.node (.node a b) c) :=
  RotationSteps.one (.root (.left a b c))

/-- Promoting the first port of the right group across two left-group ports.
All four fringe subtrees are arbitrary and are retained in their inorder slots. -/
theorem crossTwoPorts {lo p q r hi : ℕ}
    (a : BST lo p) (b : BST (p + 1) q)
    (c : BST (q + 1) r) (d : BST (r + 1) hi) :
    RotationSteps 2
      (.node a (.node b (.node c d)))
      (.node (.node a (.node b c)) d) := by
  exact .cons (.rightContext a (.root (.left b c d)))
    (.cons (.root (.left a (.node b c) d)) (.refl _))

/-- The reverse emission swap crosses the same two ports. -/
theorem crossTwoPorts_reverse {lo p q r hi : ℕ}
    (a : BST lo p) (b : BST (p + 1) q)
    (c : BST (q + 1) r) (d : BST (r + 1) hi) :
    RotationSteps 2
      (.node (.node a (.node b c)) d)
      (.node a (.node b (.node c d))) :=
  (crossTwoPorts a b c d).symm

/-- Two adjacent gap atoms sharing their middle separator change the port
chain into a fork. The right port and its descendants are part of `c`. -/
theorem overlappingGaps {lo p q hi : ℕ}
    (a : BST lo p) (b : BST (p + 1) q) (c : BST (q + 1) hi) :
    RotationSteps 1 (.node a (.node b c)) (.node (.node a b) c) :=
  crossOnePort a b c

end GreedyMerge.PortCases
