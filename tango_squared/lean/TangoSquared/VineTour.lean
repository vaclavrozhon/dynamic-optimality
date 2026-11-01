import TangoSquared.BSTExecution

/-!
# A closed adjacent-root tour of a vine

The forward scan of an active right vine and its reverse use exactly two
root rotations per noninitial key.  Arbitrary untouched gap subtrees are
preserved.  This formalizes the cheap physical execution in the Cartesian
tertiary counterexample, not the counterexample's owner-indexed flip count.
-/

namespace TangoSquared.MTR

open Tree

variable {α : Type*}

def rightVine : List α → Tree α
  | [] => .empty
  | a :: xs => .node .empty a (rightVine xs)

/-- Scan the remaining keys forward, then return through their predecessors.
The initial root is included only as the final request. -/
def vineTourWord (x : α) : List α → List α
  | [] => []
  | y :: ys => y :: (vineTourWord y ys ++ [x])

theorem vineTourWord_length (x : α) (xs : List α) :
    (vineTourWord x xs).length = 2 * xs.length := by
  induction xs generalizing x with
  | nil => simp [vineTourWord]
  | cons y ys ih => simp [vineTourWord, ih]; omega

theorem vineTourWord_eq (x : α) (xs : List α) :
    vineTourWord x xs = xs ++ (x :: xs).dropLast.reverse := by
  induction xs generalizing x with
  | nil => simp [vineTourWord]
  | cons y ys ih =>
    simp [vineTourWord, ih, List.reverse_cons, List.append_assoc]

/-- Every requested successor or predecessor is promoted by one root rotation.
The recursive middle tour is closed, so the final inverse rotation restores
the exact source tree, including the arbitrary accumulated left subtree. -/
theorem closed_vine_tour (left : Tree α) (x : α) (xs : List α) :
    MarkedTrace (.node left x (rightVine xs)) (vineTourWord x xs)
      (.node left x (rightVine xs)) (2 * xs.length) := by
  induction xs generalizing left x with
  | nil => exact .nil _
  | cons y ys ih =>
    have hm := ih (.node left x .empty) y
    have hb : MarkedTrace
        (.node (.node left x .empty) y (rightVine ys)) [x]
        (.node left x (.node .empty y (rightVine ys))) 1 :=
      .rotate (.rootRight left .empty (rightVine ys) x y)
        (.serve rfl (.nil _))
    have hs := MarkedTrace.rotate
      (RestrictedStep.rootLeft left .empty (rightVine ys) x y)
      (MarkedTrace.serve rfl (hm.trans hb))
    simpa only [rightVine, vineTourWord, List.length_cons,
      Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hs

/-- Restoring the same inorder gaps lifts the entire marked rotation trace. -/
theorem MarkedTrace.graft {s t : Tree α} {xs : List α} {k : Nat}
    (h : MarkedTrace s xs t k) (gaps : Nat → Tree α) (start : Nat) :
    MarkedTrace (graft s gaps start) xs (graft t gaps start) k := by
  induction h with
  | nil => exact .nil _
  | rotate step rest ih => exact .rotate (step.graft gaps start) ih
  | serve at_root rest ih => exact .serve (graft_rootKey _ _ _ at_root) ih

theorem closed_vine_tour_with_gaps (left : Tree α) (x : α) (xs : List α)
    (gaps : Nat → Tree α) (start : Nat) :
    MarkedTrace (graft (.node left x (rightVine xs)) gaps start)
      (vineTourWord x xs)
      (graft (.node left x (rightVine xs)) gaps start) (2 * xs.length) :=
  (closed_vine_tour left x xs).graft gaps start

end TangoSquared.MTR
