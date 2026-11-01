import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-!
# First entry of an adjacent rank walk into an interval

Queries are natural-number ranks. Consecutive ranks differ by at most
one, and repetitions are allowed. The hypotheses concern only the time
segment from the old witness to the current query.

This module proves that the first entry from the left is the left
endpoint, and the first entry from the right is the right endpoint.
Consequently a dormant witness and that first entry choose the same
binary branch at every branching cut of the interval.

The result is a local kernel: it does not construct the rank walk from
a BST execution, establish timestamp dominance for reference edits, or
prove a global changing-reference flip bound. A final wrapper uses a
given dominance hypothesis to obtain the required temporal avoidance.
-/

namespace TangoSquared.AdjacentWalk

/-- The closed interval of active-key ranks. -/
def InInterval (L R x : Nat) : Prop := L ≤ x ∧ x ≤ R

/-- Unit steps in both directions, restricted to the relevant time segment. -/
def UnitStepsOn (a : Nat → Nat) (s t : Nat) : Prop :=
  ∀ j, s ≤ j → j < t → a (j + 1) ≤ a j + 1 ∧ a j ≤ a (j + 1) + 1

/-- The open time interval contains no visit to the current key interval. -/
def AvoidsBetween (a : Nat → Nat) (s t L R : Nat) : Prop :=
  ∀ j, s < j → j < t → ¬ InInterval L R (a j)

/-- Before the first entry, a walk starting left of the interval remains left. -/
theorem stays_left {a : Nat → Nat} {s t L R : Nat}
    (hLR : L ≤ R) (hstep : UnitStepsOn a s t)
    (havoid : AvoidsBetween a s t L R) (hstart : a s < L) :
    ∀ j, s ≤ j → j < t → a j < L := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hsj hjt
      by_cases hjs : j = s
      · simpa [hjs] using hstart
      · have hsj' : s ≤ j - 1 := by omega
        have hj' : j - 1 < j := by omega
        have hprev := ih (j - 1) hj' hsj' (by omega)
        have hnext := (hstep (j - 1) hsj' (by omega)).1
        have hindex : j - 1 + 1 = j := by omega
        rw [hindex] at hnext
        have hout := havoid j (by omega) hjt
        unfold InInterval at hout
        omega

/-- Before the first entry, a walk starting right of the interval remains right. -/
theorem stays_right {a : Nat → Nat} {s t L R : Nat}
    (hLR : L ≤ R) (hstep : UnitStepsOn a s t)
    (havoid : AvoidsBetween a s t L R) (hstart : R < a s) :
    ∀ j, s ≤ j → j < t → R < a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hsj hjt
      by_cases hjs : j = s
      · simpa [hjs] using hstart
      · have hsj' : s ≤ j - 1 := by omega
        have hj' : j - 1 < j := by omega
        have hprev := ih (j - 1) hj' hsj' (by omega)
        have hnext := (hstep (j - 1) hsj' (by omega)).2
        have hindex : j - 1 + 1 = j := by omega
        rw [hindex] at hnext
        have hout := havoid j (by omega) hjt
        unfold InInterval at hout
        omega

/-- A first entry from the left lands exactly at the left endpoint. -/
theorem first_entry_from_left {a : Nat → Nat} {s t L R : Nat}
    (hst : s < t) (hstep : UnitStepsOn a s t)
    (havoid : AvoidsBetween a s t L R) (hstart : a s < L)
    (htarget : InInterval L R (a t)) : a t = L := by
  have hLR : L ≤ R := Nat.le_trans htarget.1 htarget.2
  have hprev := stays_left hLR hstep havoid hstart (t - 1)
    (by omega) (by omega)
  have hnext := (hstep (t - 1) (by omega) (by omega)).1
  have hindex : t - 1 + 1 = t := by omega
  rw [hindex] at hnext
  have htarget' := htarget.1
  omega

/-- A first entry from the right lands exactly at the right endpoint. -/
theorem first_entry_from_right {a : Nat → Nat} {s t L R : Nat}
    (hst : s < t) (hstep : UnitStepsOn a s t)
    (havoid : AvoidsBetween a s t L R) (hstart : R < a s)
    (htarget : InInterval L R (a t)) : a t = R := by
  have hLR : L ≤ R := Nat.le_trans htarget.1 htarget.2
  have hprev := stays_right hLR hstep havoid hstart (t - 1)
    (by omega) (by omega)
  have hnext := (hstep (t - 1) (by omega) (by omega)).2
  have hindex : t - 1 + 1 = t := by omega
  rw [hindex] at hnext
  have htarget' := htarget.2
  omega

/-- A dormant source is on one side, and first entry is at that side's endpoint. -/
theorem first_entry_endpoint {a : Nat → Nat} {s t L R : Nat}
    (hst : s < t) (hstep : UnitStepsOn a s t)
    (havoid : AvoidsBetween a s t L R)
    (hsource : ¬ InInterval L R (a s)) (htarget : InInterval L R (a t)) :
    (a s < L ∧ a t = L) ∨ (R < a s ∧ a t = R) := by
  by_cases hleft : a s < L
  · exact Or.inl ⟨hleft, first_entry_from_left hst hstep havoid hleft htarget⟩
  · have hright : R < a s := by
      unfold InInterval at hsource
      omega
    exact Or.inr ⟨hright, first_entry_from_right hst hstep havoid hright htarget⟩

/-- The binary BST comparison for a gap after rank c; equality goes left. -/
def leftOfCut (x c : Nat) : Bool := decide (x ≤ c)

/-- At a branching cut, a dormant witness and first entry have the same side. -/
theorem dormant_first_entry_same_side {a : Nat → Nat} {s t L R c : Nat}
    (hst : s < t) (hstep : UnitStepsOn a s t)
    (havoid : AvoidsBetween a s t L R)
    (hsource : ¬ InInterval L R (a s)) (htarget : InInterval L R (a t))
    (hLc : L ≤ c) (hcR : c < R) :
    (a s ≤ c ↔ a t ≤ c) := by
  rcases first_entry_endpoint hst hstep havoid hsource htarget with
    ⟨hleft, hentry⟩ | ⟨hright, hentry⟩
  · omega
  · omega

/-- In particular, a witness-facing binary preference cannot flip on first entry. -/
theorem dormant_first_entry_no_flip {a : Nat → Nat} {s t L R c : Nat}
    (hst : s < t) (hstep : UnitStepsOn a s t)
    (havoid : AvoidsBetween a s t L R)
    (hsource : ¬ InInterval L R (a s)) (htarget : InInterval L R (a t))
    (hLc : L ≤ c) (hcR : c < R) :
    leftOfCut (a s) c = leftOfCut (a t) c := by
  have hsame := dormant_first_entry_same_side hst hstep havoid hsource htarget hLc hcR
  by_cases hleft : a s ≤ c
  · have hleft' := hsame.mp hleft
    simp [leftOfCut, hleft, hleft']
  · have hright' : ¬ a t ≤ c := fun h => hleft (hsame.mpr h)
    simp [leftOfCut, hleft, hright']

/-- A supplied dominance bound rules out all intervening visits. -/
theorem avoids_between_of_dominance {a : Nat → Nat} {s t L R : Nat}
    (hdom : ∀ j, j < t → InInterval L R (a j) → j ≤ s) :
    AvoidsBetween a s t L R := by
  intro j hsj hjt hmem
  have hj := hdom j hjt hmem
  omega

/-- The local no-flip kernel with timestamp dominance supplied explicitly. -/
theorem dormant_no_flip_of_dominance {a : Nat → Nat} {s t L R c : Nat}
    (hst : s < t) (hstep : UnitStepsOn a s t)
    (hdom : ∀ j, j < t → InInterval L R (a j) → j ≤ s)
    (hsource : ¬ InInterval L R (a s)) (htarget : InInterval L R (a t))
    (hLc : L ≤ c) (hcR : c < R) :
    leftOfCut (a s) c = leftOfCut (a t) c :=
  dormant_first_entry_no_flip hst hstep (avoids_between_of_dominance hdom)
    hsource htarget hLc hcR

end TangoSquared.AdjacentWalk
