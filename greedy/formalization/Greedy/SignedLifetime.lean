import BlockLifetime
import Greedy.FringeCancellation

/-!
# Signed cut sums over an entire shrinking family

A family splits and loses members but never merges. A cut can straddle
at most one current descendant. Any phase with a nonzero signed coefficient
processes that descendant completely, leaving only singleton descendants.
All later coefficients vanish. Each nonzero phase carries its literal
fringe geometry, from which the constant three is proved.
-/

namespace Greedy.SignedLifetime

open Splay.Tree Splay.Tree.BST GreedyMerge.Fringe GreedyForest
open scoped BigOperators

structure PhaseGeometry (coefficient : ℤ) where
  lower : ℕ
  upper : ℕ
  rank : ℕ → ℕ
  owner : ℕ → ℕ
  tree : BST lower upper
  projection : Projection rank owner tree
  localOwners : LocalOwners rank owner lower upper
  cut : ℕ
  first : ℕ
  last : ℕ
  reversed : Bool
  identifies : coefficient = (if reversed then -1 else 1) *
    ∑ edge ∈ (GreedyMerge.Fringe.edges owner tree).toFinset,
      IntervalCancellation.internalWeight cut first last edge.1 edge.2

theorem PhaseGeometry.bound {coefficient : ℤ} (geometry : PhaseGeometry coefficient) :
    |coefficient| ≤ 3 := by
  have bound := FringeCancellation.fringe_internal_sum_abs geometry.rank geometry.owner
    geometry.tree geometry.projection geometry.localOwners geometry.cut geometry.first geometry.last
  rw [geometry.identifies, abs_mul]
  cases geometry.reversed <;> simpa using bound

variable {Record : Type*}

def total : List (Family Record × ℤ) → ℤ
  | [] => 0
  | (_, coefficient) :: rest => coefficient + total rest

def Valid (side : Record → Bool) (before : Family Record) : List (Family Record × ℤ) → Prop
  | [] => True
  | (after, coefficient) :: rest =>
      UniqueStraddler side before ∧ Refines after before ∧
      (coefficient ≠ 0 → Nonempty (PhaseGeometry coefficient)) ∧
      (coefficient ≠ 0 → ∃ source ∈ before,
        Straddles side source ∧ Collapses source before after) ∧
      Valid side after rest

theorem separated_total_zero (side : Record → Bool) (before : Family Record)
    (steps : List (Family Record × ℤ)) (separated : CutSeparated side before)
    (valid : Valid side before steps) : total steps = 0 := by
  induction steps generalizing before with
  | nil => rfl
  | cons step rest ih =>
      obtain ⟨after, coefficient⟩ := step
      obtain ⟨_, refines, _, collapses, tailValid⟩ := valid
      have zero : coefficient = 0 := by
        by_contra nonzero
        obtain ⟨source, member, straddles, _⟩ := collapses nonzero
        exact separated source member straddles
      have tailZero := ih after (cutSeparated_of_refines side before after refines separated) tailValid
      simp [total, zero, tailZero]

theorem total_abs_le_three (side : Record → Bool) (before : Family Record)
    (steps : List (Family Record × ℤ)) (valid : Valid side before steps) : |total steps| ≤ 3 := by
  induction steps generalizing before with
  | nil => simp [total]
  | cons step rest ih =>
      obtain ⟨after, coefficient⟩ := step
      obtain ⟨unique, _, geometry, collapses, tailValid⟩ := valid
      by_cases zero : coefficient = 0
      · simpa [total, zero] using ih after tailValid
      · obtain ⟨source, member, straddles, collapse⟩ := collapses zero
        have separated := cutSeparated_after_collapse side source before after unique member straddles collapse
        have tailZero := separated_total_zero side after rest separated tailValid
        obtain ⟨phase⟩ := geometry zero
        simpa [total, tailZero] using phase.bound

end Greedy.SignedLifetime
