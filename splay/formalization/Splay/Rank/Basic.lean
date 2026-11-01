import Mathlib.Data.Fin.Basic
import Lean.Elab.Tactic.Omega

namespace Splay.Rank

/--
External nodes in symmetric order. Even positions are null nodes and odd
positions are value nodes:

`null 0, value 0, null 1, ..., value (n - 1), null n`.
-/
abbrev External (n : ℕ) :=
  Fin (2 * n + 1)

/-- The external position occupied by a value node. -/
def valuePos {n : ℕ} (x : Fin n) : External n :=
  ⟨2 * x.val + 1, by omega⟩

/-- The external position occupied by a null node. -/
def nullPos {n : ℕ} (x : Fin (n + 1)) : External n :=
  ⟨2 * x.val, by omega⟩

/-- The null node immediately to the left of a value. -/
def leftNullPos {n : ℕ} (x : Fin n) : External n :=
  ⟨2 * x.val, by omega⟩

/-- The null node immediately to the right of a value. -/
def rightNullPos {n : ℕ} (x : Fin n) : External n :=
  ⟨2 * x.val + 2, by omega⟩

/--
A candidate is a minimum of `rank` on the closed external-node interval
`[lower, upper]`.
-/
def IsIntervalMin {n : ℕ} (rank : External n → ℕ)
    (lower upper candidate : External n) : Prop :=
  lower ≤ candidate ∧ candidate ≤ upper ∧
    ∀ node, lower ≤ node → node ≤ upper → rank candidate ≤ rank node

/--
Every nonempty closed interval in symmetric order has a unique node of minimum
rank. This is the exact property used to make heavy components into paths.
-/
def HasUniqueIntervalMin {n : ℕ} (rank : External n → ℕ) : Prop :=
  ∀ lower upper : External n, lower ≤ upper →
    ∃! candidate : External n,
      IsIntervalMin rank lower upper candidate

/--
The static rank information consumed by the combinatorial core. A later module
will construct these snapshots from comparison BSTs and connect them by
explicit access-marker and rotation events.
-/
structure Snapshot (n : ℕ) where
  rank : External n → ℕ
  maxRank : ℕ
  rank_le_max : ∀ x, rank x ≤ maxRank
  uniqueIntervalMin : HasUniqueIntervalMin rank
  hasZero : ∃ x, rank x = 0

end Splay.Rank
