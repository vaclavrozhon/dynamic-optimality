import Splay.Rank.Heavy

namespace Splay.Rank

/--
A dynamic heavy-path junction at `root`: between two rank snapshots, the
canonical heavy branch selected for the same nonempty external interval
changes.

The interval and root are explicit because a rank update can create junctions
at some internal nodes while leaving the outgoing heavy edge unchanged at
others.
-/
noncomputable def Snapshot.IsJunction {n : ℕ}
    (before after : Snapshot n) (lower upper : External n)
    (hNonempty : lower ≤ upper) (root : ℕ) : Prop :=
  before.heavyBranch lower upper hNonempty root ≠
    after.heavyBranch lower upper hNonempty root

/--
The canonical heavy branch contains the canonical minimum-rank external node
of its interval.
-/
theorem Snapshot.heavyBranch_contains_intervalMin {n : ℕ}
    (snapshot : Snapshot n) (lower upper : External n)
    (hNonempty : lower ≤ upper) (root : ℕ) :
    (snapshot.heavyBranch lower upper hNonempty root).Contains root
      (snapshot.intervalMin lower upper hNonempty).val := by
  obtain ⟨candidate, hCandidateMin, hContains⟩ :=
    snapshot.heavyBranch_isHeavy lower upper hNonempty root
  have hCandidateEq :
      candidate = snapshot.intervalMin lower upper hNonempty :=
    snapshot.intervalMin_unique lower upper hNonempty hCandidateMin
  simpa [hCandidateEq] using hContains

/--
If the canonical outgoing heavy branch changes, then the canonical
minimum-rank external node of the interval changes as well.

Only this implication is valid in general: two different interval minima can
still lie in the same ternary branch at `root`.
-/
theorem Snapshot.IsJunction.intervalMin_ne {n : ℕ}
    {before after : Snapshot n} {lower upper : External n}
    {hNonempty : lower ≤ upper} {root : ℕ}
    (hJunction : before.IsJunction after lower upper hNonempty root) :
    before.intervalMin lower upper hNonempty ≠
      after.intervalMin lower upper hNonempty := by
  intro hMinEq
  have hBeforeContains :=
    before.heavyBranch_contains_intervalMin lower upper hNonempty root
  have hAfterContains :=
    after.heavyBranch_contains_intervalMin lower upper hNonempty root
  rw [← hMinEq] at hAfterContains
  obtain ⟨branch, _, hBranchUnique⟩ :=
    TernaryBranch.existsUnique_contains root
      (before.intervalMin lower upper hNonempty).val
  have hBeforeEq :
      before.heavyBranch lower upper hNonempty root = branch :=
    hBranchUnique _ hBeforeContains
  have hAfterEq :
      after.heavyBranch lower upper hNonempty root = branch :=
    hBranchUnique _ hAfterContains
  exact hJunction (hBeforeEq.trans hAfterEq.symm)

end Splay.Rank
