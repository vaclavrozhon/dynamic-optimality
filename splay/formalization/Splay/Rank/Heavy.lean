import Splay.Rank.Basic
import Splay.Tree.Basic

namespace Splay.Rank

/--
The three outgoing edges in the ternary view of an internal splay-tree node.
The middle edge leads to the value stored at the node; the other two lead to
the ordinary left and right subtrees, including their null leaves.
-/
inductive TernaryBranch
  | left
  | middle
  | right
  deriving DecidableEq, Repr

namespace TernaryBranch

/--
Whether an external inorder position lies in a branch at value key `root`.

The three branch intervals are, respectively, positions at most `2 * root`,
the singleton `2 * root + 1`, and positions at least `2 * root + 2`.
-/
def Contains (branch : TernaryBranch) (root position : ℕ) : Prop :=
  match branch with
  | .left => position ≤ 2 * root
  | .middle => position = 2 * root + 1
  | .right => 2 * root + 2 ≤ position

@[simp]
theorem left_contains_iff {root position : ℕ} :
    TernaryBranch.left.Contains root position ↔ position ≤ 2 * root :=
  Iff.rfl

@[simp]
theorem middle_contains_iff {root position : ℕ} :
    TernaryBranch.middle.Contains root position ↔ position = 2 * root + 1 :=
  Iff.rfl

@[simp]
theorem right_contains_iff {root position : ℕ} :
    TernaryBranch.right.Contains root position ↔ 2 * root + 2 ≤ position :=
  Iff.rfl

/-- Every external position belongs to exactly one branch at a node. -/
theorem existsUnique_contains (root position : ℕ) :
    ∃! branch : TernaryBranch, branch.Contains root position := by
  by_cases hLeft : position ≤ 2 * root
  · refine ⟨.left, hLeft, ?_⟩
    intro branch hBranch
    cases branch with
    | left => rfl
    | middle => simp only [middle_contains_iff] at hBranch; omega
    | right => simp only [right_contains_iff] at hBranch; omega
  · by_cases hMiddle : position = 2 * root + 1
    · refine ⟨.middle, hMiddle, ?_⟩
      intro branch hBranch
      cases branch with
      | left => simp only [left_contains_iff] at hBranch; omega
      | middle => rfl
      | right => simp only [right_contains_iff] at hBranch; omega
    · have hRight : 2 * root + 2 ≤ position := by omega
      refine ⟨.right, hRight, ?_⟩
      intro branch hBranch
      cases branch with
      | left => simp only [left_contains_iff] at hBranch; omega
      | middle => simp only [middle_contains_iff] at hBranch; omega
      | right => rfl

end TernaryBranch

/--
`branch` is heavy on `[lower, upper]` when it contains that interval's
minimum-rank external node.
-/
def Snapshot.IsHeavyBranch {n : ℕ} (snapshot : Snapshot n)
    (lower upper : External n) (root : ℕ) (branch : TernaryBranch) : Prop :=
  ∃ candidate,
    IsIntervalMin snapshot.rank lower upper candidate ∧
      branch.Contains root candidate.val

/-- The canonical minimum-rank node of a nonempty external interval. -/
noncomputable def Snapshot.intervalMin {n : ℕ} (snapshot : Snapshot n)
    (lower upper : External n) (hNonempty : lower ≤ upper) : External n :=
  Classical.choose (snapshot.uniqueIntervalMin lower upper hNonempty)

theorem Snapshot.intervalMin_isMin {n : ℕ} (snapshot : Snapshot n)
    (lower upper : External n) (hNonempty : lower ≤ upper) :
    IsIntervalMin snapshot.rank lower upper
      (snapshot.intervalMin lower upper hNonempty) :=
  (Classical.choose_spec
    (snapshot.uniqueIntervalMin lower upper hNonempty)).1

theorem Snapshot.intervalMin_unique {n : ℕ} (snapshot : Snapshot n)
    (lower upper : External n) (hNonempty : lower ≤ upper)
    {candidate : External n}
    (hCandidate : IsIntervalMin snapshot.rank lower upper candidate) :
    candidate = snapshot.intervalMin lower upper hNonempty :=
  (Classical.choose_spec
    (snapshot.uniqueIntervalMin lower upper hNonempty)).2 candidate hCandidate

/--
The unique interval minimum selects exactly one outgoing branch.

This is the abstract core of `cor:heavy-paths`; the following theorem
specializes it to the complete external interval below an actual BST node.
-/
theorem Snapshot.existsUnique_heavyBranch {n : ℕ}
    (snapshot : Snapshot n) (lower upper : External n)
    (hNonempty : lower ≤ upper) (root : ℕ) :
    ∃! branch, snapshot.IsHeavyBranch lower upper root branch := by
  obtain ⟨candidate, hCandidateMin, hCandidateUnique⟩ :=
    snapshot.uniqueIntervalMin lower upper hNonempty
  obtain ⟨branch, hBranchContains, hBranchUnique⟩ :=
    TernaryBranch.existsUnique_contains root candidate.val
  refine ⟨branch, ⟨candidate, hCandidateMin, hBranchContains⟩, ?_⟩
  rintro other ⟨otherCandidate, hOtherMin, hOtherContains⟩
  have hCandidateEq : otherCandidate = candidate :=
    hCandidateUnique otherCandidate hOtherMin
  subst otherCandidate
  exact hBranchUnique other hOtherContains

/-- The canonical outgoing heavy branch selected by the interval minimum. -/
noncomputable def Snapshot.heavyBranch {n : ℕ}
    (snapshot : Snapshot n) (lower upper : External n)
    (hNonempty : lower ≤ upper) (root : ℕ) : TernaryBranch :=
  Classical.choose
    (snapshot.existsUnique_heavyBranch lower upper hNonempty root)

theorem Snapshot.heavyBranch_isHeavy {n : ℕ}
    (snapshot : Snapshot n) (lower upper : External n)
    (hNonempty : lower ≤ upper) (root : ℕ) :
    snapshot.IsHeavyBranch lower upper root
      (snapshot.heavyBranch lower upper hNonempty root) :=
  (Classical.choose_spec
    (snapshot.existsUnique_heavyBranch lower upper hNonempty root)).1

theorem Snapshot.heavyBranch_unique {n : ℕ}
    (snapshot : Snapshot n) (lower upper : External n)
    (hNonempty : lower ≤ upper) (root : ℕ) {branch : TernaryBranch}
    (hBranch : snapshot.IsHeavyBranch lower upper root branch) :
    branch = snapshot.heavyBranch lower upper hNonempty root :=
  (Classical.choose_spec
    (snapshot.existsUnique_heavyBranch lower upper hNonempty root)).2
      branch hBranch

/--
Every internal node of a splay-tree shape has exactly one outgoing heavy edge.

The interval below the node is the closed external-position interval
`[2 * lower, 2 * upper]`; the indexed left and right subtrees certify that
`root` is a genuine internal key of that interval.
-/
theorem Snapshot.existsUnique_outgoingHeavyBranch
    {n lower root upper : ℕ} (snapshot : Snapshot n)
    (left : Tree.BST lower root) (right : Tree.BST (root + 1) upper)
    (hInside : upper ≤ n) :
    let intervalLower : External n := ⟨2 * lower, by
      have hLowerRoot := left.lower_le_upper
      have hRootUpper := right.lower_le_upper
      omega⟩
    let intervalUpper : External n := ⟨2 * upper, by omega⟩
    ∃! branch,
      snapshot.IsHeavyBranch intervalLower intervalUpper root branch := by
  have hLowerRoot := left.lower_le_upper
  have hRootUpper := right.lower_le_upper
  apply snapshot.existsUnique_heavyBranch
  simp only [Fin.mk_le_mk]
  omega

end Splay.Rank
