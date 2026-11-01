import Mathlib.Data.Fintype.Card
import Splay.Lazy.Model
import Splay.Rank.Heavy

namespace Splay.Lazy.Canonical

open Splay.Rank

/--
The data of one internal node of an interval-indexed splay tree.

Keeping the two children in the structure records the exact three-way
partition used by the ternary view.  `upper_le_n` embeds all of its external
positions into the ambient tree with `n` value keys.
-/
structure AtNode (n : ℕ) where
  lower : ℕ
  root : ℕ
  upper : ℕ
  left : Tree.BST lower root
  right : Tree.BST (root + 1) upper
  upper_le_n : upper ≤ n

namespace AtNode

theorem lower_le_root {n : ℕ} (node : AtNode n) :
    node.lower ≤ node.root :=
  node.left.lower_le_upper

theorem root_lt_upper {n : ℕ} (node : AtNode n) :
    node.root < node.upper := by
  have := node.right.lower_le_upper
  omega

/-- First external position in the complete subtree of this node. -/
def wholeLower {n : ℕ} (node : AtNode n) : External n :=
  ⟨2 * node.lower, by
    have := node.lower_le_root
    have := node.root_lt_upper
    have := node.upper_le_n
    omega⟩

/-- Last external position in the complete subtree of this node. -/
def wholeUpper {n : ℕ} (node : AtNode n) : External n :=
  ⟨2 * node.upper, by
    have := node.upper_le_n
    omega⟩

theorem whole_nonempty {n : ℕ} (node : AtNode n) :
    node.wholeLower ≤ node.wholeUpper := by
  simp only [wholeLower, wholeUpper, Fin.mk_le_mk]
  have := node.lower_le_root
  have := node.root_lt_upper
  omega

/-- First external position in one of the three ternary branches. -/
def branchLower {n : ℕ} (node : AtNode n) :
    TernaryBranch → External n
  | .left => node.wholeLower
  | .middle => ⟨2 * node.root + 1, by
      have := node.root_lt_upper
      have := node.upper_le_n
      omega⟩
  | .right => ⟨2 * node.root + 2, by
      have := node.root_lt_upper
      have := node.upper_le_n
      omega⟩

/-- Last external position in one of the three ternary branches. -/
def branchUpper {n : ℕ} (node : AtNode n) :
    TernaryBranch → External n
  | .left => ⟨2 * node.root, by
      have := node.root_lt_upper
      have := node.upper_le_n
      omega⟩
  | .middle => ⟨2 * node.root + 1, by
      have := node.root_lt_upper
      have := node.upper_le_n
      omega⟩
  | .right => node.wholeUpper

theorem branch_nonempty {n : ℕ} (node : AtNode n)
    (branch : TernaryBranch) :
    node.branchLower branch ≤ node.branchUpper branch := by
  cases branch <;>
    simp only [branchLower, branchUpper, wholeLower, wholeUpper, Fin.mk_le_mk]
  · exact Nat.mul_le_mul_left 2 node.lower_le_root
  · exact le_rfl
  · have := node.root_lt_upper
    omega

/-- Canonical external node owning the heavy path through this internal node. -/
noncomputable def owner {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) : External n :=
  snapshot.intervalMin node.wholeLower node.wholeUpper node.whole_nonempty

/-- Canonical minimum in a particular outgoing ternary branch. -/
noncomputable def branchMin {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) (branch : TernaryBranch) : External n :=
  snapshot.intervalMin
    (node.branchLower branch) (node.branchUpper branch)
    (node.branch_nonempty branch)

/-- The outgoing branch containing the owner is the unique heavy branch. -/
noncomputable def heavyBranch {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) : TernaryBranch :=
  snapshot.heavyBranch
    node.wholeLower node.wholeUpper node.whole_nonempty node.root

theorem owner_isMin {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) :
    IsIntervalMin snapshot.rank node.wholeLower node.wholeUpper
      (node.owner snapshot) :=
  snapshot.intervalMin_isMin _ _ _

theorem branchMin_isMin {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) (branch : TernaryBranch) :
    IsIntervalMin snapshot.rank
      (node.branchLower branch) (node.branchUpper branch)
      (node.branchMin snapshot branch) :=
  snapshot.intervalMin_isMin _ _ _

theorem branchMin_in_branch {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) (branch : TernaryBranch) :
    branch.Contains node.root (node.branchMin snapshot branch).val := by
  have hMin := node.branchMin_isMin snapshot branch
  cases branch with
  | left =>
      exact hMin.2.1
  | middle =>
      have hLower := hMin.1
      have hUpper := hMin.2.1
      change (node.branchMin snapshot .middle).val =
        2 * node.root + 1
      change 2 * node.root + 1 ≤
        (node.branchMin snapshot .middle).val at hLower
      change (node.branchMin snapshot .middle).val ≤
        2 * node.root + 1 at hUpper
      omega
  | right =>
      exact hMin.1

theorem owner_in_heavyBranch {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) :
    (node.heavyBranch snapshot).Contains node.root
      (node.owner snapshot).val := by
  obtain ⟨candidate, hCandidateMin, hContains⟩ :=
    snapshot.heavyBranch_isHeavy
      node.wholeLower node.wholeUpper node.whole_nonempty node.root
  have hCandidateEq : candidate = node.owner snapshot :=
    snapshot.intervalMin_unique
      node.wholeLower node.wholeUpper node.whole_nonempty hCandidateMin
  change
    (snapshot.heavyBranch
      node.wholeLower node.wholeUpper node.whole_nonempty node.root).Contains
      node.root (node.owner snapshot).val
  simpa [hCandidateEq] using hContains

/-- The whole-node owner is the minimum of its selected heavy branch. -/
theorem owner_eq_branchMin_heavy {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) :
    node.owner snapshot =
      node.branchMin snapshot (node.heavyBranch snapshot) := by
  generalize heavyEq : node.heavyBranch snapshot = heavy
  apply snapshot.intervalMin_unique
  have contains := node.owner_in_heavyBranch snapshot
  rw [heavyEq] at contains
  have inside :
      node.branchLower heavy ≤ node.owner snapshot ∧
        node.owner snapshot ≤ node.branchUpper heavy := by
    cases heavy with
    | left =>
        exact ⟨(node.owner_isMin snapshot).1, contains⟩
    | middle =>
        change
          2 * node.root + 1 ≤ (node.owner snapshot).val ∧
            (node.owner snapshot).val ≤ 2 * node.root + 1
        simp only [TernaryBranch.middle_contains_iff] at contains
        omega
    | right =>
        exact ⟨contains, (node.owner_isMin snapshot).2.1⟩
  refine ⟨inside.1, inside.2, ?_⟩
  intro candidate candidateLower candidateUpper
  have wholeLowerCandidate : node.wholeLower ≤ candidate := by
    cases heavy with
    | left => exact candidateLower
    | middle =>
        change 2 * node.lower ≤ candidate.val
        change 2 * node.root + 1 ≤ candidate.val at candidateLower
        have := node.lower_le_root
        omega
    | right =>
        change 2 * node.lower ≤ candidate.val
        change 2 * node.root + 2 ≤ candidate.val at candidateLower
        have := node.lower_le_root
        omega
  have candidateWholeUpper : candidate ≤ node.wholeUpper := by
    cases heavy with
    | left =>
        change candidate.val ≤ 2 * node.upper
        change candidate.val ≤ 2 * node.root at candidateUpper
        have := node.root_lt_upper
        omega
    | middle =>
        change candidate.val ≤ 2 * node.upper
        change candidate.val ≤ 2 * node.root + 1 at candidateUpper
        have := node.root_lt_upper
        omega
    | right => exact candidateUpper
  exact
    (node.owner_isMin snapshot).2.2 candidate
      wholeLowerCandidate candidateWholeUpper

/-- A zero-rank position determines the heavy branch containing it. -/
theorem heavyBranch_eq_of_rank_eq_zero {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n)
    (branch : TernaryBranch) (candidate : External n)
    (rankZero : snapshot.rank candidate = 0)
    (insideWhole : node.wholeLower ≤ candidate ∧
      candidate ≤ node.wholeUpper)
    (contained : branch.Contains node.root candidate.val) :
    node.heavyBranch snapshot = branch := by
  symm
  apply snapshot.heavyBranch_unique
  refine ⟨candidate, ?_, contained⟩
  refine ⟨insideWhole.1, insideWhole.2, ?_⟩
  intro other _ _
  rw [rankZero]
  exact Nat.zero_le _

/-- Every branch minimum is still inside the complete node interval. -/
theorem branchMin_in_whole {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) (branch : TernaryBranch) :
    node.wholeLower ≤ node.branchMin snapshot branch ∧
      node.branchMin snapshot branch ≤ node.wholeUpper := by
  have hMin := node.branchMin_isMin snapshot branch
  cases branch with
  | left =>
      refine ⟨hMin.1, ?_⟩
      have hEndpoint :
          node.branchUpper .left ≤ node.wholeUpper := by
        change 2 * node.root ≤ 2 * node.upper
        have := node.root_lt_upper
        omega
      calc
        node.branchMin snapshot .left ≤ node.branchUpper .left := hMin.2.1
        _ ≤ node.wholeUpper := hEndpoint
  | middle =>
      constructor
      · have hEndpoint :
            node.wholeLower ≤ node.branchLower .middle := by
          change 2 * node.lower ≤ 2 * node.root + 1
          have := node.lower_le_root
          omega
        calc
          node.wholeLower ≤ node.branchLower .middle := hEndpoint
          _ ≤ node.branchMin snapshot .middle := hMin.1
      · have hEndpoint :
            node.branchUpper .middle ≤ node.wholeUpper := by
          change 2 * node.root + 1 ≤ 2 * node.upper
          have := node.root_lt_upper
          omega
        calc
          node.branchMin snapshot .middle ≤ node.branchUpper .middle := hMin.2.1
          _ ≤ node.wholeUpper := hEndpoint
  | right =>
      refine ⟨?_, hMin.2.1⟩
      have hEndpoint :
          node.wholeLower ≤ node.branchLower .right := by
        change 2 * node.lower ≤ 2 * node.root + 2
        have := node.lower_le_root
        omega
      calc
        node.wholeLower ≤ node.branchLower .right := hEndpoint
        _ ≤ node.branchMin snapshot .right := hMin.1

/--
The minimum of a light branch is not the owner of the heavy path through the
node.  This follows solely from uniqueness of the branch containing an
external inorder position.
-/
theorem branchMin_ne_owner_of_light {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) {branch : TernaryBranch}
    (hLight : branch ≠ node.heavyBranch snapshot) :
    node.branchMin snapshot branch ≠ node.owner snapshot := by
  intro hEqual
  obtain ⟨selected, _, hUnique⟩ :=
    TernaryBranch.existsUnique_contains node.root (node.owner snapshot).val
  have hBranch :
      branch = selected :=
    hUnique branch (by
      rw [← hEqual]
      exact node.branchMin_in_branch snapshot branch)
  have hHeavy :
      node.heavyBranch snapshot = selected :=
    hUnique (node.heavyBranch snapshot)
      (node.owner_in_heavyBranch snapshot)
  exact hLight (hBranch.trans hHeavy.symm)

/-- A light child has strictly larger rank than its canonical owner. -/
theorem owner_rank_lt_branchMin_of_light {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n)
    {branch : TernaryBranch}
    (hLight : branch ≠ node.heavyBranch snapshot) :
    snapshot.rank (node.owner snapshot) <
      snapshot.rank (node.branchMin snapshot branch) := by
  have hWhole := node.branchMin_in_whole snapshot branch
  have hLe :
      snapshot.rank (node.owner snapshot) ≤
        snapshot.rank (node.branchMin snapshot branch) :=
    (node.owner_isMin snapshot).2.2 _ hWhole.1 hWhole.2
  apply lt_of_le_of_ne hLe
  intro hRank
  have hChildMin :
      IsIntervalMin snapshot.rank node.wholeLower node.wholeUpper
        (node.branchMin snapshot branch) := by
    refine ⟨hWhole.1, hWhole.2, ?_⟩
    intro candidate hLower hUpper
    have hOwnerLe :=
      (node.owner_isMin snapshot).2.2 candidate hLower hUpper
    omega
  have hEqual :=
    snapshot.intervalMin_unique
      node.wholeLower node.wholeUpper node.whole_nonempty hChildMin
  exact node.branchMin_ne_owner_of_light snapshot hLight hEqual

end AtNode

/-- The three branches, in symmetric order. -/
def allBranches : List TernaryBranch :=
  [.left, .middle, .right]

@[simp]
theorem mem_allBranches (branch : TernaryBranch) :
    branch ∈ allBranches := by
  cases branch <;> simp [allBranches]

@[simp]
theorem allBranches_nodup : allBranches.Nodup := by
  simp [allBranches]

/-- Exactly the branches other than the canonical heavy one. -/
noncomputable def lightBranches {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) : List TernaryBranch :=
  allBranches.filter fun branch => branch != node.heavyBranch snapshot

@[simp]
theorem mem_lightBranches_iff {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) (branch : TernaryBranch) :
    branch ∈ lightBranches snapshot node ↔
      branch ≠ node.heavyBranch snapshot := by
  simp [lightBranches]

/-- Of the three outgoing branches, exactly two are light. -/
@[simp]
theorem length_lightBranches {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) :
    (lightBranches snapshot node).length = 2 := by
  unfold lightBranches allBranches
  generalize hHeavy : node.heavyBranch snapshot = heavy
  cases heavy <;> simp

/-- Side of the owner selected by symmetric external-node order. -/
def sideOf {n : ℕ} (owner child : External n) : Side :=
  if child.val < owner.val then .left else .right

/-- Distinct external nodes lie on the side selected by their inorder
positions. -/
theorem sideOf_order_of_ne {n : ℕ} {owner child : External n}
    (different : owner ≠ child) :
    match sideOf owner child with
    | .left => child.val < owner.val
    | .right => owner.val < child.val := by
  have valuesDifferent : child.val ≠ owner.val := by
    intro equal
    exact different (Fin.ext equal.symm)
  by_cases left : child.val < owner.val
  · simp [sideOf, left]
  · have right : owner.val < child.val := by omega
    simp [sideOf, left, right]

/-- One canonical light edge contributed by an internal splay-tree node. -/
structure Edge (n : ℕ) where
  branch : TernaryBranch
  owner : External n
  child : External n
  side : Side
  /-- Persistent identity of the internal node carrying this light edge. -/
  attachmentKey : ℕ
  attachmentDepth : ℕ
  deriving Repr

/-- The edge record associated with one outgoing branch. -/
noncomputable def edgeFor {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) (attachmentDepth : ℕ)
    (branch : TernaryBranch) : Edge n where
  branch := branch
  owner := node.owner snapshot
  child := node.branchMin snapshot branch
  side := sideOf (node.owner snapshot) (node.branchMin snapshot branch)
  attachmentKey := node.root
  attachmentDepth := attachmentDepth

/-- Exact validity predicate for a local canonical light-edge record. -/
def Edge.Valid {n : ℕ} (snapshot : Snapshot n) (node : AtNode n)
    (depth : ℕ) (edge : Edge n) : Prop :=
  edge.branch ≠ node.heavyBranch snapshot ∧
    edge.owner = node.owner snapshot ∧
    edge.child = node.branchMin snapshot edge.branch ∧
    edge.side = sideOf edge.owner edge.child ∧
    edge.attachmentKey = node.root ∧
    edge.attachmentDepth = depth ∧
    snapshot.rank edge.owner < snapshot.rank edge.child

theorem Edge.Valid.child_ne_owner {n : ℕ} {snapshot : Snapshot n}
    {node : AtNode n} {depth : ℕ} {edge : Edge n}
    (valid : edge.Valid snapshot node depth) :
    edge.child ≠ edge.owner := by
  rcases valid with ⟨_, _, _, _, _, _, hRank⟩
  intro hEqual
  rw [hEqual] at hRank
  exact Nat.lt_irrefl _ hRank

/-- A valid local edge retains the persistent key of its attachment node. -/
theorem Edge.Valid.attachmentKey_eq {n : ℕ} {snapshot : Snapshot n}
    {node : AtNode n} {depth : ℕ} {edge : Edge n}
    (valid : edge.Valid snapshot node depth) :
    edge.attachmentKey = node.root :=
  valid.2.2.2.2.1

/-- `side` is precisely the side selected by external inorder position. -/
theorem Edge.Valid.side_order {n : ℕ} {snapshot : Snapshot n}
    {node : AtNode n} {depth : ℕ} {edge : Edge n}
    (valid : edge.Valid snapshot node depth) :
    match edge.side with
    | .left => edge.child.val < edge.owner.val
    | .right => edge.owner.val < edge.child.val := by
  have hSide := valid.2.2.2.1
  have hNe := valid.child_ne_owner
  have hValNe : edge.child.val ≠ edge.owner.val := by
    intro hVal
    apply hNe
    exact Fin.ext hVal
  by_cases hLeft : edge.child.val < edge.owner.val
  · have hSideLeft : edge.side = .left := by
      rw [hSide]
      simp [sideOf, hLeft]
    rw [hSideLeft]
    exact hLeft
  · have hRight : edge.owner.val < edge.child.val := by omega
    have hSideRight : edge.side = .right := by
      rw [hSide]
      simp [sideOf, hLeft]
    rw [hSideRight]
    exact hRight

/-- If the owner lies in the left ternary branch, that branch is heavy. -/
theorem AtNode.heavyBranch_eq_left_of_owner_le_root {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n)
    (ownerLeft : (node.owner snapshot).val ≤ 2 * node.root) :
    node.heavyBranch snapshot = .left := by
  generalize heavyEq : node.heavyBranch snapshot = heavy
  have contained := node.owner_in_heavyBranch snapshot
  rw [heavyEq] at contained
  cases heavy with
  | left => rfl
  | middle =>
      simp only [TernaryBranch.middle_contains_iff] at contained
      omega
  | right =>
      simp only [TernaryBranch.right_contains_iff] at contained
      omega

/-- If the owner lies in the right ternary branch, that branch is heavy. -/
theorem AtNode.heavyBranch_eq_right_of_root_lt_owner {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n)
    (ownerRight : 2 * node.root + 2 ≤ (node.owner snapshot).val) :
    node.heavyBranch snapshot = .right := by
  generalize heavyEq : node.heavyBranch snapshot = heavy
  have contained := node.owner_in_heavyBranch snapshot
  rw [heavyEq] at contained
  cases heavy with
  | left =>
      simp only [TernaryBranch.left_contains_iff] at contained
      omega
  | middle =>
      simp only [TernaryBranch.middle_contains_iff] at contained
      omega
  | right => rfl

/-- A light local child lies strictly outside a left heavy branch. -/
theorem Edge.Valid.child_gt_root_of_heavy_left {n : ℕ}
    {snapshot : Snapshot n} {node : AtNode n} {depth : ℕ}
    {edge : Edge n} (valid : edge.Valid snapshot node depth)
    (heavyLeft : node.heavyBranch snapshot = .left) :
    2 * node.root < edge.child.val := by
  have contained : edge.branch.Contains node.root edge.child.val := by
    rw [valid.2.2.1]
    exact node.branchMin_in_branch snapshot edge.branch
  cases branchEq : edge.branch with
  | left =>
      exact False.elim (valid.1 (branchEq.trans heavyLeft.symm))
  | middle =>
      rw [branchEq] at contained
      simp only [TernaryBranch.middle_contains_iff] at contained
      omega
  | right =>
      rw [branchEq] at contained
      simp only [TernaryBranch.right_contains_iff] at contained
      omega

/-- A light local child lies strictly outside a right heavy branch. -/
theorem Edge.Valid.child_lt_root_of_heavy_right {n : ℕ}
    {snapshot : Snapshot n} {node : AtNode n} {depth : ℕ}
    {edge : Edge n} (valid : edge.Valid snapshot node depth)
    (heavyRight : node.heavyBranch snapshot = .right) :
    edge.child.val < 2 * node.root + 2 := by
  have contained : edge.branch.Contains node.root edge.child.val := by
    rw [valid.2.2.1]
    exact node.branchMin_in_branch snapshot edge.branch
  cases branchEq : edge.branch with
  | left =>
      rw [branchEq] at contained
      simp only [TernaryBranch.left_contains_iff] at contained
      omega
  | middle =>
      rw [branchEq] at contained
      simp only [TernaryBranch.middle_contains_iff] at contained
      omega
  | right =>
      exact False.elim (valid.1 (branchEq.trans heavyRight.symm))

/-- Distinct local light branches are separated in symmetric order. -/
theorem Edge.Valid.other_child_gt_root_of_child_le {n : ℕ}
    {snapshot : Snapshot n} {node : AtNode n} {depth : ℕ}
    {first second : Edge n}
    (firstValid : first.Valid snapshot node depth)
    (secondValid : second.Valid snapshot node depth)
    (different : first.child ≠ second.child)
    (firstLeft : first.child.val ≤ 2 * node.root) :
    2 * node.root < second.child.val := by
  have firstContained :
      first.branch.Contains node.root first.child.val := by
    rw [firstValid.2.2.1]
    exact node.branchMin_in_branch snapshot first.branch
  have secondContained :
      second.branch.Contains node.root second.child.val := by
    rw [secondValid.2.2.1]
    exact node.branchMin_in_branch snapshot second.branch
  have branchesDifferent : first.branch ≠ second.branch := by
    intro branchesEqual
    apply different
    rw [firstValid.2.2.1, secondValid.2.2.1, branchesEqual]
  have firstBranchLeft : first.branch = .left := by
    cases firstBranch : first.branch with
    | left => rfl
    | middle =>
        rw [firstBranch] at firstContained
        simp only [TernaryBranch.middle_contains_iff] at firstContained
        omega
    | right =>
        rw [firstBranch] at firstContained
        simp only [TernaryBranch.right_contains_iff] at firstContained
        omega
  have secondNotLeft : second.branch ≠ .left := by
    intro secondLeft
    exact branchesDifferent (firstBranchLeft.trans secondLeft.symm)
  cases secondBranch : second.branch with
  | left => exact False.elim (secondNotLeft secondBranch)
  | middle =>
      rw [secondBranch] at secondContained
      simp only [TernaryBranch.middle_contains_iff] at secondContained
      omega
  | right =>
      rw [secondBranch] at secondContained
      simp only [TernaryBranch.right_contains_iff] at secondContained
      omega

/-- Symmetric counterpart of `other_child_gt_root_of_child_le`. -/
theorem Edge.Valid.other_child_lt_root_of_root_le_child {n : ℕ}
    {snapshot : Snapshot n} {node : AtNode n} {depth : ℕ}
    {first second : Edge n}
    (firstValid : first.Valid snapshot node depth)
    (secondValid : second.Valid snapshot node depth)
    (different : first.child ≠ second.child)
    (firstRight : 2 * node.root + 2 ≤ first.child.val) :
    second.child.val < 2 * node.root + 2 := by
  have firstContained :
      first.branch.Contains node.root first.child.val := by
    rw [firstValid.2.2.1]
    exact node.branchMin_in_branch snapshot first.branch
  have secondContained :
      second.branch.Contains node.root second.child.val := by
    rw [secondValid.2.2.1]
    exact node.branchMin_in_branch snapshot second.branch
  have branchesDifferent : first.branch ≠ second.branch := by
    intro branchesEqual
    apply different
    rw [firstValid.2.2.1, secondValid.2.2.1, branchesEqual]
  have firstBranchRight : first.branch = .right := by
    cases firstBranch : first.branch with
    | left =>
        rw [firstBranch] at firstContained
        simp only [TernaryBranch.left_contains_iff] at firstContained
        omega
    | middle =>
        rw [firstBranch] at firstContained
        simp only [TernaryBranch.middle_contains_iff] at firstContained
        omega
    | right => rfl
  have secondNotRight : second.branch ≠ .right := by
    intro secondRight
    exact branchesDifferent (firstBranchRight.trans secondRight.symm)
  cases secondBranch : second.branch with
  | left =>
      rw [secondBranch] at secondContained
      simp only [TernaryBranch.left_contains_iff] at secondContained
      omega
  | middle =>
      rw [secondBranch] at secondContained
      simp only [TernaryBranch.middle_contains_iff] at secondContained
      omega
  | right => exact False.elim (secondNotRight secondBranch)

/-- The two canonical light edges contributed at one internal node. -/
noncomputable def edgesAtNode {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) (attachmentDepth : ℕ) : List (Edge n) :=
  (lightBranches snapshot node).map
    (edgeFor snapshot node attachmentDepth)

@[simp]
theorem length_edgesAtNode {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) (attachmentDepth : ℕ) :
    (edgesAtNode snapshot node attachmentDepth).length = 2 := by
  simp [edgesAtNode]

theorem edgeFor_valid_of_light {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) (depth : ℕ) {branch : TernaryBranch}
    (hLight : branch ≠ node.heavyBranch snapshot) :
    (edgeFor snapshot node depth branch).Valid snapshot node depth := by
  refine ⟨hLight, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact node.owner_rank_lt_branchMin_of_light snapshot hLight

theorem mem_edgesAtNode_valid {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) (depth : ℕ) {edge : Edge n}
    (hMember : edge ∈ edgesAtNode snapshot node depth) :
    edge.Valid snapshot node depth := by
  simp only [edgesAtNode, List.mem_map] at hMember
  obtain ⟨branch, hBranch, rfl⟩ := hMember
  apply edgeFor_valid_of_light
  exact (mem_lightBranches_iff snapshot node branch).mp hBranch

theorem mem_edgesAtNode_child_ne_owner {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n) (depth : ℕ)
    {edge : Edge n} (hMember : edge ∈ edgesAtNode snapshot node depth) :
    edge.child ≠ edge.owner := by
  exact (mem_edgesAtNode_valid snapshot node depth hMember).child_ne_owner

/-- Every edge emitted at a node records that node's persistent key. -/
theorem mem_edgesAtNode_attachmentKey {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n) (depth : ℕ)
    {edge : Edge n} (member : edge ∈ edgesAtNode snapshot node depth) :
    edge.attachmentKey = node.root :=
  (mem_edgesAtNode_valid snapshot node depth member).attachmentKey_eq

/-- First external position belonging to an indexed comparison subtree. -/
def subtreeLower {n lower upper : ℕ} (tree : Tree.BST lower upper)
    (upper_le_n : upper ≤ n) : External n :=
  ⟨2 * lower, by
    have hBounds := tree.lower_le_upper
    omega⟩

/-- Last external position belonging to an indexed comparison subtree. -/
def subtreeUpper {n lower upper : ℕ} (_tree : Tree.BST lower upper)
    (upper_le_n : upper ≤ n) : External n :=
  ⟨2 * upper, by omega⟩

theorem subtree_nonempty {n lower upper : ℕ}
    (tree : Tree.BST lower upper) (upper_le_n : upper ≤ n) :
    subtreeLower tree upper_le_n ≤ subtreeUpper tree upper_le_n := by
  simp only [subtreeLower, subtreeUpper, Fin.mk_le_mk]
  exact Nat.mul_le_mul_left 2 tree.lower_le_upper

/-- Canonical heavy-path root of an entire indexed comparison subtree. -/
noncomputable def subtreeOwner {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST lower upper)
    (upper_le_n : upper ≤ n) : External n :=
  snapshot.intervalMin
    (subtreeLower tree upper_le_n) (subtreeUpper tree upper_le_n)
    (subtree_nonempty tree upper_le_n)

theorem subtreeOwner_isMin {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST lower upper)
    (upper_le_n : upper ≤ n) :
    IsIntervalMin snapshot.rank
      (subtreeLower tree upper_le_n) (subtreeUpper tree upper_le_n)
      (subtreeOwner snapshot tree upper_le_n) :=
  snapshot.intervalMin_isMin _ _ _

@[simp]
theorem node_owner_eq_subtreeOwner {n lower root upper : ℕ}
    (snapshot : Snapshot n) (left : Tree.BST lower root)
    (right : Tree.BST (root + 1) upper) (upper_le_n : upper ≤ n) :
    let node : AtNode n := {
      lower := lower
      root := root
      upper := upper
      left := left
      right := right
      upper_le_n := upper_le_n
    }
    node.owner snapshot =
      subtreeOwner snapshot (.node left right) upper_le_n := by
  rfl

@[simp]
theorem node_left_branchMin_eq_subtreeOwner {n lower root upper : ℕ}
    (snapshot : Snapshot n) (left : Tree.BST lower root)
    (right : Tree.BST (root + 1) upper) (upper_le_n : upper ≤ n) :
    let node : AtNode n := {
      lower := lower
      root := root
      upper := upper
      left := left
      right := right
      upper_le_n := upper_le_n
    }
    node.branchMin snapshot .left =
      subtreeOwner snapshot left (by
        have hRootUpper := right.lower_le_upper
        omega) := by
  rfl

@[simp]
theorem node_right_branchMin_eq_subtreeOwner {n lower root upper : ℕ}
    (snapshot : Snapshot n) (left : Tree.BST lower root)
    (right : Tree.BST (root + 1) upper) (upper_le_n : upper ≤ n) :
    let node : AtNode n := {
      lower := lower
      root := root
      upper := upper
      left := left
      right := right
      upper_le_n := upper_le_n
    }
    node.branchMin snapshot .right =
      subtreeOwner snapshot right upper_le_n := by
  rfl

/--
Canonical light-edge records for every internal node of a subtree.

The explicit `depth` parameter is the structural depth of the subtree root in
the ambient splay tree.  Recursive calls increment it, so every record carries
the depth of the internal node at which its light edge is attached.
-/
noncomputable def treeEdges {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST lower upper)
    (upper_le_n : upper ≤ n) (depth : ℕ := 0) : List (Edge n) :=
  match tree with
  | .empty _ => []
  | .node (root := root) left right =>
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      edgesAtNode snapshot node depth ++
        treeEdges snapshot left (by
          have hRootUpper := right.lower_le_upper
          omega) (depth + 1) ++
        treeEdges snapshot right upper_le_n (depth + 1)

/-- The canonical list has exactly two light edges per internal node. -/
@[simp]
theorem length_treeEdges {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST lower upper)
    (upper_le_n : upper ≤ n) (depth : ℕ := 0) :
    (treeEdges snapshot tree upper_le_n depth).length = 2 * tree.size := by
  induction tree generalizing depth with
  | empty =>
      simp [treeEdges, Tree.BST.size]
  | @node lower root upper left right ihLeft ihRight =>
      simp only [treeEdges, List.length_append, length_edgesAtNode,
        ihLeft, ihRight, Tree.BST.size]
      omega

/-- Child vertices of all canonical light edges, in construction order. -/
noncomputable def treeChildren {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST lower upper)
    (upper_le_n : upper ≤ n) (depth : ℕ := 0) : List (External n) :=
  (treeEdges snapshot tree upper_le_n depth).map Edge.child

@[simp]
theorem length_treeChildren {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST lower upper)
    (upper_le_n : upper ≤ n) (depth : ℕ := 0) :
    (treeChildren snapshot tree upper_le_n depth).length =
      2 * tree.size := by
  simp [treeChildren]

theorem branchMin_injective {n : ℕ} (snapshot : Snapshot n)
    (node : AtNode n) :
    Function.Injective (node.branchMin snapshot) := by
  intro first second hEqual
  obtain ⟨selected, _, hUnique⟩ :=
    TernaryBranch.existsUnique_contains node.root
      (node.branchMin snapshot first).val
  have hFirst : first = selected :=
    hUnique first (node.branchMin_in_branch snapshot first)
  have hSecond : second = selected := by
    apply hUnique second
    simpa only [hEqual] using
      (node.branchMin_in_branch snapshot second)
  exact hFirst.trans hSecond.symm

@[simp]
theorem edgesAtNode_children_nodup {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n) (depth : ℕ) :
    ((edgesAtNode snapshot node depth).map Edge.child).Nodup := by
  simp only [edgesAtNode, List.map_map]
  apply List.Nodup.map
  · exact branchMin_injective snapshot node
  · exact allBranches_nodup.filter _

theorem mem_treeEdges_rank_lt {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST lower upper)
    (upper_le_n : upper ≤ n) {depth : ℕ} {edge : Edge n}
    (hMember : edge ∈ treeEdges snapshot tree upper_le_n depth) :
    snapshot.rank edge.owner < snapshot.rank edge.child := by
  induction tree generalizing depth with
  | empty =>
      simp [treeEdges] at hMember
  | @node lower root upper left right ihLeft ihRight =>
      rw [treeEdges] at hMember
      rcases List.mem_append.mp hMember with hPrefix | hRight
      · rcases List.mem_append.mp hPrefix with hLocal | hLeft
        · exact (mem_edgesAtNode_valid snapshot
            {
              lower := lower
              root := root
              upper := upper
              left := left
              right := right
              upper_le_n := upper_le_n
            } depth hLocal).2.2.2.2.2.2
        · exact ihLeft (by
            have hRootUpper := right.lower_le_upper
            omega) hLeft
      · exact ihRight upper_le_n hRight

/-- Every canonical light edge respects symmetric external-node order. -/
theorem mem_treeEdges_side_order {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST lower upper)
    (upper_le_n : upper ≤ n) {depth : ℕ} {edge : Edge n}
    (hMember : edge ∈ treeEdges snapshot tree upper_le_n depth) :
    match edge.side with
    | .left => edge.child.val < edge.owner.val
    | .right => edge.owner.val < edge.child.val := by
  induction tree generalizing depth with
  | empty =>
      simp [treeEdges] at hMember
  | @node lower root upper left right ihLeft ihRight =>
      rw [treeEdges] at hMember
      rcases List.mem_append.mp hMember with hPrefix | hRight
      · rcases List.mem_append.mp hPrefix with hLocal | hLeft
        · exact
            (mem_edgesAtNode_valid snapshot
              {
                lower := lower
                root := root
                upper := upper
                left := left
                right := right
                upper_le_n := upper_le_n
              } depth hLocal).side_order
        · exact ihLeft (by
            have hRootUpper := right.lower_le_upper
            omega) hLeft
      · exact ihRight upper_le_n hRight

/-- A canonical light edge never loops from a vertex to itself. -/
theorem mem_treeEdges_child_ne_owner {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST lower upper)
    (upper_le_n : upper ≤ n) {depth : ℕ} {edge : Edge n}
    (hMember : edge ∈ treeEdges snapshot tree upper_le_n depth) :
    edge.child ≠ edge.owner := by
  intro hEqual
  have hRank :=
    mem_treeEdges_rank_lt snapshot tree upper_le_n hMember
  rw [hEqual] at hRank
  exact Nat.lt_irrefl _ hRank

/-- The persistent attachment key of a canonical edge belongs to its BST. -/
theorem mem_treeEdges_attachmentKey_bounds {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST lower upper)
    (upper_le_n : upper ≤ n) {depth : ℕ} {edge : Edge n}
    (hMember : edge ∈ treeEdges snapshot tree upper_le_n depth) :
    lower ≤ edge.attachmentKey ∧ edge.attachmentKey < upper := by
  induction tree generalizing depth with
  | empty =>
      simp [treeEdges] at hMember
  | @node lower root upper left right ihLeft ihRight =>
      rw [treeEdges] at hMember
      rcases List.mem_append.mp hMember with hPrefix | hRight
      · rcases List.mem_append.mp hPrefix with hLocal | hLeft
        · have attachment :=
            mem_edgesAtNode_attachmentKey snapshot {
              lower := lower
              root := root
              upper := upper
              left := left
              right := right
              upper_le_n := upper_le_n
            } depth hLocal
          change edge.attachmentKey = root at attachment
          rw [attachment]
          exact ⟨left.lower_le_upper, by
            have := right.lower_le_upper
            omega⟩
        · have childBounds := ihLeft (by
            have := right.lower_le_upper
            omega) hLeft
          have rootLtUpper : root < upper := by
            have := right.lower_le_upper
            omega
          exact ⟨childBounds.1, childBounds.2.trans rootLtUpper⟩
      · have childBounds := ihRight upper_le_n hRight
        have lowerLeRoot : lower ≤ root := left.lower_le_upper
        exact ⟨lowerLeRoot.trans (by omega), childBounds.2⟩

theorem mem_treeEdges_inside {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST lower upper)
    (upper_le_n : upper ≤ n) {depth : ℕ} {edge : Edge n}
    (hMember : edge ∈ treeEdges snapshot tree upper_le_n depth) :
    subtreeLower tree upper_le_n ≤ edge.owner ∧
      edge.owner ≤ subtreeUpper tree upper_le_n ∧
      subtreeLower tree upper_le_n ≤ edge.child ∧
      edge.child ≤ subtreeUpper tree upper_le_n := by
  induction tree generalizing depth with
  | empty =>
      simp [treeEdges] at hMember
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      rw [treeEdges] at hMember
      rcases List.mem_append.mp hMember with hPrefix | hRight
      · rcases List.mem_append.mp hPrefix with hLocal | hLeft
        · have hValid := mem_edgesAtNode_valid snapshot node depth hLocal
          have hOwner := node.owner_isMin snapshot
          have hChild := node.branchMin_in_whole snapshot edge.branch
          rw [hValid.2.1, hValid.2.2.1]
          exact ⟨hOwner.1, hOwner.2.1, hChild.1, hChild.2⟩
        · have hLeftBound : root ≤ n := by
            have hRootUpper := right.lower_le_upper
            omega
          have hInside := ihLeft hLeftBound hLeft
          have hLowerEq :
              subtreeLower left hLeftBound =
                subtreeLower (.node left right) upper_le_n := by
            rfl
          have hUpperLe :
            subtreeUpper left hLeftBound ≤
                subtreeUpper (.node left right) upper_le_n := by
            simp only [subtreeUpper, Fin.mk_le_mk]
            apply Nat.mul_le_mul_left
            exact (Nat.le_succ root).trans right.lower_le_upper
          have hOwnerUpper :
              edge.owner ≤ subtreeUpper (.node left right) upper_le_n :=
            calc
              edge.owner ≤ subtreeUpper left hLeftBound := hInside.2.1
              _ ≤ subtreeUpper (.node left right) upper_le_n := hUpperLe
          have hChildUpper :
              edge.child ≤ subtreeUpper (.node left right) upper_le_n :=
            calc
              edge.child ≤ subtreeUpper left hLeftBound := hInside.2.2.2
              _ ≤ subtreeUpper (.node left right) upper_le_n := hUpperLe
          refine ⟨?_, hOwnerUpper, ?_, hChildUpper⟩
          · rw [← hLowerEq]
            exact hInside.1
          · rw [← hLowerEq]
            exact hInside.2.2.1
      · have hInside := ihRight upper_le_n hRight
        have hLowerLe :
            subtreeLower (.node left right) upper_le_n ≤
              subtreeLower right upper_le_n := by
          simp only [subtreeLower, Fin.mk_le_mk]
          have hLowerRoot := left.lower_le_upper
          omega
        have hUpperEq :
            subtreeUpper right upper_le_n =
              subtreeUpper (.node left right) upper_le_n := by
          rfl
        have hOwnerLower :
            subtreeLower (.node left right) upper_le_n ≤ edge.owner :=
          calc
            subtreeLower (.node left right) upper_le_n ≤
                subtreeLower right upper_le_n := hLowerLe
            _ ≤ edge.owner := hInside.1
        have hChildLower :
            subtreeLower (.node left right) upper_le_n ≤ edge.child :=
          calc
            subtreeLower (.node left right) upper_le_n ≤
                subtreeLower right upper_le_n := hLowerLe
            _ ≤ edge.child := hInside.2.2.1
        refine ⟨hOwnerLower, ?_, hChildLower, ?_⟩
        · rw [← hUpperEq]
          exact hInside.2.1
        · rw [← hUpperEq]
          exact hInside.2.2.2

theorem subtreeOwner_rank_lt_child_of_mem {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST lower upper)
    (upper_le_n : upper ≤ n) {depth : ℕ} {edge : Edge n}
    (hMember : edge ∈ treeEdges snapshot tree upper_le_n depth) :
    snapshot.rank (subtreeOwner snapshot tree upper_le_n) <
      snapshot.rank edge.child := by
  have hInside := mem_treeEdges_inside snapshot tree upper_le_n hMember
  have hRootLe :
      snapshot.rank (subtreeOwner snapshot tree upper_le_n) ≤
        snapshot.rank edge.owner :=
    (subtreeOwner_isMin snapshot tree upper_le_n).2.2
      edge.owner hInside.1 hInside.2.1
  exact lt_of_le_of_lt hRootLe
    (mem_treeEdges_rank_lt snapshot tree upper_le_n hMember)

/-- Canonical light-edge regions are laminar in symmetric order.

If two distinct canonical edges have the same owner, then every edge leaving
the first child stays on the first child's side of the second child.  This is
the structural fact behind the manuscript's statement that reparenting a
paired loser installs it as the new top-most child of the winner. -/
theorem mem_treeEdges_nested_children {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST lower upper)
    (upper_le_n : upper ≤ n) {depth : ℕ}
    {winnerEdge loserEdge childEdge : Edge n}
    (winnerMember : winnerEdge ∈
      treeEdges snapshot tree upper_le_n depth)
    (loserMember : loserEdge ∈
      treeEdges snapshot tree upper_le_n depth)
    (childMember : childEdge ∈
      treeEdges snapshot tree upper_le_n depth)
    (sameOwner : winnerEdge.owner = loserEdge.owner)
    (childOwner : childEdge.owner = winnerEdge.child)
    (different : winnerEdge.child ≠ loserEdge.child) :
    if loserEdge.child.val < winnerEdge.child.val then
      loserEdge.child.val < childEdge.child.val
    else
      childEdge.child.val < loserEdge.child.val := by
  induction tree generalizing depth with
  | empty =>
      simp [treeEdges] at winnerMember
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      have leftBound : root ≤ n := by
        have := right.lower_le_upper
        omega
      have leftOwnerUpper {edge : Edge n}
          (member : edge ∈
            treeEdges snapshot left leftBound (depth + 1)) :
          edge.owner.val ≤ 2 * root := by
        have inside :=
          mem_treeEdges_inside snapshot left leftBound member
        change edge.owner.val ≤ 2 * root
        exact inside.2.1
      have leftChildUpper {edge : Edge n}
          (member : edge ∈
            treeEdges snapshot left leftBound (depth + 1)) :
          edge.child.val ≤ 2 * root := by
        have inside :=
          mem_treeEdges_inside snapshot left leftBound member
        change edge.child.val ≤ 2 * root
        exact inside.2.2.2
      have rightOwnerLower {edge : Edge n}
          (member : edge ∈
            treeEdges snapshot right upper_le_n (depth + 1)) :
          2 * root + 2 ≤ edge.owner.val := by
        have inside :=
          mem_treeEdges_inside snapshot right upper_le_n member
        change 2 * root + 2 ≤ edge.owner.val
        exact inside.1
      have rightChildLower {edge : Edge n}
          (member : edge ∈
            treeEdges snapshot right upper_le_n (depth + 1)) :
          2 * root + 2 ≤ edge.child.val := by
        have inside :=
          mem_treeEdges_inside snapshot right upper_le_n member
        change 2 * root + 2 ≤ edge.child.val
        exact inside.2.2.1
      have differentValues :
          winnerEdge.child.val ≠ loserEdge.child.val := by
        intro valuesEqual
        exact different (Fin.ext valuesEqual)
      have childCannotBeLocal
          (winnerFull : winnerEdge ∈
            treeEdges snapshot (.node left right) upper_le_n depth)
          (childLocal : childEdge ∈ edgesAtNode snapshot node depth) :
          False := by
        have rankLt :=
          subtreeOwner_rank_lt_child_of_mem snapshot (.node left right)
            upper_le_n winnerFull
        have childValid :=
          mem_edgesAtNode_valid snapshot node depth childLocal
        have ownerEq :
            subtreeOwner snapshot (.node left right) upper_le_n =
              winnerEdge.child := by
          change node.owner snapshot = winnerEdge.child
          exact childValid.2.1.symm.trans childOwner
        rw [ownerEq] at rankLt
        exact Nat.lt_irrefl _ rankLt
      rw [treeEdges] at winnerMember loserMember childMember
      rcases List.mem_append.mp winnerMember with winnerPrefix | winnerRight
      · rcases List.mem_append.mp winnerPrefix with
          winnerLocal | winnerLeft
        · have winnerValid :=
            mem_edgesAtNode_valid snapshot node depth winnerLocal
          rcases List.mem_append.mp loserMember with loserPrefix | loserRight
          · rcases List.mem_append.mp loserPrefix with
              loserLocal | loserLeft
            · have loserValid :=
                mem_edgesAtNode_valid snapshot node depth loserLocal
              rcases List.mem_append.mp childMember with
                  childPrefix | childRight
              · rcases List.mem_append.mp childPrefix with
                    childLocal | childLeft
                · have childValid :=
                    mem_edgesAtNode_valid snapshot node depth childLocal
                  have winnerChildEqOwner :
                      winnerEdge.child = winnerEdge.owner := by
                    calc
                      winnerEdge.child = childEdge.owner := childOwner.symm
                      _ = node.owner snapshot := childValid.2.1
                      _ = winnerEdge.owner := winnerValid.2.1.symm
                  exact False.elim
                    (winnerValid.child_ne_owner winnerChildEqOwner)
                · have winnerChildUpper :
                      winnerEdge.child.val ≤ 2 * root := by
                    rw [← childOwner]
                    exact leftOwnerUpper childLeft
                  have loserChildLower :
                      2 * root < loserEdge.child.val :=
                    winnerValid.other_child_gt_root_of_child_le
                      loserValid different winnerChildUpper
                  have childUpper := leftChildUpper childLeft
                  have notLoserBefore :
                      ¬ loserEdge.child.val < winnerEdge.child.val := by omega
                  simp only [if_neg notLoserBefore]
                  omega
              · have winnerChildLower :
                    2 * root + 2 ≤ winnerEdge.child.val := by
                  rw [← childOwner]
                  exact rightOwnerLower childRight
                have loserChildUpper :
                    loserEdge.child.val < 2 * root + 2 :=
                  winnerValid.other_child_lt_root_of_root_le_child
                    loserValid different winnerChildLower
                have childLower := rightChildLower childRight
                have loserBefore :
                    loserEdge.child.val < winnerEdge.child.val := by omega
                simp only [if_pos loserBefore]
                omega
            · have nodeOwnerLeft :
                  (node.owner snapshot).val ≤ 2 * root := by
                rw [← winnerValid.2.1, sameOwner]
                exact leftOwnerUpper loserLeft
              have heavyLeft :=
                node.heavyBranch_eq_left_of_owner_le_root
                  snapshot nodeOwnerLeft
              have winnerChildLower :=
                winnerValid.child_gt_root_of_heavy_left heavyLeft
              change 2 * root < winnerEdge.child.val at winnerChildLower
              rcases List.mem_append.mp childMember with
                  childPrefix | childRight
              · rcases List.mem_append.mp childPrefix with
                    childLocal | childLeft
                · have childValid :=
                    mem_edgesAtNode_valid snapshot node depth childLocal
                  have winnerChildEqOwner :
                      winnerEdge.child = winnerEdge.owner := by
                    calc
                      winnerEdge.child = childEdge.owner := childOwner.symm
                      _ = node.owner snapshot := childValid.2.1
                      _ = winnerEdge.owner := winnerValid.2.1.symm
                  exact False.elim
                    (winnerValid.child_ne_owner winnerChildEqOwner)
                · have childOwnerUpper := leftOwnerUpper childLeft
                  rw [childOwner] at childOwnerUpper
                  omega
              · have loserUpper := leftChildUpper loserLeft
                have childLower := rightChildLower childRight
                have loserBefore :
                    loserEdge.child.val < winnerEdge.child.val := by omega
                simp only [if_pos loserBefore]
                omega
          · have nodeOwnerRight :
                2 * root + 2 ≤ (node.owner snapshot).val := by
              rw [← winnerValid.2.1, sameOwner]
              exact rightOwnerLower loserRight
            have heavyRight :=
              node.heavyBranch_eq_right_of_root_lt_owner
                snapshot nodeOwnerRight
            have winnerChildUpper :=
              winnerValid.child_lt_root_of_heavy_right heavyRight
            change winnerEdge.child.val < 2 * root + 2 at winnerChildUpper
            rcases List.mem_append.mp childMember with
                childPrefix | childRight
            · rcases List.mem_append.mp childPrefix with
                  childLocal | childLeft
              · have childValid :=
                  mem_edgesAtNode_valid snapshot node depth childLocal
                have winnerChildEqOwner :
                    winnerEdge.child = winnerEdge.owner := by
                  calc
                    winnerEdge.child = childEdge.owner := childOwner.symm
                    _ = node.owner snapshot := childValid.2.1
                    _ = winnerEdge.owner := winnerValid.2.1.symm
                exact False.elim
                  (winnerValid.child_ne_owner winnerChildEqOwner)
              · have loserLower := rightChildLower loserRight
                have childUpper := leftChildUpper childLeft
                have notLoserBefore :
                    ¬ loserEdge.child.val < winnerEdge.child.val := by omega
                simp only [if_neg notLoserBefore]
                omega
            · have childOwnerLower := rightOwnerLower childRight
              rw [childOwner] at childOwnerLower
              omega
        · rcases List.mem_append.mp loserMember with loserPrefix | loserRight
          · rcases List.mem_append.mp loserPrefix with
              loserLocal | loserLeft
            · have loserValid :=
                mem_edgesAtNode_valid snapshot node depth loserLocal
              have nodeOwnerLeft :
                  (node.owner snapshot).val ≤ 2 * root := by
                rw [← loserValid.2.1, ← sameOwner]
                exact leftOwnerUpper winnerLeft
              have heavyLeft :=
                node.heavyBranch_eq_left_of_owner_le_root
                  snapshot nodeOwnerLeft
              have loserChildLower :=
                loserValid.child_gt_root_of_heavy_left heavyLeft
              change 2 * root < loserEdge.child.val at loserChildLower
              rcases List.mem_append.mp childMember with
                  childPrefix | childRight
              · rcases List.mem_append.mp childPrefix with
                    childLocal | childLeft
                · have winnerFull : winnerEdge ∈
                      treeEdges snapshot (.node left right)
                        upper_le_n depth := by
                    simp only [treeEdges, List.mem_append]
                    exact Or.inl (Or.inr winnerLeft)
                  exact False.elim
                    (childCannotBeLocal winnerFull childLocal)
                · have winnerUpper := leftChildUpper winnerLeft
                  have childUpper := leftChildUpper childLeft
                  have notLoserBefore :
                      ¬ loserEdge.child.val < winnerEdge.child.val := by omega
                  simp only [if_neg notLoserBefore]
                  omega
              · have winnerUpper := leftChildUpper winnerLeft
                have childOwnerLower := rightOwnerLower childRight
                rw [childOwner] at childOwnerLower
                omega
            · rcases List.mem_append.mp childMember with
                  childPrefix | childRight
              · rcases List.mem_append.mp childPrefix with
                    childLocal | childLeft
                · have winnerFull : winnerEdge ∈
                      treeEdges snapshot (.node left right)
                        upper_le_n depth := by
                    simp only [treeEdges, List.mem_append]
                    exact Or.inl (Or.inr winnerLeft)
                  exact False.elim
                    (childCannotBeLocal winnerFull childLocal)
                · exact ihLeft leftBound winnerLeft loserLeft childLeft
              · have winnerUpper := leftChildUpper winnerLeft
                have childOwnerLower := rightOwnerLower childRight
                rw [childOwner] at childOwnerLower
                omega
          · have winnerOwnerUpper := leftOwnerUpper winnerLeft
            have loserOwnerLower := rightOwnerLower loserRight
            have ownerValuesEqual := congrArg Fin.val sameOwner
            omega
      · rcases List.mem_append.mp loserMember with loserPrefix | loserRight
        · rcases List.mem_append.mp loserPrefix with
            loserLocal | loserLeft
          · have loserValid :=
              mem_edgesAtNode_valid snapshot node depth loserLocal
            have nodeOwnerRight :
                2 * root + 2 ≤ (node.owner snapshot).val := by
              rw [← loserValid.2.1, ← sameOwner]
              exact rightOwnerLower winnerRight
            have heavyRight :=
              node.heavyBranch_eq_right_of_root_lt_owner
                snapshot nodeOwnerRight
            have loserChildUpper :=
              loserValid.child_lt_root_of_heavy_right heavyRight
            change loserEdge.child.val < 2 * root + 2 at loserChildUpper
            rcases List.mem_append.mp childMember with
                childPrefix | childRight
            · rcases List.mem_append.mp childPrefix with
                  childLocal | childLeft
              · have winnerFull : winnerEdge ∈
                    treeEdges snapshot (.node left right)
                      upper_le_n depth := by
                  simp only [treeEdges, List.mem_append]
                  exact Or.inr winnerRight
                exact False.elim
                  (childCannotBeLocal winnerFull childLocal)
              · have winnerLower := rightChildLower winnerRight
                have childOwnerUpper := leftOwnerUpper childLeft
                rw [childOwner] at childOwnerUpper
                omega
            · have winnerLower := rightChildLower winnerRight
              have childLower := rightChildLower childRight
              have loserBefore :
                  loserEdge.child.val < winnerEdge.child.val := by omega
              simp only [if_pos loserBefore]
              omega
          · have winnerOwnerLower := rightOwnerLower winnerRight
            have loserOwnerUpper := leftOwnerUpper loserLeft
            have ownerValuesEqual := congrArg Fin.val sameOwner
            omega
        · rcases List.mem_append.mp childMember with childPrefix | childRight
          · rcases List.mem_append.mp childPrefix with childLocal | childLeft
            · have winnerFull : winnerEdge ∈
                  treeEdges snapshot (.node left right) upper_le_n depth := by
                simp only [treeEdges, List.mem_append]
                exact Or.inr winnerRight
              exact False.elim
                (childCannotBeLocal winnerFull childLocal)
            · have winnerLower := rightChildLower winnerRight
              have childOwnerUpper := leftOwnerUpper childLeft
              rw [childOwner] at childOwnerUpper
              omega
          · exact ihRight upper_le_n winnerRight loserRight childRight

/--
No external vertex starts two canonical light edges.

This is the key ownership fact omitted by the abstract interval interface. At
a splay-tree node, the two local children belong to distinct ternary
branches.  A local child on a recursive branch is that branch's interval
minimum, whereas every recursive light-edge child has strictly larger rank.
The left and right recursive lists are separated by symmetric order.
-/
@[simp]
theorem treeChildren_nodup {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST lower upper)
    (upper_le_n : upper ≤ n) (depth : ℕ := 0) :
    (treeChildren snapshot tree upper_le_n depth).Nodup := by
  induction tree generalizing depth with
  | empty =>
      simp [treeChildren, treeEdges]
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      have hLeftBound : root ≤ n := by
        have hRootUpper := right.lower_le_upper
        omega
      let localChildren :=
        (edgesAtNode snapshot node depth).map Edge.child
      let leftChildren :=
        treeChildren snapshot left hLeftBound (depth + 1)
      let rightChildren :=
        treeChildren snapshot right upper_le_n (depth + 1)
      have hLocalNodup : localChildren.Nodup := by
        exact edgesAtNode_children_nodup snapshot node depth
      have hLeftNodup : leftChildren.Nodup := by
        exact ihLeft hLeftBound (depth + 1)
      have hRightNodup : rightChildren.Nodup := by
        exact ihRight upper_le_n (depth + 1)
      have hLocalLeft : localChildren.Disjoint leftChildren := by
        rw [List.disjoint_left]
        intro child hLocal hLeft
        rcases List.mem_map.mp hLocal with
          ⟨localEdge, hLocalEdge, hLocalChild⟩
        rcases List.mem_map.mp hLeft with
          ⟨leftEdge, hLeftEdge, hLeftChild⟩
        have hValid :=
          mem_edgesAtNode_valid snapshot node depth hLocalEdge
        have hLeftInside :=
          mem_treeEdges_inside snapshot left hLeftBound hLeftEdge
        have hLeftRank :=
          subtreeOwner_rank_lt_child_of_mem
            snapshot left hLeftBound hLeftEdge
        have hChildEq : localEdge.child = leftEdge.child :=
          hLocalChild.trans hLeftChild.symm
        cases hBranch : localEdge.branch with
        | left =>
            have hLocalIsOwner :
                localEdge.child =
                  subtreeOwner snapshot left hLeftBound := by
              calc
                localEdge.child =
                    node.branchMin snapshot localEdge.branch :=
                  hValid.2.2.1
                _ = node.branchMin snapshot .left := by rw [hBranch]
                _ = subtreeOwner snapshot left hLeftBound := by
                  exact node_left_branchMin_eq_subtreeOwner
                    snapshot left right upper_le_n
            rw [← hChildEq, hLocalIsOwner] at hLeftRank
            exact (Nat.lt_irrefl _ hLeftRank)
        | middle =>
            have hLocalPosition :
                localEdge.child.val = 2 * root + 1 := by
              rw [hValid.2.2.1, hBranch]
              exact node.branchMin_in_branch snapshot .middle
            have hLeftPosition : leftEdge.child.val ≤ 2 * root := by
              exact hLeftInside.2.2.2
            have hPositionEq :
                localEdge.child.val = leftEdge.child.val :=
              congrArg Fin.val hChildEq
            omega
        | right =>
            have hLocalPosition :
                2 * root + 2 ≤ localEdge.child.val := by
              rw [hValid.2.2.1, hBranch]
              exact node.branchMin_in_branch snapshot .right
            have hLeftPosition : leftEdge.child.val ≤ 2 * root := by
              exact hLeftInside.2.2.2
            have hPositionEq :
                localEdge.child.val = leftEdge.child.val :=
              congrArg Fin.val hChildEq
            omega
      have hLocalRight : localChildren.Disjoint rightChildren := by
        rw [List.disjoint_left]
        intro child hLocal hRight
        rcases List.mem_map.mp hLocal with
          ⟨localEdge, hLocalEdge, hLocalChild⟩
        rcases List.mem_map.mp hRight with
          ⟨rightEdge, hRightEdge, hRightChild⟩
        have hValid :=
          mem_edgesAtNode_valid snapshot node depth hLocalEdge
        have hRightInside :=
          mem_treeEdges_inside snapshot right upper_le_n hRightEdge
        have hRightRank :=
          subtreeOwner_rank_lt_child_of_mem
            snapshot right upper_le_n hRightEdge
        have hChildEq : localEdge.child = rightEdge.child :=
          hLocalChild.trans hRightChild.symm
        cases hBranch : localEdge.branch with
        | left =>
            have hLocalPosition :
                localEdge.child.val ≤ 2 * root := by
              rw [hValid.2.2.1, hBranch]
              exact node.branchMin_in_branch snapshot .left
            have hRightPosition :
                2 * (root + 1) ≤ rightEdge.child.val := by
              exact hRightInside.2.2.1
            have hPositionEq :
                localEdge.child.val = rightEdge.child.val :=
              congrArg Fin.val hChildEq
            omega
        | middle =>
            have hLocalPosition :
                localEdge.child.val = 2 * root + 1 := by
              rw [hValid.2.2.1, hBranch]
              exact node.branchMin_in_branch snapshot .middle
            have hRightPosition :
                2 * (root + 1) ≤ rightEdge.child.val := by
              exact hRightInside.2.2.1
            have hPositionEq :
                localEdge.child.val = rightEdge.child.val :=
              congrArg Fin.val hChildEq
            omega
        | right =>
            have hLocalIsOwner :
                localEdge.child =
                  subtreeOwner snapshot right upper_le_n := by
              calc
                localEdge.child =
                    node.branchMin snapshot localEdge.branch :=
                  hValid.2.2.1
                _ = node.branchMin snapshot .right := by rw [hBranch]
                _ = subtreeOwner snapshot right upper_le_n := by
                  exact node_right_branchMin_eq_subtreeOwner
                    snapshot left right upper_le_n
            rw [← hChildEq, hLocalIsOwner] at hRightRank
            exact (Nat.lt_irrefl _ hRightRank)
      have hLeftRight : leftChildren.Disjoint rightChildren := by
        rw [List.disjoint_left]
        intro child hLeft hRight
        rcases List.mem_map.mp hLeft with
          ⟨leftEdge, hLeftEdge, hLeftChild⟩
        rcases List.mem_map.mp hRight with
          ⟨rightEdge, hRightEdge, hRightChild⟩
        have hLeftInside :=
          mem_treeEdges_inside snapshot left hLeftBound hLeftEdge
        have hRightInside :=
          mem_treeEdges_inside snapshot right upper_le_n hRightEdge
        have hLeftPosition : leftEdge.child.val ≤ 2 * root :=
          hLeftInside.2.2.2
        have hRightPosition :
            2 * (root + 1) ≤ rightEdge.child.val :=
          hRightInside.2.2.1
        have hPositionEq : leftEdge.child.val = rightEdge.child.val :=
          congrArg Fin.val (hLeftChild.trans hRightChild.symm)
        omega
      have hPrefixNodup :
          (localChildren ++ leftChildren).Nodup :=
        hLocalNodup.append hLeftNodup hLocalLeft
      have hPrefixRight :
          (localChildren ++ leftChildren).Disjoint rightChildren := by
        exact List.disjoint_append_left.mpr ⟨hLocalRight, hLeftRight⟩
      rw [treeChildren, treeEdges]
      simp only [List.map_append]
      exact hPrefixNodup.append hRightNodup hPrefixRight

/-- Canonical light-edge records themselves are duplicate-free. -/
@[simp]
theorem treeEdges_nodup {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST lower upper)
    (upper_le_n : upper ≤ n) (depth : ℕ := 0) :
    (treeEdges snapshot tree upper_le_n depth).Nodup := by
  apply List.Nodup.of_map Edge.child
  simpa only [treeChildren] using
    treeChildren_nodup snapshot tree upper_le_n depth

/--
The canonical owner of a subtree is not the child endpoint of any canonical
light edge inside that subtree.

Every such child has strictly larger rank than the subtree owner, so this
also rules out the only vertex that must have no heap parent.
-/
theorem subtreeOwner_not_mem_treeChildren {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST lower upper)
    (upper_le_n : upper ≤ n) (depth : ℕ := 0) :
    subtreeOwner snapshot tree upper_le_n ∉
      treeChildren snapshot tree upper_le_n depth := by
  intro hMember
  obtain ⟨edge, hEdge, hChild⟩ := List.mem_map.mp hMember
  have hRank :=
    subtreeOwner_rank_lt_child_of_mem
      snapshot tree upper_le_n hEdge
  rw [hChild] at hRank
  exact Nat.lt_irrefl _ hRank

/--
For a full splay-tree shape under the supplied comparison ranks, the canonical
light-edge children are exactly all external vertices except the canonical
root.

There are `2 * n` light edges, their child endpoints are distinct, and the
external carrier has `2 * n + 1` vertices.  Together with the preceding
rank argument this turns the local light-edge construction into a rooted
spanning tree.
-/
theorem mem_treeChildren_iff_ne_subtreeOwner {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (depth : ℕ := 0) (child : External n) :
    child ∈ treeChildren snapshot tree (Nat.le_refl n) depth ↔
      child ≠ subtreeOwner snapshot tree (Nat.le_refl n) := by
  let children :=
    treeChildren snapshot tree (Nat.le_refl n) depth
  let root :=
    subtreeOwner snapshot tree (Nat.le_refl n)
  have hNodup : children.Nodup := by
    exact treeChildren_nodup snapshot tree (Nat.le_refl n) depth
  have hRootNotMem : root ∉ children := by
    exact subtreeOwner_not_mem_treeChildren
      snapshot tree (Nat.le_refl n) depth
  have hSubset :
      children.toFinset ⊆ (Finset.univ : Finset (External n)).erase root := by
    intro element hElement
    rw [Finset.mem_erase]
    constructor
    · intro hEqual
      subst element
      exact hRootNotMem (by simpa using hElement)
    · exact Finset.mem_univ element
  have hChildrenCard : children.toFinset.card = 2 * n := by
    rw [List.toFinset_card_of_nodup hNodup]
    simp [children]
  have hTargetCard :
      ((Finset.univ : Finset (External n)).erase root).card = 2 * n := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ root)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hChildren :
      children.toFinset =
        (Finset.univ : Finset (External n)).erase root := by
    apply Finset.eq_of_subset_of_card_le hSubset
    omega
  change child ∈ children ↔ child ≠ root
  rw [← List.mem_toFinset, hChildren, Finset.mem_erase]
  simp

end Splay.Lazy.Canonical
