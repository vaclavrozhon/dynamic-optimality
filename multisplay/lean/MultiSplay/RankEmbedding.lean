import MultiSplay.OrdinalShift
import Splay.Lazy.Canonical

/-!
# Keeping the splay heavy-path decomposition under component embeddings

A component embedded at ordinal offset `offset` maps external positions by
`position ↦ 2 * offset + position`. If every rank in that component is increased
by the same amount, every interval minimum, heavy branch, and internal light
edge is retained. This applies to the uniform rank increase at a common join.
-/

namespace MultiSplay.RankEmbedding

open Splay.Rank (External Snapshot IsIntervalMin TernaryBranch)
open Splay.Lazy.Canonical (AtNode Edge)

variable {n m : Nat}

def external (offset : Nat) (fits : offset + n ≤ m) (position : External n) : External m :=
  ⟨2 * offset + position.val, by have := position.isLt; omega⟩

@[simp] theorem external_le (offset : Nat) (fits : offset + n ≤ m) (a b : External n) :
    external offset fits a ≤ external offset fits b ↔ a ≤ b := by
  change 2 * offset + a.val ≤ 2 * offset + b.val ↔ a.val ≤ b.val
  omega

@[simp] theorem external_lt (offset : Nat) (fits : offset + n ≤ m) (a b : External n) :
    external offset fits a < external offset fits b ↔ a < b := by
  change 2 * offset + a.val < 2 * offset + b.val ↔ a.val < b.val
  omega

theorem external_injective (offset : Nat) (fits : offset + n ≤ m) :
    Function.Injective (external offset fits) := by
  intro a b same
  apply Fin.ext
  have h := congrArg Fin.val same
  simp only [external] at h
  omega

theorem between (offset : Nat) (fits : offset + n ≤ m) (lower upper : External n)
    (candidate : External m) (lo : external offset fits lower ≤ candidate)
    (hi : candidate ≤ external offset fits upper) :
    ∃ position : External n, candidate = external offset fits position ∧ lower ≤ position ∧ position ≤ upper := by
  have upperBound := upper.isLt
  change 2 * offset + lower.val ≤ candidate.val at lo
  change candidate.val ≤ 2 * offset + upper.val at hi
  let position : External n := ⟨candidate.val - 2 * offset, by omega⟩
  refine ⟨position, ?_, ?_, ?_⟩
  · apply Fin.ext
    dsimp [external, position]
    omega
  · change lower.val ≤ candidate.val - 2 * offset
    omega
  · change candidate.val - 2 * offset ≤ upper.val
    omega

/-- The rank equation is local to the embedded component; outside ranks may
be arbitrary. Thus the theorem applies inside a larger common forest. -/
theorem intervalMin (offset delta : Nat) (fits : offset + n ≤ m)
    (before : Snapshot n) (after : Snapshot m)
    (ranks : ∀ position, after.rank (external offset fits position) = before.rank position + delta)
    (lower upper : External n) (nonempty : lower ≤ upper) :
    after.intervalMin (external offset fits lower) (external offset fits upper)
        ((external_le offset fits lower upper).mpr nonempty) =
      external offset fits (before.intervalMin lower upper nonempty) := by
  symm
  apply after.intervalMin_unique
  have minimum := before.intervalMin_isMin lower upper nonempty
  refine ⟨(external_le offset fits _ _).mpr minimum.1,
    (external_le offset fits _ _).mpr minimum.2.1, ?_⟩
  intro candidate lo hi
  obtain ⟨position, rfl, lo, hi⟩ := between offset fits lower upper candidate lo hi
  rw [ranks, ranks]
  exact Nat.add_le_add_right (minimum.2.2 position lo hi) delta

def node (offset : Nat) (fits : offset + n ≤ m) (source : AtNode n) : AtNode m where
  lower := offset + source.lower
  root := offset + source.root
  upper := offset + source.upper
  left := OrdinalShift.tree offset source.left
  right := OrdinalShift.tree offset source.right
  upper_le_n := by have := source.upper_le_n; omega

@[simp] theorem node_wholeLower (offset : Nat) (fits : offset + n ≤ m) (source : AtNode n) :
    (node offset fits source).wholeLower = external offset fits source.wholeLower := by
  apply Fin.ext
  simp [node, AtNode.wholeLower, external, Nat.mul_add]

@[simp] theorem node_wholeUpper (offset : Nat) (fits : offset + n ≤ m) (source : AtNode n) :
    (node offset fits source).wholeUpper = external offset fits source.wholeUpper := by
  apply Fin.ext
  simp [node, AtNode.wholeUpper, external, Nat.mul_add]

@[simp] theorem node_branchLower (offset : Nat) (fits : offset + n ≤ m) (source : AtNode n)
    (branch : TernaryBranch) :
    (node offset fits source).branchLower branch = external offset fits (source.branchLower branch) := by
  apply Fin.ext
  cases branch <;> simp [node, AtNode.branchLower, AtNode.wholeLower, external, Nat.mul_add, Nat.add_assoc]

@[simp] theorem node_branchUpper (offset : Nat) (fits : offset + n ≤ m) (source : AtNode n)
    (branch : TernaryBranch) :
    (node offset fits source).branchUpper branch = external offset fits (source.branchUpper branch) := by
  apply Fin.ext
  cases branch <;> simp [node, AtNode.branchUpper, AtNode.wholeUpper, external, Nat.mul_add, Nat.add_assoc]

theorem owner (offset delta : Nat) (fits : offset + n ≤ m)
    (before : Snapshot n) (after : Snapshot m)
    (ranks : ∀ position, after.rank (external offset fits position) = before.rank position + delta)
    (source : AtNode n) :
    (node offset fits source).owner after = external offset fits (source.owner before) := by
  simp only [AtNode.owner, node_wholeLower, node_wholeUpper]
  exact intervalMin offset delta fits before after ranks _ _ _

theorem branchMin (offset delta : Nat) (fits : offset + n ≤ m)
    (before : Snapshot n) (after : Snapshot m)
    (ranks : ∀ position, after.rank (external offset fits position) = before.rank position + delta)
    (source : AtNode n) (branch : TernaryBranch) :
    (node offset fits source).branchMin after branch = external offset fits (source.branchMin before branch) := by
  simp only [AtNode.branchMin, node_branchLower, node_branchUpper]
  exact intervalMin offset delta fits before after ranks _ _ _

@[simp] theorem contains (offset root : Nat) (fits : offset + n ≤ m)
    (position : External n) (branch : TernaryBranch) :
    branch.Contains (offset + root) (external offset fits position).val ↔
      branch.Contains root position.val := by
  cases branch <;> simp only [TernaryBranch.Contains, external] <;> omega

theorem heavyBranch (offset delta : Nat) (fits : offset + n ≤ m)
    (before : Snapshot n) (after : Snapshot m)
    (ranks : ∀ position, after.rank (external offset fits position) = before.rank position + delta)
    (source : AtNode n) :
    (node offset fits source).heavyBranch after = source.heavyBranch before := by
  obtain ⟨branch, branchContains, unique⟩ :=
    TernaryBranch.existsUnique_contains source.root (source.owner before).val
  have old := source.owner_in_heavyBranch before
  have new := (node offset fits source).owner_in_heavyBranch after
  rw [owner offset delta fits before after ranks source] at new
  have new' : ((node offset fits source).heavyBranch after).Contains source.root (source.owner before).val :=
    (contains offset source.root fits (source.owner before) _).mp new
  exact (unique _ new').trans (unique _ old).symm

def edge (offset depthDelta : Nat) (fits : offset + n ≤ m) (source : Edge n) : Edge m where
  branch := source.branch
  owner := external offset fits source.owner
  child := external offset fits source.child
  side := source.side
  attachmentKey := offset + source.attachmentKey
  attachmentDepth := depthDelta + source.attachmentDepth

@[simp] theorem sideOf (offset : Nat) (fits : offset + n ≤ m) (owner child : External n) :
    Splay.Lazy.Canonical.sideOf (external offset fits owner) (external offset fits child) =
      Splay.Lazy.Canonical.sideOf owner child := by
  simp [Splay.Lazy.Canonical.sideOf, external]

theorem edgeFor (offset delta depthDelta : Nat) (fits : offset + n ≤ m)
    (before : Snapshot n) (after : Snapshot m)
    (ranks : ∀ position, after.rank (external offset fits position) = before.rank position + delta)
    (source : AtNode n) (depth : Nat) (branch : TernaryBranch) :
    Splay.Lazy.Canonical.edgeFor after (node offset fits source) (depthDelta + depth) branch =
      edge offset depthDelta fits (Splay.Lazy.Canonical.edgeFor before source depth branch) := by
  unfold Splay.Lazy.Canonical.edgeFor
  rw [owner offset delta fits before after ranks, branchMin offset delta fits before after ranks]
  simp only [sideOf, edge, node]

theorem edgesAtNode (offset delta depthDelta : Nat) (fits : offset + n ≤ m)
    (before : Snapshot n) (after : Snapshot m)
    (ranks : ∀ position, after.rank (external offset fits position) = before.rank position + delta)
    (source : AtNode n) (depth : Nat) :
    Splay.Lazy.Canonical.edgesAtNode after (node offset fits source) (depthDelta + depth) =
      (Splay.Lazy.Canonical.edgesAtNode before source depth).map (edge offset depthDelta fits) := by
  simp only [Splay.Lazy.Canonical.edgesAtNode, Splay.Lazy.Canonical.lightBranches,
    heavyBranch offset delta fits before after ranks, List.map_map]
  apply List.map_congr_left
  intro branch member
  exact edgeFor offset delta depthDelta fits before after ranks source depth branch

/-- Every internal light edge survives a uniform local rank shift. Only its
ordinal address and the structural depth of its attachment are translated. -/
theorem treeEdges (offset delta depthDelta : Nat) (fits : offset + n ≤ m)
    (before : Snapshot n) (after : Snapshot m)
    (ranks : ∀ position, after.rank (external offset fits position) = before.rank position + delta)
    {lower upper : Nat} (source : Splay.Tree.BST lower upper) (inside : upper ≤ n) (depth : Nat) :
    Splay.Lazy.Canonical.treeEdges after (OrdinalShift.tree offset source)
        (by omega) (depthDelta + depth) =
      (Splay.Lazy.Canonical.treeEdges before source inside depth).map (edge offset depthDelta fits) := by
  induction source generalizing depth with
  | empty => rfl
  | @node lower root upper left right ihl ihr =>
      let current : AtNode n := ⟨lower, root, upper, left, right, inside⟩
      have bound : root ≤ n := by have := right.lower_le_upper; omega
      have first := edgesAtNode offset delta depthDelta fits before after ranks current depth
      have restLeft := ihl bound (depth + 1)
      have restRight := ihr inside (depth + 1)
      simp only [OrdinalShift.tree, Splay.Lazy.Canonical.treeEdges, List.map_append]
      change Splay.Lazy.Canonical.edgesAtNode after (node offset fits current) (depthDelta + depth) ++ _ ++ _ = _
      rw [first]
      rw [show depthDelta + depth + 1 = depthDelta + (depth + 1) by omega, restLeft, restRight]

theorem subtreeOwner (offset delta : Nat) (fits : offset + n ≤ m)
    (before : Snapshot n) (after : Snapshot m)
    (ranks : ∀ position, after.rank (external offset fits position) = before.rank position + delta)
    {lower upper : Nat} (source : Splay.Tree.BST lower upper) (inside : upper ≤ n) :
    Splay.Lazy.Canonical.subtreeOwner after (OrdinalShift.tree offset source) (by omega) =
      external offset fits (Splay.Lazy.Canonical.subtreeOwner before source inside) := by
  have lowerEq : Splay.Lazy.Canonical.subtreeLower (OrdinalShift.tree offset source) (by omega) =
      external offset fits (Splay.Lazy.Canonical.subtreeLower source inside) := by
    apply Fin.ext
    simp [Splay.Lazy.Canonical.subtreeLower, external, Nat.mul_add]
  have upperEq : Splay.Lazy.Canonical.subtreeUpper (OrdinalShift.tree offset source) (by omega) =
      external offset fits (Splay.Lazy.Canonical.subtreeUpper source inside) := by
    apply Fin.ext
    simp [Splay.Lazy.Canonical.subtreeUpper, external, Nat.mul_add]
  unfold Splay.Lazy.Canonical.subtreeOwner
  simp only [lowerEq, upperEq]
  exact intervalMin offset delta fits before after ranks _ _ _

/-- In particular, an internal lazy interval's signed raw gaps do not change. -/
theorem gap (offset delta : Nat) (fits : offset + n ≤ m)
    (before : Snapshot n) (after : Snapshot m)
    (ranks : ∀ position, after.rank (external offset fits position) = before.rank position + delta)
    (owner child : External n) :
    (after.rank (external offset fits child) : Int) - after.rank (external offset fits owner) =
      (before.rank child : Int) - before.rank owner := by
  rw [ranks, ranks]
  omega

end MultiSplay.RankEmbedding
