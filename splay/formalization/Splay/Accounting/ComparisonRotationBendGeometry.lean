import Splay.Accounting.JunctionBendReduction
import Splay.Assumptions.StructuralNormalForm
import Splay.Rank.SplayUpdate

namespace Splay.Accounting.ComparisonRotationBendGeometry

open Splay.Rank
open Splay.Tree
open Splay.Tree.BST
open Splay.Assumptions.NormalForm
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.JunctionBendReduction

/--
The structural information already exported for one comparison-tree
rotation: the rotation is genuine, its depth is uniformly bounded, and both
endpoint snapshots satisfy the relevant-neighbor rank bound.

`RotationAt.existsExactTreeRankUpdate` additionally supplies the exact
pointwise `-1/0/1` rank update.  The exact junction budget is isolated below
as `JunctionBound`; `ComparisonRotationJunctionBound` subsequently proves
that budget `1` always suffices, independently of the depth and neighbor-rank
fields retained here for the surrounding structural-normal-form API.
-/
structure BoundedComparisonRotation
    {n depth : ℕ}
    (splayTree beforeComparison afterComparison : BST 0 n)
    (maxRotationDepth neighborRankBound : ℕ) : Prop where
  rotation :
    RotationAt depth beforeComparison afterComparison
  depth_le :
    depth ≤ maxRotationDepth
  before_neighborRank :
    HasRelevantNeighborRankBound
      (Snapshot.ofTree beforeComparison) neighborRankBound
  after_neighborRank :
    HasRelevantNeighborRankBound
      (Snapshot.ofTree afterComparison) neighborRankBound

namespace BoundedComparisonRotation

/--
Every structurally normal comparison-trace step yields the bounded local
rotation context needed by this module.
-/
theorem ofTrace
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    (normal : IsStructurallyNormal bounds trace)
    (splayTree : BST 0 n) (step : Fin trace.rotationCount) :
    BoundedComparisonRotation
      (depth := trace.rotationDepth step)
      splayTree
      (trace.state step.castSucc) (trace.state step.succ)
      bounds.maxRotationDepth bounds.neighborDepthSlack where
  rotation := trace.rotates step
  depth_le := normal.rotationDepth_le step
  before_neighborRank :=
    normal.state_neighborRankBound step.castSucc
  after_neighborRank :=
    normal.state_neighborRankBound step.succ

/--
The rank-update API turns the contextual rotation into an exact pointwise
unit shift.  This records the part of the rotation geometry already available
from `Rank.RotationUpdate`.
-/
theorem existsExactUnitRankUpdate
    {n depth maxRotationDepth neighborRankBound : ℕ}
    {splayTree beforeComparison afterComparison : BST 0 n}
    (context :
      BoundedComparisonRotation
        (depth := depth)
        splayTree beforeComparison afterComparison
        maxRotationDepth neighborRankBound) :
    ∃ shiftAt : ℕ → ℤ,
      ExactTreeRankUpdate
          beforeComparison afterComparison shiftAt ∧
        IsUnitRotationShift shiftAt :=
  context.rotation.existsExactTreeRankUpdate

/--
At most `budget` nodes of the fixed splay tree change their canonical
outgoing heavy branch.  Keeping this named proposition remains useful for
explicit finite budgets; `ComparisonRotationJunctionBound.junctionBound_one`
discharges it uniformly with `budget = 1`.
-/
def JunctionBound
    {n depth maxRotationDepth neighborRankBound : ℕ}
    {splayTree beforeComparison afterComparison : BST 0 n}
    (_context :
      BoundedComparisonRotation
        (depth := depth)
        splayTree beforeComparison afterComparison
        maxRotationDepth neighborRankBound)
    (budget : ℕ) : Prop :=
  junctionCount
      (Snapshot.ofTree beforeComparison)
      (Snapshot.ofTree afterComparison)
      splayTree ≤ budget

/--
The concrete bend action induced by a bounded comparison-tree rotation while
the splay-tree shape stays fixed.
-/
noncomputable def bendAction
    {n depth maxRotationDepth neighborRankBound : ℕ}
    {splayTree beforeComparison afterComparison : BST 0 n}
    (_context :
      BoundedComparisonRotation
        (depth := depth)
        splayTree beforeComparison afterComparison
        maxRotationDepth neighborRankBound) :
    BendAction :=
  BendAction.between .comparisonRotation 0 0
    (bends (Snapshot.ofTree beforeComparison) splayTree)
    (bends (Snapshot.ofTree afterComparison) splayTree)

/-- The comparison-rotation action has its exact singleton finite history. -/
theorem bendAction_history
    {n depth maxRotationDepth neighborRankBound : ℕ}
    {splayTree beforeComparison afterComparison : BST 0 n}
    (context :
      BoundedComparisonRotation
        (depth := depth)
        splayTree beforeComparison afterComparison
        maxRotationDepth neighborRankBound) :
    FiniteBendHistory n
      (bends (Snapshot.ofTree beforeComparison) splayTree)
      [context.bendAction]
      (bends (Snapshot.ofTree afterComparison) splayTree) := by
  simpa only [bendAction] using
    (FiniteBendHistory.cons
      (n := n)
      (before :=
        bends (Snapshot.ofTree beforeComparison) splayTree)
      .comparisonRotation 0 0
      (FiniteBendHistory.nil
        (bends (Snapshot.ofTree afterComparison) splayTree)))

/--
A verified junction budget gives the explicit comparison-rotation creation
bound `3 * budget`.
-/
theorem created_le_three_mul_of_junctionBound
    {n depth maxRotationDepth neighborRankBound budget : ℕ}
    {splayTree beforeComparison afterComparison : BST 0 n}
    (context :
      BoundedComparisonRotation
        (depth := depth)
        splayTree beforeComparison afterComparison
        maxRotationDepth neighborRankBound)
    (bound : context.JunctionBound budget) :
    ((bends (Snapshot.ofTree afterComparison) splayTree) \
      (bends (Snapshot.ofTree beforeComparison) splayTree)).card ≤
        3 * budget := by
  exact
    (created_le_three_mul_junctionCount
      (Snapshot.ofTree beforeComparison)
      (Snapshot.ofTree afterComparison)
      splayTree).trans
        (Nat.mul_le_mul_left 3 bound)

/--
The exact local-soundness bridge consumed by the global bend telescope.
-/
theorem bendAction_locallySound_of_junctionBound
    {n depth maxRotationDepth neighborRankBound budget : ℕ}
    {splayTree beforeComparison afterComparison : BST 0 n}
    (context :
      BoundedComparisonRotation
        (depth := depth)
        splayTree beforeComparison afterComparison
        maxRotationDepth neighborRankBound)
    (constants : BendConstants)
    (bound : context.JunctionBound budget)
    (allowance : 3 * budget ≤ constants.comparisonRotation) :
    context.bendAction.LocallySound constants := by
  change
    0 = 0 ∧ 0 = 0 ∧
      ((bends (Snapshot.ofTree afterComparison) splayTree) \
        (bends (Snapshot.ofTree beforeComparison) splayTree)).card ≤
          constants.comparisonRotation
  exact
    ⟨rfl, rfl,
      (context.created_le_three_mul_of_junctionBound bound).trans
        allowance⟩

/--
Package one bounded rotation, a junction budget, and a comparison allowance
as the finite local step expected by the global accounting layer.
-/
noncomputable def finiteBendStep_of_junctionBound
    {n depth maxRotationDepth neighborRankBound budget : ℕ}
    {splayTree beforeComparison afterComparison : BST 0 n}
    (context :
      BoundedComparisonRotation
        (depth := depth)
        splayTree beforeComparison afterComparison
        maxRotationDepth neighborRankBound)
    (constants : BendConstants)
    (bound : context.JunctionBound budget)
    (allowance : 3 * budget ≤ constants.comparisonRotation) :
    LocalFiniteBendStep constants n where
  beforeBends :=
    bends (Snapshot.ofTree beforeComparison) splayTree
  afterBends :=
    bends (Snapshot.ofTree afterComparison) splayTree
  action := context.bendAction
  history := context.bendAction_history
  locallySound :=
    context.bendAction_locallySound_of_junctionBound
      constants bound allowance

end BoundedComparisonRotation

/--
The recursive junction count is at most the number of internal nodes of the
fixed splay tree.
-/
theorem junctionCountFrom_le_size
    {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) :
    junctionCountFrom before after tree upper_le_n ≤ tree.size := by
  induction tree with
  | empty boundary =>
      simp [junctionCountFrom, BST.size]
  | @node lower root upper left right ihLeft ihRight =>
      have left_le_n : root ≤ n := by
        have hRight := right.lower_le_upper
        omega
      have leftBound := ihLeft left_le_n
      have rightBound := ihRight upper_le_n
      simp only [junctionCountFrom, BST.size]
      split <;> omega

/-- Complete-tree form of `junctionCountFrom_le_size`. -/
theorem junctionCount_le_n
    {n : ℕ} (before after : Snapshot n) (tree : BST 0 n) :
    junctionCount before after tree ≤ n := by
  calc
    junctionCount before after tree =
        junctionCountFrom before after tree (Nat.le_refl n) := rfl
    _ ≤ tree.size :=
      junctionCountFrom_le_size before after tree (Nat.le_refl n)
    _ = n := tree.size_eq_upper

/--
Unconditional finite-size fallback: one comparison rotation creates at most
`3 * n` bends.  This is explicit and useful for finite instances, but it is
not a uniform comparison-rotation constant as `n` varies.
-/
theorem BoundedComparisonRotation.created_le_three_mul_n
    {n depth maxRotationDepth neighborRankBound : ℕ}
    {splayTree beforeComparison afterComparison : BST 0 n}
    (context :
      BoundedComparisonRotation
        (depth := depth)
        splayTree beforeComparison afterComparison
        maxRotationDepth neighborRankBound) :
    ((bends (Snapshot.ofTree afterComparison) splayTree) \
      (bends (Snapshot.ofTree beforeComparison) splayTree)).card ≤
        3 * n := by
  exact
    context.created_le_three_mul_of_junctionBound
      (junctionCount_le_n
        (Snapshot.ofTree beforeComparison)
        (Snapshot.ofTree afterComparison) splayTree)

/-- The finite-size junction budget, exposed in the residual-premise API. -/
theorem BoundedComparisonRotation.junctionBound_n
    {n depth maxRotationDepth neighborRankBound : ℕ}
    {splayTree beforeComparison afterComparison : BST 0 n}
    (context :
      BoundedComparisonRotation
        (depth := depth)
        splayTree beforeComparison afterComparison
        maxRotationDepth neighborRankBound) :
    context.JunctionBound n :=
  junctionCount_le_n
    (Snapshot.ofTree beforeComparison)
    (Snapshot.ofTree afterComparison) splayTree

/--
The unconditional finite-size action is locally sound whenever the supplied
comparison-rotation allowance explicitly dominates `3 * n`.
-/
theorem BoundedComparisonRotation.bendAction_locallySound_of_three_mul_n_le
    {n depth maxRotationDepth neighborRankBound : ℕ}
    {splayTree beforeComparison afterComparison : BST 0 n}
    (context :
      BoundedComparisonRotation
        (depth := depth)
        splayTree beforeComparison afterComparison
        maxRotationDepth neighborRankBound)
    (constants : BendConstants)
    (allowance : 3 * n ≤ constants.comparisonRotation) :
    context.bendAction.LocallySound constants :=
  context.bendAction_locallySound_of_junctionBound
    constants context.junctionBound_n allowance

/--
Finite local-step packaging for the explicit `3 * n` fallback.  Its
allowance depends on the key-universe size, so this theorem does not assert a
uniform `BendConstants` across different `n`.
-/
noncomputable def BoundedComparisonRotation.finiteBendStep_of_three_mul_n_le
    {n depth maxRotationDepth neighborRankBound : ℕ}
    {splayTree beforeComparison afterComparison : BST 0 n}
    (context :
      BoundedComparisonRotation
        (depth := depth)
        splayTree beforeComparison afterComparison
        maxRotationDepth neighborRankBound)
    (constants : BendConstants)
    (allowance : 3 * n ≤ constants.comparisonRotation) :
    LocalFiniteBendStep constants n :=
  context.finiteBendStep_of_junctionBound
    constants context.junctionBound_n allowance

/--
Every structurally normal trace rotation therefore has the checked finite-size
fallback bound.  The sharper module `ComparisonRotationJunctionBound` proves
the uniform bound `created ≤ 3`; this theorem is retained as a standalone
finite-universe fallback.
-/
theorem structuralTraceRotation_created_le_three_mul_n
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    (normal : IsStructurallyNormal bounds trace)
    (splayTree : BST 0 n) (step : Fin trace.rotationCount) :
    ((bends
        (Snapshot.ofTree (trace.state step.succ)) splayTree) \
      (bends
        (Snapshot.ofTree (trace.state step.castSucc)) splayTree)).card ≤
          3 * n := by
  exact
    (BoundedComparisonRotation.ofTrace normal splayTree step).created_le_three_mul_n

end Splay.Accounting.ComparisonRotationBendGeometry
