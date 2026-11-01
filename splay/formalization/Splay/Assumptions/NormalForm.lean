import Splay.Statement
import Splay.Tree.SplayStep

namespace Splay.Assumptions.NormalForm

/-- A comparison-tree state on the fixed key set `Fin n`. -/
abbrev ComparisonTree (n : ℕ) :=
  Tree.BST 0 n

/--
A comparison-tree execution serving `accesses`.

There is one more state than rotation. Consecutive states are related by an
actual `RotationAt`, so neither the transition relation nor its depth is an
unconstrained cost annotation. Requests are assigned, in order, to states in
which their key is at the root.

`servedAt` is only monotone, rather than strictly monotone. Thus repeated
requests to the current root and the one-key case need no artificial rotation.
-/
structure ComparisonTrace (n : ℕ) (accesses : List (Fin n)) where
  /-- Number of rotations in the execution. -/
  rotationCount : ℕ
  /-- Tree before the first rotation and after each successive rotation. -/
  state : Fin (rotationCount + 1) → ComparisonTree n
  /-- Depth of the shallower endpoint of each rotated edge. -/
  rotationDepth : Fin rotationCount → ℕ
  /-- Every adjacent pair of states differs by the recorded rotation. -/
  rotates :
    ∀ step : Fin rotationCount,
      Tree.BST.RotationAt (rotationDepth step)
        (state step.castSucc) (state step.succ)
  /-- State at which each request is served. -/
  servedAt : Fin accesses.length → Fin (rotationCount + 1)
  /-- Requests occur in their list order, possibly at the same state. -/
  servedInOrder : Monotone servedAt
  /-- A request is served only while its key is at the root. -/
  serves :
    ∀ request : Fin accesses.length,
      (state (servedAt request)).HasRoot (accesses.get request).val

namespace ComparisonTrace

/--
Concrete cost charged to the normal-form trace: one unit per request and one
per rotation. Bounded rotation depth later makes this equivalent up to a
constant to the usual local-touch accounting.
-/
def cost {n : ℕ} {accesses : List (Fin n)}
    (trace : ComparisonTrace n accesses) : ℕ :=
  accesses.length + trace.rotationCount

end ComparisonTrace

/-- Universal finite constants promised by one normal-form transformation. -/
structure Bounds where
  /-- Multiplicative constant in the logarithmic height bound. -/
  heightMultiplier : ℕ
  /-- Uniform maximum depth of every rotation. -/
  maxRotationDepth : ℕ
  /-- Multiplicative overhead relative to the comparison optimum. -/
  costMultiplier : ℕ
  heightMultiplier_pos : 0 < heightMultiplier
  costMultiplier_pos : 0 < costMultiplier

/--
The structural part of normal form for one trace.

The stabilized logarithm is positive even for `n = 1`, avoiding a special
small-tree convention in the height bound.
-/
structure IsNormal {n : ℕ} {accesses : List (Fin n)}
    (bounds : Bounds) (trace : ComparisonTrace n accesses) : Prop where
  height_le :
    ∀ time,
      (trace.state time).height ≤
        bounds.heightMultiplier * Analysis.stabilizedLog n
  rotationDepth_le :
    ∀ step,
      trace.rotationDepth step ≤ bounds.maxRotationDepth

/--
Explicit hypothesis corresponding to the normal-form theorem used by the
paper.

It asks for one set of universal constants and, for every nonempty key
universe and access sequence, a concrete comparison-tree trace which

* serves the requests at the root in order,
* consists solely of bounded-depth rotations,
* maintains logarithmic height at every intermediate state, and
* has concrete trace cost within a constant factor of `model.optCost`.

This definition asserts neither that the hypothesis holds nor any
competitiveness conclusion; later developments must receive a proof of
`Hypothesis model` explicitly.
-/
def Hypothesis (model : CostModel) : Prop :=
  ∃ bounds : Bounds,
    ∀ (n : ℕ), 0 < n →
      ∀ accesses : List (Fin n),
        ∃ trace : ComparisonTrace n accesses,
          IsNormal bounds trace ∧
            trace.cost ≤ bounds.costMultiplier * model.optCost accesses

end Splay.Assumptions.NormalForm
