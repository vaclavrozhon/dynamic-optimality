import MultiSplay.ForestPotential
import Splay.Accounting.OfflineHeavyBoundedSteps

/-!
# Root operations with persistent heavy representations

`Component` retains the original tree, its actual representation, and the
history-dependent representation witness. The root-operation certificates below
are constructed from the existing splay proofs for arbitrary current witnesses;
they are not assumptions about an unspecified normalization algorithm.

The charged work is the support-and-rotation budget of `HasSupportedPath`.
Converting this work to pointer operations is a separate execution bridge.
-/

namespace MultiSplay.Heavy

open Splay.Tree
open Splay.Accounting.OfflineConnectedSupport (HeavyRepresentation HasSupportedPath heavyUnitCost)

structure Component (capacity : Nat) where
  lower : Nat
  upper : Nat
  source : BST lower upper
  actual : BST lower upper
  representation : HeavyRepresentation capacity source actual
  fits : source.size ≤ capacity

def Component.ofRepresentation {capacity lower upper : Nat}
    {source actual : BST lower upper}
    (representation : HeavyRepresentation capacity source actual)
    (fits : source.size ≤ capacity) : Component capacity :=
  ⟨lower, upper, source, actual, representation, fits⟩

def Component.potential {capacity : Nat} (component : Component capacity) : Nat :=
  component.representation.potential

def Component.size {capacity : Nat} (component : Component capacity) : Nat :=
  component.source.size

theorem Component.potential_le_size {capacity : Nat} (component : Component capacity) :
    component.potential ≤ 64 * component.size :=
  component.representation.potential_le_size

theorem Component.height_le {capacity : Nat} (component : Component capacity) :
    component.actual.height ≤ 6 * (Nat.clog 2 (capacity + 1)) ^ 2 :=
  component.representation.height_le_capacity component.fits

/-- A raw root join consumes these very two child representations. The new
representation is reached from the raw joined tree by a supported path. -/
structure JoinResult {capacity lower pivot upper : Nat}
    {left actualLeft : BST lower pivot} {right actualRight : BST (pivot + 1) upper}
    (leftRep : HeavyRepresentation capacity left actualLeft)
    (rightRep : HeavyRepresentation capacity right actualRight) where
  actual : BST lower upper
  representation : HeavyRepresentation capacity (.node left right) actual
  work : Nat
  path : HasSupportedPath (.node actualLeft actualRight) actual work work
  work_le : work ≤ heavyUnitCost capacity
  amortized : work + representation.potential ≤ leftRep.potential + rightRep.potential + 115

theorem exists_join {capacity lower pivot upper : Nat}
    {left actualLeft : BST lower pivot} {right actualRight : BST (pivot + 1) upper}
    (leftRep : HeavyRepresentation capacity left actualLeft)
    (rightRep : HeavyRepresentation capacity right actualRight)
    (fits : (BST.node left right).size ≤ capacity) :
    Nonempty (JoinResult leftRep rightRep) := by
  obtain ⟨actual, representation, work, path, work_le, amortized⟩ :=
    leftRep.exists_join rightRep fits
  exact ⟨⟨actual, representation, work, path, work_le, amortized⟩⟩

/-- Splitting exposes the source pivot and returns its actual child histories.
It does not select new representations of the source children. -/
structure SplitResult {capacity lower pivot upper : Nat}
    {left : BST lower pivot} {right : BST (pivot + 1) upper} {actual : BST lower upper}
    (representation : HeavyRepresentation capacity (.node left right) actual) where
  actualLeft : BST lower pivot
  actualRight : BST (pivot + 1) upper
  leftRep : HeavyRepresentation capacity left actualLeft
  rightRep : HeavyRepresentation capacity right actualRight
  work : Nat
  path : HasSupportedPath actual (.node actualLeft actualRight) work work
  work_le : work ≤ heavyUnitCost capacity
  amortized : work + leftRep.potential + rightRep.potential ≤ representation.potential + 115

theorem exists_split {capacity lower pivot upper : Nat}
    {left : BST lower pivot} {right : BST (pivot + 1) upper} {actual : BST lower upper}
    (representation : HeavyRepresentation capacity (.node left right) actual) :
    Nonempty (SplitResult representation) := by
  obtain ⟨actualLeft, actualRight, leftRep, rightRep, work, path, work_le, amortized⟩ :=
    representation.exists_split_node
  exact ⟨⟨actualLeft, actualRight, leftRep, rightRep, work, path, work_le, by omega⟩⟩

/-- A comparator rotation is implemented without changing the represented
alphabet. Its allowance is proportional to its depth in the source component. -/
structure RotationResult {capacity lower upper depth : Nat}
    {source target actual : BST lower upper}
    (rotation : BST.RotationAt depth source target)
    (representation : HeavyRepresentation capacity source actual) where
  final : BST lower upper
  finalRep : HeavyRepresentation capacity target final
  work : Nat
  path : HasSupportedPath actual final work work
  work_le : work ≤ (4 * heavyUnitCost capacity + 4) * (depth + 1)
  amortized : work + finalRep.potential ≤ representation.potential + 464 * (depth + 1)

theorem exists_rotation {capacity lower upper depth : Nat}
    {source target actual : BST lower upper}
    (rotation : BST.RotationAt depth source target)
    (representation : HeavyRepresentation capacity source actual)
    (fits : source.size ≤ capacity) :
    Nonempty (RotationResult rotation representation) := by
  obtain ⟨final, finalRep, work, path, work_le, amortized⟩ :=
    representation.exists_rotation rotation fits
  exact ⟨⟨final, finalRep, work, path, work_le, amortized⟩⟩

/-- The local operations include one unit for the raw insertion or deletion.
The certificates are supplied by the unconditional existence theorems above. -/
inductive Edit (capacity : Nat) :
    List (Component capacity) → List (Component capacity) → Nat → Nat → Prop
  | join {lower pivot upper : Nat}
      {left actualLeft : BST lower pivot} {right actualRight : BST (pivot + 1) upper}
      {leftRep : HeavyRepresentation capacity left actualLeft}
      {rightRep : HeavyRepresentation capacity right actualRight}
      (leftFits : left.size ≤ capacity) (rightFits : right.size ≤ capacity)
      (fits : (BST.node left right).size ≤ capacity) (result : JoinResult leftRep rightRep) :
      Edit capacity
        [Component.ofRepresentation leftRep leftFits, Component.ofRepresentation rightRep rightFits]
        [Component.ofRepresentation result.representation fits] (result.work + 1) 116
  | split {lower pivot upper : Nat}
      {left : BST lower pivot} {right : BST (pivot + 1) upper} {actual : BST lower upper}
      {representation : HeavyRepresentation capacity (.node left right) actual}
      (fits : (BST.node left right).size ≤ capacity)
      (leftFits : left.size ≤ capacity) (rightFits : right.size ≤ capacity)
      (result : SplitResult representation) :
      Edit capacity [Component.ofRepresentation representation fits]
        [Component.ofRepresentation result.leftRep leftFits,
         Component.ofRepresentation result.rightRep rightFits] (result.work + 1) 116
  | rotate {lower upper depth : Nat} {source target actual : BST lower upper}
      {rotation : BST.RotationAt depth source target}
      {representation : HeavyRepresentation capacity source actual}
      (fits : source.size ≤ capacity) (targetFits : target.size ≤ capacity)
      (result : RotationResult rotation representation) :
      Edit capacity [Component.ofRepresentation representation fits]
        [Component.ofRepresentation result.finalRep targetFits] result.work (464 * (depth + 1))

theorem edit_amortized (capacity : Nat) : Forest.LocallyAmortized Component.potential (Edit capacity) := by
  intro a b cost allowance edit
  cases edit with
  | join leftFits rightFits fits result =>
      have h := result.amortized
      simp only [Forest.potential_cons, Forest.potential_nil,
        Component.ofRepresentation, Component.potential]
      omega
  | split fits leftFits rightFits result =>
      have h := result.amortized
      simp only [Forest.potential_cons, Forest.potential_nil,
        Component.ofRepresentation, Component.potential]
      omega
  | rotate fits targetFits result =>
      simpa [Forest.potential, Component.ofRepresentation, Component.potential] using result.amortized

/-- Any finite interleaving of actual root operations and rotation simulations
has one global initialization charge, even when components are repeatedly joined. -/
theorem forest_work_bound {capacity : Nat} {initial final : List (Component capacity)}
    {work allowance : Nat} (trace : Forest.Trace (Edit capacity) initial final work allowance) :
    work ≤ 64 * Forest.potential Component.size initial + allowance :=
  trace.cost_le_initial_size (edit_amortized capacity) Component.potential_le_size

end MultiSplay.Heavy
