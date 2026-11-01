import MultiSplay.ForestPotential
import Splay.Accounting.OfflineRibRotation

/-!
# Persistent root operations for the rib representation

A rib is a maximal one-direction chain in the comparison-tree representation.
The existing splay normalizer replaces these chains by bounded representations.
The `side` field specifies the orientation required at a component boundary.

The join theorem below accepts arbitrary orientations. It explicitly pays for
reorienting both children before the common raw join. Each child retains the
representation history returned by that operation.
-/

namespace MultiSplay.Rib

open Splay.Tree
open Splay.Accounting.OfflineConnectedSupport (RibRepresentation HasSupportedPath ribUnitCost)

structure Component (capacity : Nat) where
  lower : Nat
  upper : Nat
  side : Bool
  source : BST lower upper
  actual : BST lower upper
  representation : RibRepresentation capacity side source actual
  fits : source.size ≤ capacity

def Component.ofRepresentation {capacity lower upper : Nat} {side : Bool}
    {source actual : BST lower upper}
    (representation : RibRepresentation capacity side source actual)
    (fits : source.size ≤ capacity) : Component capacity :=
  ⟨lower, upper, side, source, actual, representation, fits⟩

def Component.potential {capacity : Nat} (component : Component capacity) : Nat :=
  component.representation.potential

def Component.size {capacity : Nat} (component : Component capacity) : Nat :=
  component.source.size

theorem Component.potential_le_size {capacity : Nat} (component : Component capacity) :
    component.potential ≤ 256 * component.size :=
  component.representation.potential_le_size

theorem Component.height_le {capacity : Nat} (component : Component capacity) :
    component.actual.height ≤ component.source.height * (5 * Nat.clog 2 (capacity + 1)) :=
  component.representation.height_le component.fits

structure JoinResult {capacity lower pivot upper : Nat} {leftSide rightSide : Bool}
    {left actualLeft : BST lower pivot} {right actualRight : BST (pivot + 1) upper}
    (leftRep : RibRepresentation capacity leftSide left actualLeft)
    (rightRep : RibRepresentation capacity rightSide right actualRight) (side : Bool) where
  preparedLeft : BST lower pivot
  preparedRight : BST (pivot + 1) upper
  preparedLeftRep : RibRepresentation capacity true left preparedLeft
  preparedRightRep : RibRepresentation capacity false right preparedRight
  leftWork : Nat
  rightWork : Nat
  leftPath : HasSupportedPath actualLeft preparedLeft leftWork leftWork
  rightPath : HasSupportedPath actualRight preparedRight rightWork rightWork
  actual : BST lower upper
  representation : RibRepresentation capacity side (.node left right) actual
  joinWork : Nat
  joinPath : HasSupportedPath (.node preparedLeft preparedRight) actual joinWork joinWork
  work_le : leftWork + rightWork + joinWork ≤ 5 * ribUnitCost capacity
  amortized : leftWork + rightWork + joinWork + representation.potential ≤
    leftRep.potential + rightRep.potential + 2240

theorem exists_join {capacity lower pivot upper : Nat} {leftSide rightSide : Bool}
    {left actualLeft : BST lower pivot} {right actualRight : BST (pivot + 1) upper}
    (leftRep : RibRepresentation capacity leftSide left actualLeft)
    (rightRep : RibRepresentation capacity rightSide right actualRight) (side : Bool)
    (fits : (BST.node left right).size ≤ capacity) :
    Nonempty (JoinResult leftRep rightRep side) := by
  have leftFits : left.size ≤ capacity := by simp only [BST.size] at fits; omega
  have rightFits : right.size ≤ capacity := by simp only [BST.size] at fits; omega
  obtain ⟨preparedLeft, preparedLeftRep, leftWork, leftPath, leftBound, leftAmortized⟩ :=
    leftRep.exists_reorient true leftFits
  obtain ⟨preparedRight, preparedRightRep, rightWork, rightPath, rightBound, rightAmortized⟩ :=
    rightRep.exists_reorient false rightFits
  obtain ⟨actual, representation, joinWork, joinPath, joinBound, joinAmortized⟩ :=
    RibRepresentation.exists_join side preparedLeftRep preparedRightRep fits
  exact ⟨⟨preparedLeft, preparedRight, preparedLeftRep, preparedRightRep,
    leftWork, rightWork, leftPath, rightPath, actual, representation, joinWork, joinPath,
    by omega, by omega⟩⟩

structure SplitResult {capacity lower pivot upper : Nat} {side : Bool}
    {left : BST lower pivot} {right : BST (pivot + 1) upper} {actual : BST lower upper}
    (representation : RibRepresentation capacity side (.node left right) actual) where
  actualLeft : BST lower pivot
  actualRight : BST (pivot + 1) upper
  leftRep : RibRepresentation capacity true left actualLeft
  rightRep : RibRepresentation capacity false right actualRight
  work : Nat
  path : HasSupportedPath actual (.node actualLeft actualRight) work work
  work_le : work ≤ ribUnitCost capacity
  amortized : work + leftRep.potential + rightRep.potential ≤ representation.potential + 448

theorem exists_split {capacity lower pivot upper : Nat} {side : Bool}
    {left : BST lower pivot} {right : BST (pivot + 1) upper} {actual : BST lower upper}
    (representation : RibRepresentation capacity side (.node left right) actual) :
    Nonempty (SplitResult representation) := by
  obtain ⟨actualLeft, actualRight, leftRep, rightRep, work, path, work_le, amortized⟩ :=
    representation.exists_split_node
  exact ⟨⟨actualLeft, actualRight, leftRep, rightRep, work, path, work_le, by omega⟩⟩

structure RotationResult {capacity lower upper depth : Nat} {side : Bool}
    {source target actual : BST lower upper}
    (rotation : BST.RotationAt depth source target)
    (representation : RibRepresentation capacity side source actual) where
  final : BST lower upper
  finalRep : RibRepresentation capacity side target final
  work : Nat
  path : HasSupportedPath actual final work work
  work_le : work ≤ (6 * ribUnitCost capacity + 6) * (depth + 1)
  amortized : work + finalRep.potential ≤ representation.potential + 2694 * (depth + 1)

theorem exists_rotation {capacity lower upper depth : Nat} {side : Bool}
    {source target actual : BST lower upper}
    (rotation : BST.RotationAt depth source target)
    (representation : RibRepresentation capacity side source actual)
    (fits : source.size ≤ capacity) : Nonempty (RotationResult rotation representation) := by
  obtain ⟨final, finalRep, work, path, work_le, amortized⟩ :=
    representation.exists_rotation rotation fits
  exact ⟨⟨final, finalRep, work, path, work_le, amortized⟩⟩

inductive Edit (capacity : Nat) :
    List (Component capacity) → List (Component capacity) → Nat → Nat → Prop
  | join {lower pivot upper : Nat} {leftSide rightSide side : Bool}
      {left actualLeft : BST lower pivot} {right actualRight : BST (pivot + 1) upper}
      {leftRep : RibRepresentation capacity leftSide left actualLeft}
      {rightRep : RibRepresentation capacity rightSide right actualRight}
      (leftFits : left.size ≤ capacity) (rightFits : right.size ≤ capacity)
      (fits : (BST.node left right).size ≤ capacity) (result : JoinResult leftRep rightRep side) :
      Edit capacity
        [Component.ofRepresentation leftRep leftFits, Component.ofRepresentation rightRep rightFits]
        [Component.ofRepresentation result.representation fits]
        (result.leftWork + result.rightWork + result.joinWork + 1) 2241
  | split {lower pivot upper : Nat} {side : Bool}
      {left : BST lower pivot} {right : BST (pivot + 1) upper} {actual : BST lower upper}
      {representation : RibRepresentation capacity side (.node left right) actual}
      (fits : (BST.node left right).size ≤ capacity)
      (leftFits : left.size ≤ capacity) (rightFits : right.size ≤ capacity)
      (result : SplitResult representation) :
      Edit capacity [Component.ofRepresentation representation fits]
        [Component.ofRepresentation result.leftRep leftFits,
         Component.ofRepresentation result.rightRep rightFits] (result.work + 1) 449
  | rotate {lower upper depth : Nat} {side : Bool} {source target actual : BST lower upper}
      {rotation : BST.RotationAt depth source target}
      {representation : RibRepresentation capacity side source actual}
      (fits : source.size ≤ capacity) (targetFits : target.size ≤ capacity)
      (result : RotationResult rotation representation) :
      Edit capacity [Component.ofRepresentation representation fits]
        [Component.ofRepresentation result.finalRep targetFits] result.work (2694 * (depth + 1))

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

theorem forest_work_bound {capacity : Nat} {initial final : List (Component capacity)}
    {work allowance : Nat} (trace : Forest.Trace (Edit capacity) initial final work allowance) :
    work ≤ 256 * Forest.potential Component.size initial + allowance :=
  trace.cost_le_initial_size (edit_amortized capacity) Component.potential_le_size

end MultiSplay.Rib
