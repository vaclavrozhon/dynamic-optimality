import Splay.Assumptions.NormalForm
import Splay.Lazy.SplayTrace

namespace Splay.Assumptions.NormalForm.ComparisonTrace

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

/-- The comparison tree before the first rotation. -/
def initialTree {n : ℕ} {accesses : List (Fin n)}
    (trace : ComparisonTrace n accesses) : ComparisonTree n :=
  trace.state 0

/-- The comparison tree after the final rotation. -/
def finalTree {n : ℕ} {accesses : List (Fin n)}
    (trace : ComparisonTrace n accesses) : ComparisonTree n :=
  trace.state (Fin.last trace.rotationCount)

private theorem chain_toRotationExecution
    {n count : ℕ}
    (state : Fin (count + 1) → ComparisonTree n)
    (rotationDepth : Fin count → ℕ)
    (rotates :
      ∀ step : Fin count,
        RotationAt (rotationDepth step)
          (state step.castSucc) (state step.succ)) :
    RotationExecution count (state 0) (state (Fin.last count)) := by
  induction count with
  | zero =>
      have indicesEqual :
          (0 : Fin (0 + 1)) = Fin.last 0 :=
        Fin.ext (by rfl)
      rw [indicesEqual]
      exact .refl
  | succ count ih =>
      let tailState : Fin (count + 1) → ComparisonTree n :=
        fun time => state time.succ
      let tailDepth : Fin count → ℕ :=
        fun step => rotationDepth step.succ
      have tailRotates :
          ∀ step : Fin count,
            RotationAt (tailDepth step)
              (tailState step.castSucc) (tailState step.succ) := by
        intro step
        simpa [tailState, tailDepth] using rotates step.succ
      have tailExecution :
          RotationExecution count
            (tailState 0) (tailState (Fin.last count)) :=
        ih tailState tailDepth tailRotates
      have head :=
        rotates (0 : Fin count.succ)
      simpa [tailState] using
        (RotationExecution.step head tailExecution)

/--
The contiguous portion of an indexed rotation chain beginning at `start` and
containing exactly `steps` rotations.
-/
private theorem chain_segment_toRotationExecution
    {n count : ℕ}
    (state : Fin (count + 1) → ComparisonTree n)
    (rotationDepth : Fin count → ℕ)
    (rotates :
      ∀ step : Fin count,
        RotationAt (rotationDepth step)
          (state step.castSucc) (state step.succ))
    (start steps : ℕ) (within : start + steps ≤ count) :
    RotationExecution steps
      (state ⟨start, by omega⟩)
      (state ⟨start + steps, by omega⟩) := by
  induction steps generalizing start with
  | zero =>
      exact .refl
  | succ steps ih =>
      have start_lt : start < count := by omega
      let first : Fin count := ⟨start, start_lt⟩
      have head := rotates first
      have tail :
          RotationExecution steps
            (state ⟨start + 1, by omega⟩)
            (state ⟨(start + 1) + steps, by omega⟩) :=
        ih (start + 1) (by omega)
      simpa [first, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (RotationExecution.step head tail)

/--
The indexed normal-form trace flattens to the same number of ordinary
rotations, with exactly its first and final comparison trees as endpoints.
-/
theorem toRotationExecution
    {n : ℕ} {accesses : List (Fin n)}
    (trace : ComparisonTrace n accesses) :
    RotationExecution trace.rotationCount
      trace.initialTree trace.finalTree := by
  exact
    chain_toRotationExecution
      trace.state trace.rotationDepth trace.rotates

/--
Any monotone pair of time indices cuts out the exact intervening rotation
segment.  This is the scheduling bridge used to interleave requests with the
comparison trace.
-/
theorem toRotationExecution_between
    {n : ℕ} {accesses : List (Fin n)}
    (trace : ComparisonTrace n accesses)
    (start finish : Fin (trace.rotationCount + 1))
    (ordered : start ≤ finish) :
    RotationExecution (finish.val - start.val)
      (trace.state start) (trace.state finish) := by
  have finish_le : finish.val ≤ trace.rotationCount := by
    omega
  have within :
      start.val + (finish.val - start.val) ≤ trace.rotationCount := by
    omega
  have segment :=
    chain_segment_toRotationExecution
      trace.state trace.rotationDepth trace.rotates
      start.val (finish.val - start.val) within
  have end_eq :
      start.val + (finish.val - start.val) = finish.val := by
    omega
  convert segment using 1
  apply congrArg trace.state
  apply Fin.ext
  exact end_eq.symm

/--
Consequently, a local comparison-tree rotation realizer composes through an
entire normal-form comparison trace while the represented splay-tree shape
stays fixed.
-/
theorem existsRepresentedTransition
    {params : Interface.Parameters}
    {n : ℕ} {accesses : List (Fin n)}
    {splayTree : Tree.BST 0 n}
    (realizer : ComparisonRotationTraceRealizer params splayTree)
    (trace : ComparisonTrace n accesses)
    {initial : State n}
    (initialRepresents :
      initial.Represents params
        (Snapshot.ofTree trace.initialTree) splayTree) :
    Nonempty
      (RepresentedTransition params
        (Snapshot.ofTree trace.initialTree) splayTree
        (Snapshot.ofTree trace.finalTree) splayTree initial) :=
  trace.toRotationExecution.existsRepresentedComparisonTransition
    realizer initialRepresents

end Splay.Assumptions.NormalForm.ComparisonTrace
