import Splay.Lazy.AtomicRealizersComplete

namespace Splay.Tree.BST.RotationExecution

open Splay.Lazy
open Splay.Rank

/--
Proof-relevant decomposition of one represented transition along every
ordinary rotation of a supplied `RotationExecution`.

The transition is an index of this type.  Consequently the `step`
constructor records definitionally that its event list is the concatenation
of the transition for the first concrete rotation and the transition for the
remaining concrete rotation execution.
-/
inductive RepresentedTransitionProvenance
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n} :
    {length : ℕ} →
      {beforeTree afterTree : BST 0 n} →
      (execution :
        RotationExecution length beforeTree afterTree) →
      {initial : State n} →
      (transition :
        RepresentedTransition params
          snapshot beforeTree snapshot afterTree initial) →
      Type
  | refl
      {tree : BST 0 n} {initial : State n}
      (initialRepresents :
        initial.Represents params snapshot tree) :
      RepresentedTransitionProvenance
        (.refl : RotationExecution 0 tree tree)
        (RepresentedTransition.refl initialRepresents)
  | step
      {length rotationDepth : ℕ}
      {beforeTree middleTree afterTree : BST 0 n}
      (head : RotationAt rotationDepth beforeTree middleTree)
      (tail :
        RotationExecution length middleTree afterTree)
      {initial : State n}
      (headTransition :
        RepresentedTransition params
          snapshot beforeTree snapshot middleTree initial)
      (tailTransition :
        RepresentedTransition params
          snapshot middleTree snapshot afterTree headTransition.final)
      (tailProvenance :
        RepresentedTransitionProvenance tail tailTransition) :
      RepresentedTransitionProvenance
        (.step head tail)
        (headTransition.trans tailTransition)

namespace RepresentedTransitionProvenance

/--
Every ordinary-rotation realizer lifts to an exact transition together with
the rotation-by-rotation decomposition of that same transition.
-/
theorem exists_of_realizer
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    (realizer : SplayRotationTraceRealizer params snapshot)
    {length : ℕ} {beforeTree afterTree : BST 0 n}
    (execution : RotationExecution length beforeTree afterTree)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (Σ transition :
          RepresentedTransition params
            snapshot beforeTree snapshot afterTree initial,
        RepresentedTransitionProvenance execution transition) := by
  induction length generalizing beforeTree afterTree initial with
  | zero =>
      cases execution
      exact
        ⟨⟨RepresentedTransition.refl initialRepresents,
          .refl initialRepresents⟩⟩
  | succ length ih =>
      cases execution with
      | step head tail =>
          obtain ⟨headTransition⟩ :=
            realizer head initialRepresents
          obtain ⟨⟨tailTransition, tailProvenance⟩⟩ :=
            ih tail headTransition.final_represents
          exact
            ⟨⟨headTransition.trans tailTransition,
              .step head tail headTransition tailTransition
                tailProvenance⟩⟩

end RepresentedTransitionProvenance

/--
Proof-relevant decomposition of a comparison-tree rotation execution.  The
splay-tree shape is fixed while the represented rank snapshot changes after
every concrete comparison rotation.
-/
inductive RepresentedComparisonTransitionProvenance
    {n : ℕ} {params : Interface.Parameters}
    (splayTree : BST 0 n) :
    {length : ℕ} →
      {beforeComparison afterComparison : BST 0 n} →
      (execution :
        RotationExecution length beforeComparison afterComparison) →
      {initial : State n} →
      (transition :
        RepresentedTransition params
          (Snapshot.ofTree beforeComparison) splayTree
          (Snapshot.ofTree afterComparison) splayTree initial) →
      Type
  | refl
      (comparisonTree : BST 0 n)
      {initial : State n}
      (initialRepresents :
        initial.Represents params
          (Snapshot.ofTree comparisonTree) splayTree) :
      RepresentedComparisonTransitionProvenance splayTree
        (.refl : RotationExecution 0 comparisonTree comparisonTree)
        (RepresentedTransition.refl initialRepresents)
  | step
      {length rotationDepth : ℕ}
      {beforeComparison middleComparison afterComparison : BST 0 n}
      (head :
        RotationAt rotationDepth beforeComparison middleComparison)
      (tail :
        RotationExecution length middleComparison afterComparison)
      {initial : State n}
      (headTransition :
        RepresentedTransition params
          (Snapshot.ofTree beforeComparison) splayTree
          (Snapshot.ofTree middleComparison) splayTree initial)
      (tailTransition :
        RepresentedTransition params
          (Snapshot.ofTree middleComparison) splayTree
          (Snapshot.ofTree afterComparison) splayTree
          headTransition.final)
      (tailProvenance :
        RepresentedComparisonTransitionProvenance
          splayTree tail tailTransition) :
      RepresentedComparisonTransitionProvenance splayTree
        (.step head tail)
        (headTransition.trans tailTransition)

namespace RepresentedComparisonTransitionProvenance

/--
A one-comparison-rotation realizer lifts to an exact recursively decomposed
transition for a whole comparison rotation execution.
-/
theorem exists_of_realizer
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : BST 0 n}
    (realizer :
      ComparisonRotationTraceRealizer params splayTree)
    {length : ℕ}
    {beforeComparison afterComparison : BST 0 n}
    (execution :
      RotationExecution length beforeComparison afterComparison)
    {initial : State n}
    (initialRepresents :
      initial.Represents params
        (Snapshot.ofTree beforeComparison) splayTree) :
    Nonempty
      (Σ transition :
          RepresentedTransition params
            (Snapshot.ofTree beforeComparison) splayTree
            (Snapshot.ofTree afterComparison) splayTree initial,
        RepresentedComparisonTransitionProvenance
          splayTree execution transition) := by
  induction length generalizing
      beforeComparison afterComparison initial with
  | zero =>
      cases execution
      exact
        ⟨⟨RepresentedTransition.refl initialRepresents,
          .refl beforeComparison initialRepresents⟩⟩
  | succ length ih =>
      cases execution with
      | step head tail =>
          obtain ⟨headTransition⟩ :=
            realizer head initialRepresents
          obtain ⟨⟨tailTransition, tailProvenance⟩⟩ :=
            ih tail headTransition.final_represents
          exact
            ⟨⟨headTransition.trans tailTransition,
              .step head tail headTransition tailTransition
                tailProvenance⟩⟩

/-- Unconditional exact comparison-rotation provenance. -/
theorem exists_complete
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : BST 0 n}
    {length : ℕ}
    {beforeComparison afterComparison : BST 0 n}
    (execution :
      RotationExecution length beforeComparison afterComparison)
    {initial : State n}
    (initialRepresents :
      initial.Represents params
        (Snapshot.ofTree beforeComparison) splayTree) :
    Nonempty
      (Σ transition :
          RepresentedTransition params
            (Snapshot.ofTree beforeComparison) splayTree
            (Snapshot.ofTree afterComparison) splayTree initial,
        RepresentedComparisonTransitionProvenance
          splayTree execution transition) :=
  exists_of_realizer
    (Splay.Lazy.comparisonRotationTraceRealizer params splayTree)
    execution initialRepresents

end RepresentedComparisonTransitionProvenance

end Splay.Tree.BST.RotationExecution

namespace Splay.Tree.BST.SplayStep

open Splay.Lazy
open Splay.Rank

/--
The represented transition for one concrete bottom-up splay step, retaining
its exact one- or two-rotation implementation and the transition segment for
each ordinary rotation.
-/
structure RepresentedTransitionProvenance
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {key : ℕ} {beforeTree afterTree : BST 0 n}
    (step : SplayStep key beforeTree afterTree)
    {initial : State n}
    (transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial) : Type where
  rotationCount : ℕ
  rotationExecution :
    RotationExecution rotationCount beforeTree afterTree
  depth_eq :
    beforeTree.depth key =
      rotationCount + afterTree.depth key
  rotationProvenance :
    RotationExecution.RepresentedTransitionProvenance
      rotationExecution transition

namespace RepresentedTransitionProvenance

/--
Construct exact one-step provenance from an ordinary-rotation realizer.
-/
theorem exists_of_realizer
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    (realizer : SplayRotationTraceRealizer params snapshot)
    {key : ℕ} {beforeTree afterTree : BST 0 n}
    (step : SplayStep key beforeTree afterTree)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (Σ transition :
          RepresentedTransition params
            snapshot beforeTree snapshot afterTree initial,
        RepresentedTransitionProvenance step transition) := by
  obtain ⟨rotationCount, rotationExecution, depthEq⟩ :=
    step.toRotationExecution
  obtain ⟨⟨transition, rotationProvenance⟩⟩ :=
    RotationExecution.RepresentedTransitionProvenance.exists_of_realizer
      realizer rotationExecution initialRepresents
  exact
    ⟨⟨transition,
      { rotationCount := rotationCount
        rotationExecution := rotationExecution
        depth_eq := depthEq
        rotationProvenance := rotationProvenance }⟩⟩

end RepresentedTransitionProvenance

end Splay.Tree.BST.SplayStep

namespace Splay.Tree.BST.SplayExecution

open Splay.Lazy
open Splay.Rank

/--
Proof-relevant decomposition of a represented transition along the exact
`SplayStep`s of a supplied complete bottom-up splay execution.

Each head segment additionally retains its one- or two-ordinary-rotation
decomposition.  This closes the structural execution/transition indexing
gap: the only information still absent is the manuscript's cost-sensitive
lazy pairing implementation inside those checked segments.
-/
inductive RepresentedTransitionProvenance
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {key : ℕ} :
    {beforeTree afterTree : BST 0 n} →
      (execution : SplayExecution key beforeTree afterTree) →
      {initial : State n} →
      (transition :
        RepresentedTransition params
          snapshot beforeTree snapshot afterTree initial) →
      Type
  | done
      {tree : BST 0 n}
      (root : tree.HasRoot key)
      {initial : State n}
      (initialRepresents :
        initial.Represents params snapshot tree) :
      RepresentedTransitionProvenance
        (.done root)
        (RepresentedTransition.refl initialRepresents)
  | next
      {beforeTree middleTree afterTree : BST 0 n}
      (head : SplayStep key beforeTree middleTree)
      (tail : SplayExecution key middleTree afterTree)
      {initial : State n}
      (headTransition :
        RepresentedTransition params
          snapshot beforeTree snapshot middleTree initial)
      (tailTransition :
        RepresentedTransition params
          snapshot middleTree snapshot afterTree headTransition.final)
      (headProvenance :
        SplayStep.RepresentedTransitionProvenance
          head headTransition)
      (tailProvenance :
        RepresentedTransitionProvenance tail tailTransition) :
      RepresentedTransitionProvenance
        (.next head tail)
        (headTransition.trans tailTransition)

namespace RepresentedTransitionProvenance

/--
Every complete splay execution has a represented transition definitionally
decomposed along that same execution, assuming only the ordinary-rotation
realizer.
-/
theorem exists_of_realizer
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    (realizer : SplayRotationTraceRealizer params snapshot)
    {key : ℕ} {beforeTree afterTree : BST 0 n}
    (execution : SplayExecution key beforeTree afterTree)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (Σ transition :
          RepresentedTransition params
            snapshot beforeTree snapshot afterTree initial,
        RepresentedTransitionProvenance execution transition) := by
  induction execution generalizing initial with
  | done root =>
      exact
        ⟨⟨RepresentedTransition.refl initialRepresents,
          .done root initialRepresents⟩⟩
  | next head tail ih =>
      obtain ⟨⟨headTransition, headProvenance⟩⟩ :=
        SplayStep.RepresentedTransitionProvenance.exists_of_realizer
          realizer head initialRepresents
      obtain ⟨⟨tailTransition, tailProvenance⟩⟩ :=
        ih headTransition.final_represents
      exact
        ⟨⟨headTransition.trans tailTransition,
          .next head tail headTransition tailTransition
            headProvenance tailProvenance⟩⟩

/--
The repository's unconditional structural rotation realizer supplies exact
stepwise provenance for every complete splay.
-/
theorem exists_complete
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {key : ℕ} {beforeTree afterTree : BST 0 n}
    (execution : SplayExecution key beforeTree afterTree)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (Σ transition :
          RepresentedTransition params
            snapshot beforeTree snapshot afterTree initial,
        RepresentedTransitionProvenance execution transition) :=
  exists_of_realizer
    (Splay.Lazy.splayRotationTraceRealizer params snapshot)
    execution initialRepresents

end RepresentedTransitionProvenance

end Splay.Tree.BST.SplayExecution

namespace Splay.Tree.BST.SplaySequence

open Splay.Lazy
open Splay.Rank

/--
Exact transition provenance for a dependent sequence of complete splays.
Every request boundary and every bottom-up step inside that request is
retained as an index.
-/
inductive RepresentedTransitionProvenance
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n} :
    {accesses : List (Fin n)} →
      {beforeTree afterTree : BST 0 n} →
      (sequence : SplaySequence accesses beforeTree afterTree) →
      {initial : State n} →
      (transition :
        RepresentedTransition params
          snapshot beforeTree snapshot afterTree initial) →
      Type
  | done
      (tree : BST 0 n)
      {initial : State n}
      (initialRepresents :
        initial.Represents params snapshot tree) :
      RepresentedTransitionProvenance
        (.done tree)
        (RepresentedTransition.refl initialRepresents)
  | next
      {access : Fin n} {accesses : List (Fin n)}
      {beforeTree middleTree afterTree : BST 0 n}
      (head : SplayExecution access.val beforeTree middleTree)
      (tail : SplaySequence accesses middleTree afterTree)
      {initial : State n}
      (headTransition :
        RepresentedTransition params
          snapshot beforeTree snapshot middleTree initial)
      (tailTransition :
        RepresentedTransition params
          snapshot middleTree snapshot afterTree headTransition.final)
      (headProvenance :
        SplayExecution.RepresentedTransitionProvenance
          head headTransition)
      (tailProvenance :
        RepresentedTransitionProvenance tail tailTransition) :
      RepresentedTransitionProvenance
        (.next head tail)
        (headTransition.trans tailTransition)

namespace RepresentedTransitionProvenance

/--
Every dependent splay sequence has an exact recursively decomposed rich
transition under an ordinary-rotation realizer.
-/
theorem exists_of_realizer
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    (realizer : SplayRotationTraceRealizer params snapshot)
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    (sequence : SplaySequence accesses beforeTree afterTree)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (Σ transition :
          RepresentedTransition params
            snapshot beforeTree snapshot afterTree initial,
        RepresentedTransitionProvenance sequence transition) := by
  induction sequence generalizing initial with
  | done tree =>
      exact
        ⟨⟨RepresentedTransition.refl initialRepresents,
          .done tree initialRepresents⟩⟩
  | next head tail ih =>
      obtain ⟨⟨headTransition, headProvenance⟩⟩ :=
        SplayExecution.RepresentedTransitionProvenance.exists_of_realizer
          realizer head initialRepresents
      obtain ⟨⟨tailTransition, tailProvenance⟩⟩ :=
        ih headTransition.final_represents
      exact
        ⟨⟨headTransition.trans tailTransition,
          .next head tail headTransition tailTransition
            headProvenance tailProvenance⟩⟩

/--
Unconditional exact decomposition of a complete dependent splay sequence.
-/
theorem exists_complete
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    (sequence : SplaySequence accesses beforeTree afterTree)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (Σ transition :
          RepresentedTransition params
            snapshot beforeTree snapshot afterTree initial,
        RepresentedTransitionProvenance sequence transition) :=
  exists_of_realizer
    (Splay.Lazy.splayRotationTraceRealizer params snapshot)
    sequence initialRepresents

end RepresentedTransitionProvenance

end Splay.Tree.BST.SplaySequence
