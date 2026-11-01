import Splay.Accounting.SplayExecutionProvenance
import Splay.Lazy.ProductiveFreeRealizers

namespace Splay.Tree.BST.RotationExecution

open Splay.Lazy
open Splay.Rank

/--
Ordinary-rotation provenance together with an authenticated productive-free
transition.
-/
structure ProductiveFreeProvenance
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {length : ℕ} {beforeTree afterTree : BST 0 n}
    (execution : RotationExecution length beforeTree afterTree)
    (initial : State n) where
  realized :
    ProductiveFreeRepresentedTransition params
      snapshot beforeTree snapshot afterTree initial
  provenance :
    RepresentedTransitionProvenance execution realized.transition

namespace ProductiveFreeProvenance

/--
A productive-free one-rotation realizer composes along an exact ordinary
rotation execution while retaining the standard structural provenance.
-/
theorem exists_of_realizer
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    (realizer : ProductiveFreeSplayRotationTraceRealizer params snapshot)
    {length : ℕ} {beforeTree afterTree : BST 0 n}
    (execution : RotationExecution length beforeTree afterTree)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (ProductiveFreeProvenance
        (params := params) (snapshot := snapshot) execution initial) := by
  induction length generalizing beforeTree afterTree initial with
  | zero =>
      cases execution
      let realized :=
        ProductiveFreeRepresentedTransition.refl initialRepresents
      exact
        ⟨{
          realized := realized
          provenance := .refl initialRepresents
        }⟩
  | succ length ih =>
      cases execution with
      | step head tail =>
          obtain ⟨headRealized⟩ :=
            realizer head initialRepresents
          obtain ⟨tailRealized⟩ :=
            ih tail headRealized.transition.final_represents
          let realized := headRealized.trans tailRealized.realized
          exact
            ⟨{
              realized := realized
              provenance :=
                .step head tail
                  headRealized.transition
                  tailRealized.realized.transition
                  tailRealized.provenance
            }⟩

/-- Concrete productive-free provenance for every ordinary rotation execution. -/
theorem exists_complete
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {length : ℕ} {beforeTree afterTree : BST 0 n}
    (execution : RotationExecution length beforeTree afterTree)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (ProductiveFreeProvenance
        (params := params) (snapshot := snapshot) execution initial) :=
  exists_of_realizer
    (productiveFreeSplayRotationTraceRealizer params snapshot)
    execution initialRepresents

end ProductiveFreeProvenance

end Splay.Tree.BST.RotationExecution

namespace Splay.Tree.BST.SplayStep

open Splay.Lazy
open Splay.Rank

/-- One exact splay step with productive-free standard provenance. -/
structure ProductiveFreeProvenance
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {key : ℕ} {beforeTree afterTree : BST 0 n}
    (step : SplayStep key beforeTree afterTree)
    (initial : State n) where
  realized :
    ProductiveFreeRepresentedTransition params
      snapshot beforeTree snapshot afterTree initial
  provenance :
    RepresentedTransitionProvenance step realized.transition

namespace ProductiveFreeProvenance

theorem exists_of_realizer
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    (realizer : ProductiveFreeSplayRotationTraceRealizer params snapshot)
    {key : ℕ} {beforeTree afterTree : BST 0 n}
    (step : SplayStep key beforeTree afterTree)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (ProductiveFreeProvenance
        (params := params) (snapshot := snapshot) step initial) := by
  obtain ⟨rotationCount, rotationExecution, depthEq⟩ :=
    step.toRotationExecution
  obtain ⟨rotationRealized⟩ :=
    RotationExecution.ProductiveFreeProvenance.exists_of_realizer
      realizer rotationExecution initialRepresents
  exact
    ⟨{
      realized := rotationRealized.realized
      provenance :=
        { rotationCount := rotationCount
          rotationExecution := rotationExecution
          depth_eq := depthEq
          rotationProvenance := rotationRealized.provenance }
    }⟩

end ProductiveFreeProvenance

end Splay.Tree.BST.SplayStep

namespace Splay.Tree.BST.SplayExecution

open Splay.Lazy
open Splay.Rank

/-- A complete bottom-up splay with productive-free standard provenance. -/
structure ProductiveFreeProvenance
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {key : ℕ} {beforeTree afterTree : BST 0 n}
    (execution : SplayExecution key beforeTree afterTree)
    (initial : State n) where
  realized :
    ProductiveFreeRepresentedTransition params
      snapshot beforeTree snapshot afterTree initial
  provenance :
    RepresentedTransitionProvenance execution realized.transition

namespace ProductiveFreeProvenance

theorem exists_of_realizer
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    (realizer : ProductiveFreeSplayRotationTraceRealizer params snapshot)
    {key : ℕ} {beforeTree afterTree : BST 0 n}
    (execution : SplayExecution key beforeTree afterTree)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (ProductiveFreeProvenance
        (params := params) (snapshot := snapshot) execution initial) := by
  induction execution generalizing initial with
  | done root =>
      let realized :=
        ProductiveFreeRepresentedTransition.refl initialRepresents
      exact
        ⟨{
          realized := realized
          provenance := .done root initialRepresents
        }⟩
  | next head tail ih =>
      obtain ⟨headRealized⟩ :=
        SplayStep.ProductiveFreeProvenance.exists_of_realizer
          realizer head initialRepresents
      obtain ⟨tailRealized⟩ :=
        ih headRealized.realized.transition.final_represents
      let realized :=
        headRealized.realized.trans tailRealized.realized
      exact
        ⟨{
          realized := realized
          provenance :=
            .next head tail
              headRealized.realized.transition
              tailRealized.realized.transition
              headRealized.provenance tailRealized.provenance
        }⟩

end ProductiveFreeProvenance

end Splay.Tree.BST.SplayExecution

namespace Splay.Tree.BST.SplaySequence

open Splay.Lazy
open Splay.Rank

/-- A request sequence with productive-free standard provenance. -/
structure ProductiveFreeProvenance
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    (sequence : SplaySequence accesses beforeTree afterTree)
    (initial : State n) where
  realized :
    ProductiveFreeRepresentedTransition params
      snapshot beforeTree snapshot afterTree initial
  provenance :
    RepresentedTransitionProvenance sequence realized.transition

namespace ProductiveFreeProvenance

theorem exists_of_realizer
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    (realizer : ProductiveFreeSplayRotationTraceRealizer params snapshot)
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    (sequence : SplaySequence accesses beforeTree afterTree)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (ProductiveFreeProvenance
        (params := params) (snapshot := snapshot) sequence initial) := by
  induction sequence generalizing initial with
  | done tree =>
      let realized :=
        ProductiveFreeRepresentedTransition.refl initialRepresents
      exact
        ⟨{
          realized := realized
          provenance := .done tree initialRepresents
        }⟩
  | next head tail ih =>
      obtain ⟨headRealized⟩ :=
        SplayExecution.ProductiveFreeProvenance.exists_of_realizer
          realizer head initialRepresents
      obtain ⟨tailRealized⟩ :=
        ih headRealized.realized.transition.final_represents
      let realized :=
        headRealized.realized.trans tailRealized.realized
      exact
        ⟨{
          realized := realized
          provenance :=
            .next head tail
              headRealized.realized.transition
              tailRealized.realized.transition
              headRealized.provenance tailRealized.provenance
        }⟩

/-- Concrete productive-free provenance for every complete splay sequence. -/
theorem exists_complete
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    (sequence : SplaySequence accesses beforeTree afterTree)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (ProductiveFreeProvenance
        (params := params) (snapshot := snapshot) sequence initial) :=
  exists_of_realizer
    (productiveFreeSplayRotationTraceRealizer params snapshot)
    sequence initialRepresents

end ProductiveFreeProvenance

end Splay.Tree.BST.SplaySequence
