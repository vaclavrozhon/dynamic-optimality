import Splay.Accounting.NormalFormBendHistory

namespace Splay.Accounting.NormalFormBendHistory.ComparisonExecutionCertificate

open Splay.Tree
open Splay.Tree.BST
open Splay.Assumptions.NormalForm
open Splay.Assumptions.NormalForm.ComparisonTrace
open Splay.Accounting.ComparisonRotationBendGeometry

/--
A comparison-trace segment together with its automatically generated bend
certificate.  Keeping the execution proof and its certificate in one
dependent pair makes endpoint transports coherent.
-/
private abbrev CertifiedSegment
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    (splayTree : BST 0 n)
    (start steps : ℕ)
    (within : start + steps ≤ trace.rotationCount) :=
  PSigma fun execution :
    RotationExecution steps
      (trace.state ⟨start, by omega⟩)
      (trace.state ⟨start + steps, by omega⟩) =>
  NormalFormBendHistory.ComparisonExecutionCertificate
    constants bounds.maxRotationDepth bounds.neighborDepthSlack
    splayTree execution

/--
Recursively certify the contiguous trace segment beginning at a natural time
and containing the stated number of rotations.
-/
private noncomputable def certifiedSegment
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    (normal : IsStructurallyNormal bounds trace)
    (splayTree : BST 0 n)
    (allowance : 3 ≤ constants.comparisonRotation)
    (start steps : ℕ)
    (within : start + steps ≤ trace.rotationCount) :
    CertifiedSegment (constants := constants)
      (bounds := bounds) (trace := trace)
      splayTree start steps within := by
  induction steps generalizing start with
  | zero =>
      exact
        PSigma.mk .refl
          (NormalFormBendHistory.ComparisonExecutionCertificate.refl _)
  | succ steps ih =>
      have start_lt : start < trace.rotationCount := by
        omega
      let step : Fin trace.rotationCount := ⟨start, start_lt⟩
      have tailWithin :
          start + 1 + steps ≤ trace.rotationCount := by
        omega
      let tail :=
        ih (start + 1) tailWithin
      let rotation := trace.rotates step
      let context :=
        BoundedComparisonRotation.ofTrace normal splayTree step
      let combinedExecution :=
        RotationExecution.step rotation tail.fst
      let combinedCertificate :
          NormalFormBendHistory.ComparisonExecutionCertificate
            constants bounds.maxRotationDepth bounds.neighborDepthSlack
            splayTree combinedExecution :=
        .step rotation tail.fst context allowance tail.snd
      let combined :
          PSigma fun execution :
            RotationExecution steps.succ
              (trace.state step.castSucc)
              (trace.state
                ⟨start + 1 + steps, by omega⟩) =>
          NormalFormBendHistory.ComparisonExecutionCertificate
            constants bounds.maxRotationDepth bounds.neighborDepthSlack
            splayTree execution :=
        PSigma.mk combinedExecution combinedCertificate
      have startIndex :
          step.castSucc =
            (⟨start, by omega⟩ :
              Fin (trace.rotationCount + 1)) := by
        apply Fin.ext
        rfl
      have finishIndex :
          (⟨start + 1 + steps, by omega⟩ :
            Fin (trace.rotationCount + 1)) =
          (⟨start + steps.succ, by omega⟩ :
            Fin (trace.rotationCount + 1)) := by
        apply Fin.ext
        change start + 1 + steps = start + steps.succ
        omega
      rw [startIndex, finishIndex] at combined
      exact combined

/--
Every exact execution proof for a monotone comparison-trace segment has an
automatic bend certificate.  Proof irrelevance transports the recursively
constructed canonical execution to the caller's proof index.
-/
theorem exists_of_trace_segment
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    (normal : IsStructurallyNormal bounds trace)
    (splayTree : BST 0 n)
    (start finish : Fin (trace.rotationCount + 1))
    (ordered : start ≤ finish)
    (execution :
      RotationExecution (finish.val - start.val)
        (trace.state start) (trace.state finish))
    (allowance : 3 ≤ constants.comparisonRotation) :
    Nonempty
      (NormalFormBendHistory.ComparisonExecutionCertificate
        constants bounds.maxRotationDepth bounds.neighborDepthSlack
        splayTree execution) := by
  have within :
      start.val + (finish.val - start.val) ≤
        trace.rotationCount := by
    have finish_le : finish.val ≤ trace.rotationCount := by
      omega
    omega
  let canonical :=
    certifiedSegment normal splayTree allowance
      start.val (finish.val - start.val) within
  have endValue :
      start.val + (finish.val - start.val) = finish.val := by
    omega
  have endIndex :
      (⟨start.val + (finish.val - start.val), by omega⟩ :
        Fin (trace.rotationCount + 1)) = finish := by
    apply Fin.ext
    exact endValue
  have startIndex :
      (⟨start.val, by omega⟩ :
        Fin (trace.rotationCount + 1)) = start := by
    apply Fin.ext
    rfl
  let aligned :
      PSigma fun alignedExecution :
        RotationExecution (finish.val - start.val)
          (trace.state start) (trace.state finish) =>
      NormalFormBendHistory.ComparisonExecutionCertificate
        constants bounds.maxRotationDepth bounds.neighborDepthSlack
        splayTree alignedExecution := by
    let unaligned :
        PSigma fun canonicalExecution :
          RotationExecution (finish.val - start.val)
            (trace.state
              (⟨start.val, by omega⟩ :
                Fin (trace.rotationCount + 1)))
            (trace.state
              (⟨start.val + (finish.val - start.val), by omega⟩ :
                Fin (trace.rotationCount + 1))) =>
        NormalFormBendHistory.ComparisonExecutionCertificate
          constants bounds.maxRotationDepth bounds.neighborDepthSlack
          splayTree canonicalExecution :=
      PSigma.mk canonical.fst canonical.snd
    rw [startIndex, endIndex] at unaligned
    exact unaligned
  have executionEq : aligned.fst = execution :=
    Subsingleton.elim _ _
  exact ⟨executionEq ▸ aligned.snd⟩

/--
Convenience form for the canonical exact execution returned directly by
`ComparisonTrace.toRotationExecution_between`.
-/
theorem exists_of_toRotationExecution_between
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    (normal : IsStructurallyNormal bounds trace)
    (splayTree : BST 0 n)
    (start finish : Fin (trace.rotationCount + 1))
    (ordered : start ≤ finish)
    (allowance : 3 ≤ constants.comparisonRotation) :
    Nonempty
      (NormalFormBendHistory.ComparisonExecutionCertificate
        constants bounds.maxRotationDepth bounds.neighborDepthSlack
        splayTree
        (trace.toRotationExecution_between start finish ordered)) :=
  exists_of_trace_segment
    normal splayTree start finish ordered
    (trace.toRotationExecution_between start finish ordered)
    allowance

end Splay.Accounting.NormalFormBendHistory.ComparisonExecutionCertificate
