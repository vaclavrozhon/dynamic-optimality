import Splay.Accounting.NormalFormComparisonBendCertificate
import Splay.Accounting.NormalFormChronologicalBendHistory

namespace Splay.Accounting.NormalFormAutomaticBendHistory

open Splay.Tree
open Splay.Tree.BST
open Splay.Assumptions.NormalForm
open Splay.Assumptions.NormalForm.ComparisonTrace

/--
A proof-relevant certificate that mirrors one exact normal-form schedule but
stores only the complete-splay certificates.

The comparison executions are already indices of the underlying `Schedule`;
`toScheduleCertificate` reconstructs all their bend certificates
automatically from structural normality.
-/
inductive SplayOnlyScheduleCertificate
    (constants : BendConstants)
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    (normal : IsStructurallyNormal bounds trace) :
    {groups : List (RequestGroup trace)} →
      {time : Fin (trace.rotationCount + 1)} →
      {before after : BST 0 n} →
      (schedule : Schedule trace groups time before after) → Type
  | finish {time : Fin (trace.rotationCount + 1)}
      (tree : BST 0 n)
      (comparison :
        RotationExecution
          (trace.rotationCount - time.val)
          (trace.state time) trace.finalTree) :
      SplayOnlyScheduleCertificate constants normal
        (Schedule.finish tree comparison)
  | next {group : RequestGroup trace}
      {groups : List (RequestGroup trace)}
      {time : Fin (trace.rotationCount + 1)}
      {before middle after : BST 0 n}
      (ordered : time ≤ group.time)
      (comparison :
        RotationExecution
          (group.time.val - time.val)
          (trace.state time) (trace.state group.time))
      (splay :
        SplaySequence group.requests before middle)
      (tail :
        Schedule trace groups group.time middle after)
      (splayCertificate :
        NormalFormChronologicalBendHistory.SplaySequenceCertificate
          constants (trace.state group.time) splay)
      (tailCertificate :
        SplayOnlyScheduleCertificate constants normal tail) :
      SplayOnlyScheduleCertificate constants normal
        (Schedule.next ordered comparison splay tail)

namespace SplayOnlyScheduleCertificate

/--
A callback supplying exactly the complete-splay certificate required for a
request group.  It contains no comparison-tree geometry obligation.
-/
abbrev SplayCertificateProvider
    (constants : BendConstants)
    {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses} :=
  ∀ (group : RequestGroup trace)
    {before after : BST 0 n}
    (splay : SplaySequence group.requests before after),
    NormalFormChronologicalBendHistory.SplaySequenceCertificate
      constants (trace.state group.time) splay

/--
The lowest-level input needed from complete-splay accounting.

For any comparison time and complete standard splay whose key is at the
comparison root, the provider supplies just that splay's numerical bend
certificate. Request-group membership will discharge the root premise
automatically.
-/
abbrev CompleteSplayCertificateProvider
    (constants : BendConstants)
    {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses} :=
  ∀ (time : Fin (trace.rotationCount + 1))
    (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after),
    (trace.state time).HasRoot key.val →
      NormalFormChronologicalBendHistory.CompleteSplayCertificate
        constants (trace.state time) key execution

private def splaySequenceCertificateOfCompleteProviderAux
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses}
    (provider :
      CompleteSplayCertificateProvider constants (trace := trace))
    (group : RequestGroup trace)
    {requests : List (Fin n)}
    (requests_mem :
      ∀ request ∈ requests, request ∈ group.requests)
    {before after : BST 0 n}
    (splay : SplaySequence requests before after) :
    NormalFormChronologicalBendHistory.SplaySequenceCertificate
      constants (trace.state group.time) splay :=
  match splay with
  | .done tree =>
      .done tree
  | .next (access := access) head tail =>
      .next head tail
        (provider group.time access head
          (group.serves
            (requests_mem access (by simp))))
        (splaySequenceCertificateOfCompleteProviderAux
          provider group
          (fun request member =>
            requests_mem request (by simp [member]))
          tail)

/--
Certify a whole request group's splay sequence from a provider for individual
complete splays.

The recursion follows the exact `SplaySequence`.  At every head, the sequence
index proves that the access belongs to `group.requests`, so `group.serves`
supplies the provider's root premise.
-/
def splaySequenceCertificateOfCompleteProvider
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses}
    (provider :
      CompleteSplayCertificateProvider constants (trace := trace))
    (group : RequestGroup trace)
    {before after : BST 0 n}
    (splay : SplaySequence group.requests before after) :
    NormalFormChronologicalBendHistory.SplaySequenceCertificate
      constants (trace.state group.time) splay :=
  splaySequenceCertificateOfCompleteProviderAux
    provider group (fun _ member => member) splay

/--
Attach a per-group splay-certificate provider to any exact schedule.

This is the explicit functional constructor for
`SplayOnlyScheduleCertificate`; the schedule itself supplies every
comparison segment.
-/
noncomputable def ofSchedule
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : BST 0 n}
    (schedule : Schedule trace groups time before after)
    (provider : SplayCertificateProvider constants (trace := trace)) :
    SplayOnlyScheduleCertificate constants normal schedule := by
  induction schedule with
  | finish tree comparison =>
      exact .finish tree comparison
  | @next group groups time before middle after
      ordered comparison splay tail ih =>
      exact
        .next ordered comparison splay tail
          (provider group splay) ih

/--
Attach the lowest-level complete-splay provider to any exact schedule.

Both layers above an individual complete splay are now automatic: this
definition first certifies every request-group sequence, and `ofSchedule`
then follows the exact schedule.
-/
noncomputable def ofScheduleWithCompleteProvider
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : BST 0 n}
    (schedule : Schedule trace groups time before after)
    (provider :
      CompleteSplayCertificateProvider constants (trace := trace)) :
    SplayOnlyScheduleCertificate constants normal schedule :=
  ofSchedule schedule fun group {_ _} splay =>
    splaySequenceCertificateOfCompleteProvider provider group splay

/--
Fill every comparison segment of a splay-only schedule certificate
automatically.

The sole additional premise is the uniform comparison-rotation allowance.
The unit junction bound and all bounded-rotation contexts are reconstructed
by `ComparisonExecutionCertificate.exists_of_trace_segment`.
-/
noncomputable def toScheduleCertificate
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : BST 0 n}
    {schedule : Schedule trace groups time before after}
    (certificate :
      SplayOnlyScheduleCertificate constants normal schedule)
    (allowance : 3 ≤ constants.comparisonRotation) :
    NormalFormChronologicalBendHistory.ScheduleCertificate
      constants normal schedule := by
  induction certificate with
  | @finish time tree comparison =>
      have finishOrdered :
          time ≤ Fin.last trace.rotationCount :=
        Fin.le_last time
      let alignedExecution :
          RotationExecution
            ((Fin.last trace.rotationCount).val - time.val)
            (trace.state time)
            (trace.state (Fin.last trace.rotationCount)) := by
        simpa [ComparisonTrace.finalTree] using comparison
      let comparisonCertificate :=
        Classical.choice
          (NormalFormBendHistory.ComparisonExecutionCertificate.exists_of_trace_segment
              normal tree time (Fin.last trace.rotationCount)
              finishOrdered alignedExecution allowance)
      have executionEq : alignedExecution = comparison :=
        Subsingleton.elim _ _
      exact
        .finish tree comparison
          (executionEq ▸ comparisonCertificate)
  | @next group groups time before middle after
      ordered comparison splay tail
      splayCertificate tailCertificate ih =>
      let comparisonCertificate :=
        Classical.choice
          (NormalFormBendHistory.ComparisonExecutionCertificate.exists_of_trace_segment
              normal before time group.time ordered
              comparison allowance)
      exact
        .next ordered comparison splay tail
          comparisonCertificate splayCertificate ih

/--
After automatic comparison certification, obtain the concrete chronological
bend witness without any per-comparison-step geometry premise.
-/
noncomputable def toConcreteZigZagBendWitness
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {before after : BST 0 n}
    {schedule : Schedule trace groups 0 before after}
    (certificate :
      SplayOnlyScheduleCertificate constants normal schedule)
    (comparisonAllowance : 3 ≤ constants.comparisonRotation)
    (requests_eq : schedule.servedRequests = accesses)
    (initialUnit : 1 ≤ constants.initial) :
    ConcreteZigZagBendWitness
      constants before accesses trace :=
  NormalFormChronologicalBendHistory.ScheduleCertificate.toConcreteZigZagBendWitness
      (certificate.toScheduleCertificate comparisonAllowance)
      requests_eq initialUnit

/--
Direct automatic normal-form wrapper around the established global
zig-zag/bend accounting theorem.
-/
theorem concrete_zigZag_bends
    {constants : BendConstants}
    {n nearCost bendsBound : ℕ}
    {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {before after : BST 0 n}
    {schedule : Schedule trace groups 0 before after}
    (certificate :
      SplayOnlyScheduleCertificate constants normal schedule)
    (comparisonAllowance : 3 ≤ constants.comparisonRotation)
    (requests_eq : schedule.servedRequests = accesses)
    (initialUnit : 1 ≤ constants.initial)
    (comparisonCost_le : trace.cost ≤ nearCost)
    (coefficient_le : constants.coefficient ≤ bendsBound) :
    (concreteSplayTranscript before accesses).zigZag ≤
      (concreteSplayTranscript before accesses).zigZig +
        bendsBound * (n + nearCost) :=
  NormalFormChronologicalBendHistory.ScheduleCertificate.concrete_zigZag_bends
      (certificate.toScheduleCertificate comparisonAllowance)
      requests_eq initialUnit comparisonCost_le coefficient_le

end SplayOnlyScheduleCertificate

end Splay.Accounting.NormalFormAutomaticBendHistory
