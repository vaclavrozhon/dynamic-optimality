import Splay.Accounting.ComparisonRotationJunctionBound
import Splay.Accounting.SplayBendTranscript
import Splay.Accounting.SplayDeterminism
import Splay.Lazy.NormalFormSchedule

namespace Splay.Accounting.NormalFormBendHistory

open Splay.Rank
open Splay.Tree
open Splay.Tree.BST
open Splay.Assumptions.NormalForm
open Splay.Assumptions.NormalForm.ComparisonTrace
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.ComparisonRotationBendGeometry
open Splay.Accounting.ComparisonRotationJunctionBound

/-!
This compatibility module composes exact finite endpoint histories in the
same chronological order as `ComparisonTrace.Schedule`.

Its complete-splay certificate retains the legacy endpoint-compression
premise:

* every complete splay request stores its own transcript witness and
  `CompletionResidue`.

That premise is known not to hold universally; see
`WholeSplayBendCounterexample`.  The multiplicity-preserving replacement is
`NormalFormChronologicalBendHistory`.  Every comparison head here already
uses the proved unit junction bound and stores only the uniform allowance
`3 ≤ constants.comparisonRotation`.
-/

@[simp]
theorem totalSplayActions_append
    (firstActions secondActions : List BendAction) :
    totalSplayActions (firstActions ++ secondActions) =
      totalSplayActions firstActions +
        totalSplayActions secondActions := by
  induction firstActions with
  | nil =>
      simp [totalSplayActions]
  | cons action actions ih =>
      simp [totalSplayActions, ih, Nat.add_assoc]

@[simp]
theorem totalComparisonRotationActions_append
    (firstActions secondActions : List BendAction) :
    totalComparisonRotationActions
        (firstActions ++ secondActions) =
      totalComparisonRotationActions firstActions +
        totalComparisonRotationActions secondActions := by
  induction firstActions with
  | nil =>
      simp [totalComparisonRotationActions]
  | cons action actions ih =>
      simp [totalComparisonRotationActions, ih, Nat.add_assoc]

@[simp]
theorem totalActionZigZig_append
    (firstActions secondActions : List BendAction) :
    totalActionZigZig (firstActions ++ secondActions) =
      totalActionZigZig firstActions +
        totalActionZigZig secondActions := by
  induction firstActions with
  | nil =>
      simp [totalActionZigZig]
  | cons action actions ih =>
      simp [totalActionZigZig, ih, Nat.add_assoc]

@[simp]
theorem totalActionZigZag_append
    (firstActions secondActions : List BendAction) :
    totalActionZigZag (firstActions ++ secondActions) =
      totalActionZigZag firstActions +
        totalActionZigZag secondActions := by
  induction firstActions with
  | nil =>
      simp [totalActionZigZag]
  | cons action actions ih =>
      simp [totalActionZigZag, ih, Nat.add_assoc]

/--
Step-indexed comparison-rotation obligations for one exact
`RotationExecution` on a fixed splay-tree shape.

The `step` constructor carries the concrete bounded-rotation context and the
single uniform allowance needed after `RotationAt.junctionCount_le_one`.
There is no residual junction premise.
-/
inductive ComparisonExecutionCertificate
    (constants : BendConstants)
    (maxRotationDepth neighborRankBound : ℕ)
    {n : ℕ} (splayTree : BST 0 n) :
    {length : ℕ} → {before after : BST 0 n} →
      RotationExecution length before after → Type
  | refl (comparison : BST 0 n) :
      ComparisonExecutionCertificate
        constants maxRotationDepth neighborRankBound splayTree
        (RotationExecution.refl (tree := comparison))
  | step {length depth : ℕ}
      {before middle after : BST 0 n}
      (rotation : RotationAt depth before middle)
      (execution : RotationExecution length middle after)
      (context :
        BoundedComparisonRotation
          (depth := depth)
          splayTree before middle
          maxRotationDepth neighborRankBound)
      (allowance :
        3 ≤ constants.comparisonRotation)
      (tail :
        ComparisonExecutionCertificate
          constants maxRotationDepth neighborRankBound
          splayTree execution) :
      ComparisonExecutionCertificate
        constants maxRotationDepth neighborRankBound splayTree
        (RotationExecution.step rotation execution)

namespace ComparisonExecutionCertificate

/-- Build the certified one-action history of one concrete rotation head. -/
noncomputable def singleton
    {constants : BendConstants}
    {maxRotationDepth neighborRankBound n depth : ℕ}
    {splayTree before after : BST 0 n}
    (context :
      BoundedComparisonRotation
        (depth := depth)
        splayTree before after
        maxRotationDepth neighborRankBound)
    (allowance : 3 ≤ constants.comparisonRotation) :
    ComparisonExecutionCertificate
      constants maxRotationDepth neighborRankBound splayTree
      (RotationExecution.singleton context.rotation) :=
  .step context.rotation .refl context allowance (.refl after)

/-- The exact comparison actions, in execution order. -/
noncomputable def actions
    {constants : BendConstants}
    {maxRotationDepth neighborRankBound n : ℕ}
    {splayTree : BST 0 n}
    {length : ℕ} {before after : BST 0 n}
    {execution : RotationExecution length before after} :
    ComparisonExecutionCertificate
      constants maxRotationDepth neighborRankBound
      splayTree execution → List BendAction
  | .refl _ => []
  | .step _ _ context _ tail =>
      context.bendAction :: tail.actions

/-- Concatenation of the singleton head histories gives exact endpoints. -/
theorem history
    {constants : BendConstants}
    {maxRotationDepth neighborRankBound n : ℕ}
    {splayTree : BST 0 n}
    {length : ℕ} {before after : BST 0 n}
    {execution : RotationExecution length before after}
    (certificate :
      ComparisonExecutionCertificate
        constants maxRotationDepth neighborRankBound
        splayTree execution) :
    FiniteBendHistory n
      (bends (Snapshot.ofTree before) splayTree)
      certificate.actions
      (bends (Snapshot.ofTree after) splayTree) := by
  induction certificate with
  | refl comparison =>
      exact .nil _
  | step rotation execution context allowance tail ih =>
      simpa only [actions, List.singleton_append] using
        context.bendAction_history.append ih

/-- Every comparison action is sound under the proved unit junction bound. -/
theorem all_actions_locallySound
    {constants : BendConstants}
    {maxRotationDepth neighborRankBound n : ℕ}
    {splayTree : BST 0 n}
    {length : ℕ} {before after : BST 0 n}
    {execution : RotationExecution length before after}
    (certificate :
      ComparisonExecutionCertificate
        constants maxRotationDepth neighborRankBound
        splayTree execution) :
    ∀ action ∈ certificate.actions,
      action.LocallySound constants := by
  induction certificate with
  | refl comparison =>
      simp [actions]
  | step rotation execution context allowance tail ih =>
      intro action member
      simp only [actions, List.mem_cons] at member
      rcases member with rfl | inTail
      · exact
          _root_.Splay.Accounting.ComparisonRotationJunctionBound.BoundedComparisonRotation.bendAction_locallySound_of_three_le
            context constants allowance
      · exact ih action inTail

/-- There are no complete-splay actions in a comparison segment. -/
@[simp]
theorem splayActions_eq_zero
    {constants : BendConstants}
    {maxRotationDepth neighborRankBound n : ℕ}
    {splayTree : BST 0 n}
    {length : ℕ} {before after : BST 0 n}
    {execution : RotationExecution length before after}
    (certificate :
      ComparisonExecutionCertificate
        constants maxRotationDepth neighborRankBound
        splayTree execution) :
    totalSplayActions certificate.actions = 0 := by
  induction certificate with
  | refl comparison =>
      rfl
  | step rotation execution context allowance tail ih =>
      simp [actions, totalSplayActions,
        BoundedComparisonRotation.bendAction,
        BendAction.between, ih]

/-- Exactly one comparison action is recorded per ordinary rotation. -/
@[simp]
theorem comparisonRotationActions_eq
    {constants : BendConstants}
    {maxRotationDepth neighborRankBound n : ℕ}
    {splayTree : BST 0 n}
    {length : ℕ} {before after : BST 0 n}
    {execution : RotationExecution length before after}
    (certificate :
      ComparisonExecutionCertificate
        constants maxRotationDepth neighborRankBound
        splayTree execution) :
    totalComparisonRotationActions certificate.actions = length := by
  induction certificate with
  | refl comparison =>
      rfl
  | step rotation execution context allowance tail ih =>
      simp [actions, totalComparisonRotationActions,
        BoundedComparisonRotation.bendAction,
        BendAction.between, ih]
      omega

/-- Comparison rotations carry no splay zig-zig count. -/
@[simp]
theorem zigZig_eq_zero
    {constants : BendConstants}
    {maxRotationDepth neighborRankBound n : ℕ}
    {splayTree : BST 0 n}
    {length : ℕ} {before after : BST 0 n}
    {execution : RotationExecution length before after}
    (certificate :
      ComparisonExecutionCertificate
        constants maxRotationDepth neighborRankBound
        splayTree execution) :
    totalActionZigZig certificate.actions = 0 := by
  induction certificate with
  | refl comparison =>
      rfl
  | step rotation execution context allowance tail ih =>
      simp [actions, totalActionZigZig,
        BoundedComparisonRotation.bendAction,
        BendAction.between, ih]

/-- Comparison rotations carry no splay zig-zag count. -/
@[simp]
theorem zigZag_eq_zero
    {constants : BendConstants}
    {maxRotationDepth neighborRankBound n : ℕ}
    {splayTree : BST 0 n}
    {length : ℕ} {before after : BST 0 n}
    {execution : RotationExecution length before after}
    (certificate :
      ComparisonExecutionCertificate
        constants maxRotationDepth neighborRankBound
        splayTree execution) :
    totalActionZigZag certificate.actions = 0 := by
  induction certificate with
  | refl comparison =>
      rfl
  | step rotation execution context allowance tail ih =>
      simp [actions, totalActionZigZag,
        BoundedComparisonRotation.bendAction,
        BendAction.between, ih]

end ComparisonExecutionCertificate

/--
Legacy finite-endpoint data for one complete splay request.

The completion residue is indexed by the concrete finite transcript witness,
and the comparison-root field ties the request to the schedule's serving
state.  The endpoint aggregation inside that residue is refuted in general;
new clients should use
`NormalFormChronologicalBendHistory.CompleteSplayCertificate`.
-/
structure CompleteSplayCertificate
    (constants : BendConstants)
    {n : ℕ} (comparison : BST 0 n)
    (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after) where
  comparisonRoot :
    comparison.HasRoot key.val
  transcript :
    SplayExecutionTranscriptWitness execution
  finiteWitness :
    SplayExecutionFiniteBendWitness
      constants (Snapshot.ofTree comparison)
      transcript.transcript
  completion :
    SplayExecutionFiniteBendWitness.CompletionResidue
      finiteWitness

namespace CompleteSplayCertificate

/--
Canonical constructor exposing the legacy local completion obligation.

The transcript and its exact finite bend history are selected by
`SplayBendTranscript`; the caller supplies `CompletionResidue` for this exact
chosen witness, not for an unrelated or existentially quantified access.
-/
noncomputable def ofCompletion
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    (comparisonRoot : comparison.HasRoot key.val)
    (splayAllowance : 7 ≤ constants.splay)
    (completion :
      let transcript := splayExecutionTranscriptWitness execution
      let finiteWitness :=
        transcript.transcript.finiteBendWitness
          comparison comparisonRoot splayAllowance
      SplayExecutionFiniteBendWitness.CompletionResidue
        finiteWitness) :
    CompleteSplayCertificate constants comparison key execution := by
  let transcript := splayExecutionTranscriptWitness execution
  let finiteWitness :=
    transcript.transcript.finiteBendWitness
      comparison comparisonRoot splayAllowance
  exact {
    comparisonRoot := comparisonRoot
    transcript := transcript
    finiteWitness := finiteWitness
    completion := completion
  }

/--
Compatibility constructor for a caller that can prove endpoint aggregation
in a restricted setting.  This proposition is not universal; see
`WholeSplayBendCounterexample`.
-/
noncomputable def ofWholeSplayAggregation
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    (comparisonRoot : comparison.HasRoot key.val)
    (splayAllowance : 7 ≤ constants.splay)
    (aggregation :
      let transcript := splayExecutionTranscriptWitness execution
      let finiteWitness :=
        transcript.transcript.finiteBendWitness
          comparison comparisonRoot splayAllowance
      SplayExecutionFiniteBendWitness.WholeSplayAggregationLaw
        finiteWitness) :
    CompleteSplayCertificate constants comparison key execution := by
  let transcript := splayExecutionTranscriptWitness execution
  let finiteWitness :=
    transcript.transcript.finiteBendWitness
      comparison comparisonRoot splayAllowance
  exact
    ofCompletion comparisonRoot splayAllowance
      (SplayExecutionFiniteBendWitness.CompletionResidue.ofWholeSplayAggregation
        finiteWitness aggregation)

/-- The endpoint action representing this one complete access. -/
noncomputable def action
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    (_certificate :
      CompleteSplayCertificate constants comparison key execution) :
    BendAction :=
  _certificate.finiteWitness.wholeSplayAction

/-- The complete request has its exact singleton endpoint history. -/
theorem history
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    (certificate :
      CompleteSplayCertificate constants comparison key execution) :
    FiniteBendHistory n
      (bends (Snapshot.ofTree comparison) before)
      [certificate.action]
      (bends (Snapshot.ofTree comparison) after) :=
  certificate.finiteWitness.wholeSplayAction_history

/-- The caller-supplied compatibility residue proves the endpoint action sound. -/
theorem action_locallySound
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    (certificate :
      CompleteSplayCertificate constants comparison key execution) :
    certificate.action.LocallySound constants :=
  certificate.finiteWitness.wholeSplayAction_locallySound
    certificate.completion

/-- The whole-access action retains the exact transcript zig-zig count. -/
@[simp]
theorem action_zigZig_eq
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    (certificate :
      CompleteSplayCertificate constants comparison key execution) :
    certificate.action.zigZig = certificate.transcript.zigZig := by
  simp [action,
    SplayExecutionFiniteBendWitness.wholeSplayAction,
    BendAction.between]

/-- The whole-access action retains the exact transcript zig-zag count. -/
@[simp]
theorem action_zigZag_eq
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    (certificate :
      CompleteSplayCertificate constants comparison key execution) :
    certificate.action.zigZag = certificate.transcript.zigZag := by
  simp [action,
    SplayExecutionFiniteBendWitness.wholeSplayAction,
    BendAction.between]

end CompleteSplayCertificate

/--
One exact complete-splay certificate per request of a dependent
`SplaySequence`, all at the same comparison snapshot.
-/
inductive SplaySequenceCertificate
    (constants : BendConstants)
    {n : ℕ} (comparison : BST 0 n) :
    {accesses : List (Fin n)} →
      {before after : BST 0 n} →
      SplaySequence accesses before after → Type
  | done (tree : BST 0 n) :
      SplaySequenceCertificate
        constants comparison (SplaySequence.done tree)
  | next {access : Fin n} {accesses : List (Fin n)}
      {before middle after : BST 0 n}
      (head : SplayExecution access.val before middle)
      (tail : SplaySequence accesses middle after)
      (headCertificate :
        CompleteSplayCertificate
          constants comparison access head)
      (tailCertificate :
        SplaySequenceCertificate constants comparison tail) :
      SplaySequenceCertificate constants comparison
        (SplaySequence.next head tail)

namespace SplaySequenceCertificate

/-- One whole-access action per request, in request order. -/
noncomputable def actions
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after} :
    SplaySequenceCertificate constants comparison sequence →
      List BendAction
  | .done _ => []
  | .next _ _ headCertificate tailCertificate =>
      headCertificate.action :: tailCertificate.actions

/-- The exact sequence transcript assembled from the per-request transcripts. -/
def transcriptWitness
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after} :
    SplaySequenceCertificate constants comparison sequence →
      SplaySequenceTranscriptWitness sequence
  | .done tree =>
      { kinds := []
        zig := 0
        zigZig := 0
        zigZag := 0
        transcript := .done tree }
  | .next head tail headCertificate tailCertificate =>
      let tailWitness := tailCertificate.transcriptWitness
      { kinds :=
          headCertificate.transcript.kinds ++
            tailWitness.kinds
        zig :=
          headCertificate.transcript.zig +
            tailWitness.zig
        zigZig :=
          headCertificate.transcript.zigZig +
            tailWitness.zigZig
        zigZag :=
          headCertificate.transcript.zigZag +
            tailWitness.zigZag
        transcript :=
          .next head tail
            headCertificate.transcript.transcript
            tailWitness.transcript }

/-- The whole-access singleton histories concatenate through the sequence. -/
theorem history
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    (certificate :
      SplaySequenceCertificate constants comparison sequence) :
    FiniteBendHistory n
      (bends (Snapshot.ofTree comparison) before)
      certificate.actions
      (bends (Snapshot.ofTree comparison) after) := by
  induction certificate with
  | done tree =>
      exact .nil _
  | next head tail headCertificate tailCertificate ih =>
      simpa only [actions, List.singleton_append] using
        headCertificate.history.append ih

/-- Every complete request action is locally sound at its serving snapshot. -/
theorem all_actions_locallySound
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    (certificate :
      SplaySequenceCertificate constants comparison sequence) :
    ∀ action ∈ certificate.actions,
      action.LocallySound constants := by
  induction certificate with
  | done tree =>
      simp [actions]
  | next head tail headCertificate tailCertificate ih =>
      intro action member
      simp only [actions, List.mem_cons] at member
      rcases member with rfl | inTail
      · exact headCertificate.action_locallySound
      · exact ih action inTail

/-- Exactly one complete-splay action is recorded per request. -/
@[simp]
theorem splayActions_eq
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    (certificate :
      SplaySequenceCertificate constants comparison sequence) :
    totalSplayActions certificate.actions = accesses.length := by
  induction certificate with
  | done tree =>
      rfl
  | next head tail headCertificate tailCertificate ih =>
      simp [actions, totalSplayActions,
        CompleteSplayCertificate.action,
        SplayExecutionFiniteBendWitness.wholeSplayAction,
        BendAction.between, ih]
      omega

/-- Complete-splay sequences contain no comparison actions. -/
@[simp]
theorem comparisonRotationActions_eq_zero
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    (certificate :
      SplaySequenceCertificate constants comparison sequence) :
    totalComparisonRotationActions certificate.actions = 0 := by
  induction certificate with
  | done tree =>
      rfl
  | next head tail headCertificate tailCertificate ih =>
      simp [actions, totalComparisonRotationActions,
        CompleteSplayCertificate.action,
        SplayExecutionFiniteBendWitness.wholeSplayAction,
        BendAction.between, ih]

/-- Whole-access actions retain the sequence transcript's total zig-zigs. -/
@[simp]
theorem zigZig_eq
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    (certificate :
      SplaySequenceCertificate constants comparison sequence) :
    totalActionZigZig certificate.actions =
      certificate.transcriptWitness.zigZig := by
  induction certificate with
  | done tree =>
      rfl
  | next head tail headCertificate tailCertificate ih =>
      simp [actions, transcriptWitness, totalActionZigZig, ih]

/-- Whole-access actions retain the sequence transcript's total zig-zags. -/
@[simp]
theorem zigZag_eq
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    (certificate :
      SplaySequenceCertificate constants comparison sequence) :
    totalActionZigZag certificate.actions =
      certificate.transcriptWitness.zigZag := by
  induction certificate with
  | done tree =>
      rfl
  | next head tail headCertificate tailCertificate ih =>
      simp [actions, transcriptWitness, totalActionZigZag, ih]

end SplaySequenceCertificate

/--
Concatenate two exact sequence transcripts along the same dependent boundary
as `SplaySequence.append`.
-/
theorem splaySequenceTranscript_append
    {n : ℕ}
    {firstAccesses secondAccesses : List (Fin n)}
    {before middle after : BST 0 n}
    {firstSequence :
      SplaySequence firstAccesses before middle}
    {secondSequence :
      SplaySequence secondAccesses middle after}
    {firstKinds secondKinds : List SplayStepKind}
    {firstZig firstZigZig firstZigZag : ℕ}
    {secondZig secondZigZig secondZigZag : ℕ}
    (first :
      SplaySequenceTranscript firstSequence firstKinds
        firstZig firstZigZig firstZigZag)
    (second :
      SplaySequenceTranscript secondSequence secondKinds
        secondZig secondZigZig secondZigZag) :
    SplaySequenceTranscript
      (firstSequence.append secondSequence)
      (firstKinds ++ secondKinds)
      (firstZig + secondZig)
      (firstZigZig + secondZigZig)
      (firstZigZag + secondZigZag) := by
  induction first with
  | done tree =>
      simpa [SplaySequence.append] using second
  | next head tail headTranscript tailTranscript ih =>
      simpa [SplaySequence.append, List.append_assoc,
        Nat.add_assoc] using
          (SplaySequenceTranscript.next
            head (tail.append secondSequence)
            headTranscript (ih second))

/--
Local certificates attached to the exact constructors of one normal-form
schedule.

At `next`, the comparison certificate changes only the snapshot on the
unchanged `before` splay tree.  The splay certificate then changes only that
tree at the new snapshot.  The tail begins at precisely the resulting pair,
so all three finite-set boundaries agree definitionally.
-/
inductive ScheduleCertificate
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
          (trace.state time) trace.finalTree)
      (comparisonCertificate :
        ComparisonExecutionCertificate
          constants bounds.maxRotationDepth
          bounds.neighborDepthSlack tree comparison) :
      ScheduleCertificate constants normal
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
      (comparisonCertificate :
        ComparisonExecutionCertificate
          constants bounds.maxRotationDepth
          bounds.neighborDepthSlack before comparison)
      (splayCertificate :
        SplaySequenceCertificate
          constants (trace.state group.time) splay)
      (tailCertificate :
        ScheduleCertificate constants normal tail) :
      ScheduleCertificate constants normal
        (Schedule.next ordered comparison splay tail)

namespace ScheduleCertificate

/--
The single chronological action list: comparison segment, complete requests
at its endpoint, then the remaining schedule.
-/
noncomputable def actions
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : BST 0 n}
    {schedule : Schedule trace groups time before after} :
    ScheduleCertificate constants normal schedule →
      List BendAction
  | .finish _ _ comparisonCertificate =>
      comparisonCertificate.actions
  | .next _ _ _ _ comparisonCertificate
      splayCertificate tailCertificate =>
      (comparisonCertificate.actions ++
        splayCertificate.actions) ++
          tailCertificate.actions

/--
Concatenate the per-group transcripts into the exact sequence obtained by
forgetting comparison rotations from this schedule.
-/
def splayTranscriptWitness
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : BST 0 n}
    {schedule : Schedule trace groups time before after} :
    ScheduleCertificate constants normal schedule →
      SplaySequenceTranscriptWitness schedule.toSplaySequence
  | .finish tree _ _ =>
      { kinds := []
        zig := 0
        zigZig := 0
        zigZag := 0
        transcript := .done tree }
  | .next _ _ _ _ comparisonCertificate
      splayCertificate tailCertificate =>
      let first := splayCertificate.transcriptWitness
      let rest := tailCertificate.splayTranscriptWitness
      { kinds := first.kinds ++ rest.kinds
        zig := first.zig + rest.zig
        zigZig := first.zigZig + rest.zigZig
        zigZag := first.zigZag + rest.zigZag
        transcript :=
          splaySequenceTranscript_append
            first.transcript rest.transcript }

/-- Reindex the assembled transcript by the advertised request list. -/
def splayTranscriptWitnessFor
    {constants : BendConstants}
    {n : ℕ} {accesses requested : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : BST 0 n}
    {schedule : Schedule trace groups time before after}
    (certificate :
      ScheduleCertificate constants normal schedule)
    (requestsEq : schedule.servedRequests = requested) :
    SplaySequenceTranscriptWitness
      (schedule.toSplaySequenceFor requestsEq) := by
  subst requested
  simpa [Schedule.toSplaySequenceFor] using
    certificate.splayTranscriptWitness

@[simp]
theorem splayTranscriptWitnessFor_zigZig
    {constants : BendConstants}
    {n : ℕ} {accesses requested : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : BST 0 n}
    {schedule : Schedule trace groups time before after}
    (certificate :
      ScheduleCertificate constants normal schedule)
    (requestsEq : schedule.servedRequests = requested) :
    (certificate.splayTranscriptWitnessFor requestsEq).zigZig =
      certificate.splayTranscriptWitness.zigZig := by
  subst requested
  rfl

@[simp]
theorem splayTranscriptWitnessFor_zigZag
    {constants : BendConstants}
    {n : ℕ} {accesses requested : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : BST 0 n}
    {schedule : Schedule trace groups time before after}
    (certificate :
      ScheduleCertificate constants normal schedule)
    (requestsEq : schedule.servedRequests = requested) :
    (certificate.splayTranscriptWitnessFor requestsEq).zigZag =
      certificate.splayTranscriptWitness.zigZag := by
  subst requested
  rfl

/--
Exact interleaved finite bend history with the schedule's true initial and
final snapshot/tree pairs.
-/
theorem history
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
      ScheduleCertificate constants normal schedule) :
    FiniteBendHistory n
      (bends (Snapshot.ofTree (trace.state time)) before)
      certificate.actions
      (bends (Snapshot.ofTree trace.finalTree) after) := by
  induction certificate with
  | finish tree comparison comparisonCertificate =>
      exact comparisonCertificate.history
  | next ordered comparison splay tail
      comparisonCertificate splayCertificate
      tailCertificate ih =>
      simpa only [actions] using
        (comparisonCertificate.history.append
          splayCertificate.history).append ih

/-- Every interleaved action is sound under its own local certificate. -/
theorem all_actions_locallySound
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
      ScheduleCertificate constants normal schedule) :
    ∀ action ∈ certificate.actions,
      action.LocallySound constants := by
  induction certificate with
  | finish tree comparison comparisonCertificate =>
      exact comparisonCertificate.all_actions_locallySound
  | next ordered comparison splay tail
      comparisonCertificate splayCertificate
      tailCertificate ih =>
      intro action member
      simp only [actions, List.mem_append] at member
      rcases member with (inComparison | inSplay) | inTail
      · exact
          comparisonCertificate.all_actions_locallySound
            action inComparison
      · exact
          splayCertificate.all_actions_locallySound
            action inSplay
      · exact ih action inTail

/-- The schedule contributes one splay action per served request. -/
theorem splayActions_eq
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
      ScheduleCertificate constants normal schedule) :
    totalSplayActions certificate.actions =
      schedule.servedRequests.length := by
  induction certificate with
  | finish tree comparison comparisonCertificate =>
      simp [actions, Schedule.servedRequests]
  | next ordered comparison splay tail
      comparisonCertificate splayCertificate
      tailCertificate ih =>
      simp [actions, Schedule.servedRequests, ih]

/-- The schedule contributes one comparison action per consumed rotation. -/
theorem comparisonRotationActions_eq
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
      ScheduleCertificate constants normal schedule) :
    totalComparisonRotationActions certificate.actions =
      schedule.comparisonRotationCount := by
  induction certificate with
  | finish tree comparison comparisonCertificate =>
      simp [actions, Schedule.comparisonRotationCount]
  | next ordered comparison splay tail
      comparisonCertificate splayCertificate
      tailCertificate ih =>
      simp [actions, Schedule.comparisonRotationCount, ih]

/-- Interleaved actions retain the concatenated transcript's zig-zig sum. -/
@[simp]
theorem zigZig_eq
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
      ScheduleCertificate constants normal schedule) :
    totalActionZigZig certificate.actions =
      certificate.splayTranscriptWitness.zigZig := by
  induction certificate with
  | finish tree comparison comparisonCertificate =>
      simp [actions, splayTranscriptWitness]
  | next ordered comparison splay tail
      comparisonCertificate splayCertificate
      tailCertificate ih =>
      simp [actions, splayTranscriptWitness, ih]

/-- Interleaved actions retain the concatenated transcript's zig-zag sum. -/
@[simp]
theorem zigZag_eq
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
      ScheduleCertificate constants normal schedule) :
    totalActionZigZag certificate.actions =
      certificate.splayTranscriptWitness.zigZag := by
  induction certificate with
  | finish tree comparison comparisonCertificate =>
      simp [actions, splayTranscriptWitness]
  | next ordered comparison splay tail
      comparisonCertificate splayCertificate
      tailCertificate ih =>
      simp [actions, splayTranscriptWitness, ih]

end ScheduleCertificate

/--
The final data product for a full schedule starting at comparison time zero.
It retains the exact endpoint bend sets, the single interleaved history,
pointwise local soundness, and both requested action counts.
-/
structure InterleavedFiniteBendWitness
    (constants : BendConstants)
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    (normal : IsStructurallyNormal bounds trace)
    {groups : List (RequestGroup trace)}
    {before after : BST 0 n}
    (schedule : Schedule trace groups 0 before after)
    (requests_eq : schedule.servedRequests = accesses) where
  transcript :
    SplaySequenceTranscriptWitness
      (schedule.toSplaySequenceFor requests_eq)
  actions : List BendAction
  history :
    FiniteBendHistory n
      (bends (Snapshot.ofTree trace.initialTree) before)
      actions
      (bends (Snapshot.ofTree trace.finalTree) after)
  locallySound :
    ∀ action ∈ actions, action.LocallySound constants
  zigZig_eq :
    totalActionZigZig actions = transcript.zigZig
  zigZag_eq :
    totalActionZigZag actions = transcript.zigZag
  splayActions_eq :
    totalSplayActions actions = accesses.length
  comparisonRotationActions_eq :
    totalComparisonRotationActions actions =
      trace.rotationCount

/--
Chronological composition theorem for a complete normal-form schedule.

All remaining assumptions occur inside `ScheduleCertificate` at their exact
rotation or request constructors.  `requests_eq` is only the structural
statement that the schedule's grouped requests flatten to the original
access list.
-/
noncomputable def ScheduleCertificate.toInterleavedFiniteBendWitness
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {before after : BST 0 n}
    {schedule : Schedule trace groups 0 before after}
    (certificate :
      ScheduleCertificate constants normal schedule)
    (requests_eq : schedule.servedRequests = accesses) :
    InterleavedFiniteBendWitness
      constants normal schedule requests_eq where
  transcript :=
    certificate.splayTranscriptWitnessFor requests_eq
  actions := certificate.actions
  history := by
    simpa [ComparisonTrace.initialTree] using certificate.history
  locallySound := certificate.all_actions_locallySound
  zigZig_eq := by
    calc
      totalActionZigZig certificate.actions =
          certificate.splayTranscriptWitness.zigZig :=
        certificate.zigZig_eq
      _ =
          (certificate.splayTranscriptWitnessFor
            requests_eq).zigZig := by simp
  zigZag_eq := by
    calc
      totalActionZigZag certificate.actions =
          certificate.splayTranscriptWitness.zigZag :=
        certificate.zigZag_eq
      _ =
          (certificate.splayTranscriptWitnessFor
            requests_eq).zigZag := by simp
  splayActions_eq := by
    calc
      totalSplayActions certificate.actions =
          schedule.servedRequests.length :=
        certificate.splayActions_eq
      _ = accesses.length := congrArg List.length requests_eq
  comparisonRotationActions_eq := by
    calc
      totalComparisonRotationActions certificate.actions =
          schedule.comparisonRotationCount :=
        certificate.comparisonRotationActions_eq
      _ = trace.rotationCount := by
        simpa using schedule.comparisonRotationCount_eq

namespace InterleavedFiniteBendWitness

/--
Forget the schedule-local certificate packaging and instantiate the existing
global finite bend witness with the schedule's concatenated splay sequence
and exact transcript.
-/
noncomputable def toFiniteZigZagBendWitness
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {before after : BST 0 n}
    {schedule : Schedule trace groups 0 before after}
    {requests_eq : schedule.servedRequests = accesses}
    (witness :
      InterleavedFiniteBendWitness
        constants normal schedule requests_eq) :
    FiniteZigZagBendWitness
      constants trace
      (schedule.toSplaySequenceFor requests_eq)
      witness.transcript where
  initialBends :=
    bends (Snapshot.ofTree trace.initialTree) before
  finalBends :=
    bends (Snapshot.ofTree trace.finalTree) after
  actions := witness.actions
  history := witness.history
  locallySound := witness.locallySound
  zigZig_eq := witness.zigZig_eq
  zigZag_eq := witness.zigZag_eq
  splayActions_eq := witness.splayActions_eq
  comparisonRotationActions_eq :=
    witness.comparisonRotationActions_eq

/--
Transport the schedule witness all the way to the concrete accounting API.

Schedule determinism identifies its final splay tree with the chosen
sequence's endpoint.  Transcript determinism identifies both orientation
totals with `concreteSplayTranscript`; the action list and finite-set history
themselves are unchanged.
-/
noncomputable def toConcreteFiniteZigZagBendWitness
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {before after : BST 0 n}
    {schedule : Schedule trace groups 0 before after}
    {requests_eq : schedule.servedRequests = accesses}
    (witness :
      InterleavedFiniteBendWitness
        constants normal schedule requests_eq) :
    ConcreteFiniteZigZagBendWitness
      constants before accesses trace := by
  have finalEq :=
    schedule.final_eq_chosen requests_eq
  have transcriptEq :=
    schedule.transcript_eq_concrete
      requests_eq witness.transcript.transcript
  refine {
    initialBends :=
      bends (Snapshot.ofTree trace.initialTree) before
    finalBends :=
      bends (Snapshot.ofTree trace.finalTree)
        (chosenSplaySequenceWitness before accesses).1
    actions := witness.actions
    history := ?_
    locallySound := witness.locallySound
    zigZig_eq := witness.zigZig_eq.trans transcriptEq.2.2.1
    zigZag_eq := witness.zigZag_eq.trans transcriptEq.2.2.2
    splayActions_eq := witness.splayActions_eq
    comparisonRotationActions_eq :=
      witness.comparisonRotationActions_eq
  }
  simpa only [finalEq] using witness.history

end InterleavedFiniteBendWitness

end Splay.Accounting.NormalFormBendHistory
