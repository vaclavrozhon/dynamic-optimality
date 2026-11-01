import Splay.Accounting.NormalFormBendHistory
import Splay.Accounting.WholeSplayBendAggregation

namespace Splay.Accounting.NormalFormChronologicalBendHistory

open Splay.Rank
open Splay.Tree
open Splay.Tree.BST
open Splay.Assumptions.NormalForm
open Splay.Assumptions.NormalForm.ComparisonTrace
open Splay.Accounting.LocalBendGeometry

/-!
# Chronological normal-form bend histories

Complete splays in this module expose a numerical one-action certificate.
One constructor retains the sum of all chronological creation and removal
occurrences, so a bend removed by one substep and recreated later is counted
twice rather than erased by an endpoint set difference.  The abstract local
record also permits the manuscript's different route through temporary ranks
once that route has its own exact numerical history.  Comparison segments may
still be built from exact finite-set histories and then forgotten with
`FiniteBendHistory.toBendHistory`.
-/

/--
The exact numerical data needed from one complete splay.

This interface deliberately does not prescribe the intermediate snapshots.
`ofCreationLaw` below instantiates it with the fixed-snapshot chronological
substep history.  A future temporary-rank proof can instead supply its own
action and telescope through `ofAction`.
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
  bendAction :
    BendAction
  bendHistory :
    BendHistory
      (bends (Snapshot.ofTree comparison) before).card
      [bendAction]
      (bends (Snapshot.ofTree comparison) after).card
  bendAction_locallySound :
    bendAction.LocallySound constants
  bendAction_kind_eq :
    bendAction.kind = .splay
  bendAction_zigZig_eq :
    bendAction.zigZig = transcript.zigZig
  bendAction_zigZag_eq :
    bendAction.zigZag = transcript.zigZag

namespace CompleteSplayCertificate

/--
Package any exact numerical path for one complete access.

In particular, the supplied history may telescope through auxiliary
temporary-rank snapshots; only its true comparison-snapshot endpoints are
visible to the global schedule.
-/
def ofAction
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    (comparisonRoot : comparison.HasRoot key.val)
    (transcript : SplayExecutionTranscriptWitness execution)
    (action : BendAction)
    (history :
      BendHistory
        (bends (Snapshot.ofTree comparison) before).card
        [action]
        (bends (Snapshot.ofTree comparison) after).card)
    (locallySound : action.LocallySound constants)
    (kind_eq : action.kind = .splay)
    (zigZig_eq : action.zigZig = transcript.zigZig)
    (zigZag_eq : action.zigZag = transcript.zigZag) :
    CompleteSplayCertificate constants comparison key execution where
  comparisonRoot := comparisonRoot
  transcript := transcript
  bendAction := action
  bendHistory := history
  bendAction_locallySound := locallySound
  bendAction_kind_eq := kind_eq
  bendAction_zigZig_eq := zigZig_eq
  bendAction_zigZag_eq := zigZag_eq

/--
Select the canonical transcript and finite substep witness while leaving the
strong fixed-snapshot chronological creation law explicit.
-/
noncomputable def ofCreationLaw
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    (comparisonRoot : comparison.HasRoot key.val)
    (substepAllowance : 7 ≤ constants.splay)
    (creation :
      let transcript := splayExecutionTranscriptWitness execution
      let finiteWitness :=
        transcript.transcript.finiteBendWitness
          comparison comparisonRoot substepAllowance
      SplayExecutionFiniteBendWitness.WholeSplayCreationLaw
        finiteWitness) :
    CompleteSplayCertificate constants comparison key execution := by
  let transcript := splayExecutionTranscriptWitness execution
  let finiteWitness :=
    transcript.transcript.finiteBendWitness
      comparison comparisonRoot substepAllowance
  exact {
    comparisonRoot := comparisonRoot
    transcript := transcript
    bendAction := finiteWitness.chronologicalAction
    bendHistory := finiteWitness.chronologicalAction_history
    bendAction_locallySound :=
      finiteWitness.chronologicalAction_locallySound creation
    bendAction_kind_eq := rfl
    bendAction_zigZig_eq := rfl
    bendAction_zigZag_eq := rfl
  }

/--
A numerical fixed-snapshot charging certificate discharges the chronological
creation law whenever its administrative budget fits the advertised
complete-splay allowance.
-/
noncomputable def ofCharging
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {budget : ℕ}
    (comparisonRoot : comparison.HasRoot key.val)
    (substepAllowance : 7 ≤ constants.splay)
    (charging :
      let transcript := splayExecutionTranscriptWitness execution
      let finiteWitness :=
        transcript.transcript.finiteBendWitness
          comparison comparisonRoot substepAllowance
      SplayExecutionFiniteBendWitness.WholeSplayCreationCharging
        finiteWitness budget)
    (budget_le : budget ≤ constants.splay) :
    CompleteSplayCertificate constants comparison key execution := by
  apply ofCreationLaw comparisonRoot substepAllowance
  exact charging.creationLaw budget_le

/-- The certified numerical action for this complete access. -/
def action
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    (certificate :
      CompleteSplayCertificate constants comparison key execution) :
    BendAction :=
  certificate.bendAction

/-- The chosen local path telescopes to one exact numerical action. -/
theorem history
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    (certificate :
      CompleteSplayCertificate constants comparison key execution) :
    BendHistory
      (bends (Snapshot.ofTree comparison) before).card
      [certificate.action]
      (bends (Snapshot.ofTree comparison) after).card := by
  simpa only [action] using certificate.bendHistory

/-- The certified complete-access action is locally sound. -/
theorem action_locallySound
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    (certificate :
      CompleteSplayCertificate constants comparison key execution) :
    certificate.action.LocallySound constants := by
  simpa only [action] using certificate.bendAction_locallySound

/-- The chronological action is exactly one complete-splay action. -/
@[simp]
theorem action_kind_eq
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    (certificate :
      CompleteSplayCertificate constants comparison key execution) :
    certificate.action.kind = .splay := by
  exact certificate.bendAction_kind_eq

/-- The action retains the transcript's exact zig-zig count. -/
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
  exact certificate.bendAction_zigZig_eq

/-- The action retains the transcript's exact zig-zag count. -/
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
  exact certificate.bendAction_zigZag_eq

end CompleteSplayCertificate

/-- One chronological complete-splay certificate per request. -/
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
        CompleteSplayCertificate constants comparison access head)
      (tailCertificate :
        SplaySequenceCertificate constants comparison tail) :
      SplaySequenceCertificate constants comparison
        (SplaySequence.next head tail)

namespace SplaySequenceCertificate

/-- One multiplicity-preserving action per request, in request order. -/
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

/-- Assemble the exact orientation transcript of the certified sequence. -/
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
      let rest := tailCertificate.transcriptWitness
      { kinds := headCertificate.transcript.kinds ++ rest.kinds
        zig := headCertificate.transcript.zig + rest.zig
        zigZig :=
          headCertificate.transcript.zigZig + rest.zigZig
        zigZag :=
          headCertificate.transcript.zigZag + rest.zigZag
        transcript :=
          .next head tail
            headCertificate.transcript.transcript
            rest.transcript }

/-- Numerical complete-access histories concatenate without losing events. -/
theorem history
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n}
    {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    (certificate :
      SplaySequenceCertificate constants comparison sequence) :
    BendHistory
      (bends (Snapshot.ofTree comparison) before).card
      certificate.actions
      (bends (Snapshot.ofTree comparison) after).card := by
  induction certificate with
  | done tree =>
      exact .nil _
  | next head tail headCertificate tailCertificate ih =>
      simpa only [actions, List.singleton_append] using
        headCertificate.history.append ih

/-- Every complete-access action is sound under its creation law. -/
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
      intro candidate member
      simp only [actions, List.mem_cons] at member
      rcases member with rfl | inTail
      · exact headCertificate.action_locallySound
      · exact ih candidate inTail

/-- Exactly one splay action is retained per request. -/
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
      simp [actions, totalSplayActions, ih]
      omega

/-- A complete-splay sequence contains no comparison action. -/
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
      simp [actions, totalComparisonRotationActions, ih]

/-- The action list has the assembled transcript's exact zig-zig sum. -/
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

/-- The action list has the assembled transcript's exact zig-zag sum. -/
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
Local chronological certificates attached to the exact constructors of a
normal-form schedule.
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
        NormalFormBendHistory.ComparisonExecutionCertificate
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
        NormalFormBendHistory.ComparisonExecutionCertificate
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
The exact action order: comparison segment, complete splays at its endpoint,
then the remaining schedule.
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

/-- Concatenate the certified request transcripts in schedule order. -/
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
          NormalFormBendHistory.splaySequenceTranscript_append
            first.transcript rest.transcript }

/-- Reindex the assembled transcript by an advertised request list. -/
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
Exact numerical history of all chronological comparison and splay actions.
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
    BendHistory
      (bends (Snapshot.ofTree (trace.state time)) before).card
      certificate.actions
      (bends (Snapshot.ofTree trace.finalTree) after).card := by
  induction certificate with
  | finish tree comparison comparisonCertificate =>
      exact comparisonCertificate.history.toBendHistory
  | next ordered comparison splay tail
      comparisonCertificate splayCertificate
      tailCertificate ih =>
      simpa only [actions] using
        (comparisonCertificate.history.toBendHistory.append
          splayCertificate.history).append ih

/-- Every action is locally sound under its constructor-local certificate. -/
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
      · exact comparisonCertificate.all_actions_locallySound
          action inComparison
      · exact splayCertificate.all_actions_locallySound
          action inSplay
      · exact ih action inTail

/-- The schedule has exactly one complete-splay action per served request. -/
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

/-- The schedule has exactly one comparison action per consumed rotation. -/
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

/-- The interleaved actions retain the transcript's exact zig-zig sum. -/
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

/-- The interleaved actions retain the transcript's exact zig-zag sum. -/
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

/--
Turn a complete time-zero schedule directly into the numerical witness used
by the global bend telescope.  The initial finite bend set has at most one
element per internal key.
-/
noncomputable def toZigZagBendWitness
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
    (requests_eq : schedule.servedRequests = accesses)
    (initialUnit : 1 ≤ constants.initial) :
    ZigZagBendWitness constants trace
      (schedule.toSplaySequenceFor requests_eq)
      (certificate.splayTranscriptWitnessFor requests_eq) where
  initialBends :=
    (bends (Snapshot.ofTree trace.initialTree) before).card
  finalBends :=
    (bends (Snapshot.ofTree trace.finalTree) after).card
  actions := certificate.actions
  history := by
    simpa [ComparisonTrace.initialTree] using certificate.history
  locallySound := certificate.all_actions_locallySound
  initialBends_le := by
    have finiteBound :
        (bends (Snapshot.ofTree trace.initialTree) before).card ≤ n := by
      simpa using
        Finset.card_le_univ
          (bends (Snapshot.ofTree trace.initialTree) before)
    calc
      (bends (Snapshot.ofTree trace.initialTree) before).card ≤ n :=
        finiteBound
      _ = 1 * n := by simp
      _ ≤ constants.initial * n :=
        Nat.mul_le_mul_right n initialUnit
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
      _ = accesses.length :=
        congrArg List.length requests_eq
  comparisonRotationActions_eq := by
    calc
      totalComparisonRotationActions certificate.actions =
          schedule.comparisonRotationCount :=
        certificate.comparisonRotationActions_eq
      _ = trace.rotationCount := by
        simpa using schedule.comparisonRotationCount_eq

/--
Transcript determinism transports the chronological schedule witness to the
concrete chosen splay sequence.  Numeric histories do not need an endpoint
tree cast: only the two orientation totals mention the transcript parameter.
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
      ScheduleCertificate constants normal schedule)
    (requests_eq : schedule.servedRequests = accesses)
    (initialUnit : 1 ≤ constants.initial) :
    ConcreteZigZagBendWitness
      constants before accesses trace := by
  let witness :=
    certificate.toZigZagBendWitness requests_eq initialUnit
  have transcriptEq :=
    schedule.transcript_eq_concrete requests_eq
      (certificate.splayTranscriptWitnessFor requests_eq).transcript
  exact {
    initialBends := witness.initialBends
    finalBends := witness.finalBends
    actions := witness.actions
    history := witness.history
    locallySound := witness.locallySound
    initialBends_le := witness.initialBends_le
    zigZig_eq := witness.zigZig_eq.trans transcriptEq.2.2.1
    zigZag_eq := witness.zigZag_eq.trans transcriptEq.2.2.2
    splayActions_eq := witness.splayActions_eq
    comparisonRotationActions_eq :=
      witness.comparisonRotationActions_eq
  }

/--
Directly consume the concrete chronological witness through the established
accounting theorem.
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
    (_certificate :
      ScheduleCertificate constants normal schedule)
    (_requests_eq : schedule.servedRequests = accesses)
    (_initialUnit : 1 ≤ constants.initial)
    (_comparisonCost_le : trace.cost ≤ nearCost)
    (_coefficient_le : constants.coefficient ≤ bendsBound) :
    (concreteSplayTranscript before accesses).zigZag ≤
      (concreteSplayTranscript before accesses).zigZig +
        bendsBound * (n + nearCost) :=
  _root_.Splay.Accounting.concrete_zigZag_bends
    (_certificate.toConcreteZigZagBendWitness
      _requests_eq _initialUnit)
    _comparisonCost_le _coefficient_le

end ScheduleCertificate

end Splay.Accounting.NormalFormChronologicalBendHistory
