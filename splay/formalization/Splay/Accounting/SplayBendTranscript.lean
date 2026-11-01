import Splay.Accounting.ContextualBendGeometry
import Splay.Accounting.NonZigZagBendGeometry
import Splay.Accounting.SplayPairingTranscript

namespace Splay.Accounting

open Splay.Tree.BST
open Splay.Rank
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.ContextualBendGeometry

namespace DoubleOrientationAt

/-- Boolean-general induction form of the zig-zag conversion. -/
private theorem toZigZagAt_of_false
    {isZigZig : Bool} {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (orientation :
      DoubleOrientationAt isZigZig
        (depth := depth) (key := key) before after)
    (isFalse : isZigZig = false) :
    ZigZagAt key before after := by
  induction orientation with
  | zigZigLeft a b c d =>
      simp at isFalse
  | zigZigRight a b c d =>
      simp at isFalse
  | zigZagLeftRight a b c d =>
      exact .leftRight a b c d
  | zigZagRightLeft a b c d =>
      exact .rightLeft a b c d
  | leftContext orientation right ih =>
      exact .leftContext (ih isFalse) right
  | rightContext left orientation ih =>
      exact .rightContext left (ih isFalse)

/--
A contextual double rotation classified as non-zig-zig is exactly a
`ZigZagAt`.  This connects the existing proof-relevant splay transcript to
the contextual bend geometry without reclassifying the tree shapes.
-/
theorem false_toZigZagAt
    {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (orientation :
      DoubleOrientationAt false
        (depth := depth) (key := key) before after) :
    ZigZagAt key before after :=
  toZigZagAt_of_false orientation rfl

end DoubleOrientationAt

/--
Exact chronological agreement between one transcript kind and one finite
bend action.  Only zig-zag actions are required to be locally sound in this
generic relation; the concrete construction below supplies the separately
proved zig and zig-zig creation bounds.
-/
def BendAction.MatchesTranscriptStep
    (constants : BendConstants)
    (kind : SplayStepKind) (action : BendAction) : Prop :=
  action.kind = .splay ∧
    action.zigZig =
      (if kind = .zigZig then 1 else 0) ∧
    action.zigZag =
      (if kind = .zigZag then 1 else 0) ∧
    (kind = .zigZag → action.LocallySound constants)

/--
The auxiliary creation estimate, stated only where it is needed:
an ordinary zig creates at most the administrative allowance, while a
zig-zig may additionally create one bend.  The zig-zag case is deliberately
vacuous because its full local soundness is already proved geometrically.
-/
def BendAction.NonZigZagCreationBound
    (constants : BendConstants)
    (kind : SplayStepKind) (action : BendAction) : Prop :=
  kind ≠ .zigZag →
    action.created ≤
      (if kind = .zigZig then 1 else 0) + constants.splay

/--
The proved zig-zag clause plus the zig/zig-zig creation estimate
are exactly enough for local soundness of a transcript subaction.
-/
theorem BendAction.locallySound_of_matchesTranscriptStep
    {constants : BendConstants}
    {kind : SplayStepKind} {action : BendAction}
    (matched : action.MatchesTranscriptStep constants kind)
    (creation : action.NonZigZagCreationBound constants kind) :
    action.LocallySound constants := by
  by_cases isZigZag : kind = .zigZag
  · exact matched.2.2.2 isZigZag
  · rw [BendAction.LocallySound, matched.1]
    constructor
    · rw [matched.2.2.1]
      simp [isZigZag]
    · simpa [matched.2.1] using creation isZigZag

/--
Finite bend history for every chronological step of one concrete splay
execution, aligned with its proof-indexed transcript.
-/
structure SplayExecutionFiniteBendWitness
    (constants : BendConstants)
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (snapshot : Snapshot n)
    (_transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag) where
  actions : List BendAction
  history :
    FiniteBendHistory n
      (bends snapshot before) actions (bends snapshot after)
  alignment :
    List.Forall₂
      (BendAction.MatchesTranscriptStep constants)
      kinds actions
  nonZigZagCreation :
    List.Forall₂
      (BendAction.NonZigZagCreationBound constants)
      kinds actions
  each_created_le_seven :
    ∀ action ∈ actions, action.created ≤ 7
  zigZig_eq :
    totalActionZigZig actions = zigZig
  zigZag_eq :
    totalActionZigZag actions = zigZag
  splayActions_eq :
    totalSplayActions actions = kinds.length

namespace SplayExecutionFiniteBendWitness

/-- Alignment itself gives exact equality of the two chronological lengths. -/
theorem actions_length_eq
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript) :
    witness.actions.length = kinds.length :=
  witness.alignment.length_eq.symm

/-- The aligned kind list retains all three exact transcript counts. -/
theorem exact_kind_counts
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (_witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript) :
    kinds.count .zig = zig ∧
      kinds.count .zigZig = zigZig ∧
      kinds.count .zigZag = zigZag :=
  ⟨transcript.count_zig, transcript.count_zigZig,
    transcript.count_zigZag⟩

/-- Exact positional agreement at every valid chronological index. -/
theorem action_at_index
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript)
    (index : ℕ)
    (kindIndex : index < kinds.length)
    (actionIndex : index < witness.actions.length) :
    BendAction.MatchesTranscriptStep constants
      (kinds.get ⟨index, kindIndex⟩)
      (witness.actions.get ⟨index, actionIndex⟩) :=
  witness.alignment.get kindIndex actionIndex

/-- In particular, every zig-zag selected by an index is locally sound. -/
theorem zigZag_action_at_index_locallySound
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript)
    (index : ℕ)
    (kindIndex : index < kinds.length)
    (actionIndex : index < witness.actions.length)
    (isZigZag : kinds.get ⟨index, kindIndex⟩ = .zigZag) :
    (witness.actions.get ⟨index, actionIndex⟩).LocallySound constants :=
  (witness.action_at_index index kindIndex actionIndex).2.2.2
    isZigZag

/--
Every action in the chronological alignment is locally sound whenever its
paired transcript kind is a zig-zag.
-/
theorem zigZag_actions_locallySound
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript) :
    List.Forall₂
      (fun kind action =>
        kind = .zigZag → action.LocallySound constants)
      kinds witness.actions :=
  witness.alignment.imp (fun _ _ head => head.2.2.2)

/--
Given the isolated zig/zig-zig creation estimates at matching positions,
every chronological subaction is locally sound.
-/
theorem actions_locallySound_of_nonZigZagCreation
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript)
    (creation :
      List.Forall₂
        (BendAction.NonZigZagCreationBound constants)
        kinds witness.actions) :
    List.Forall₂
      (fun _ action => action.LocallySound constants)
      kinds witness.actions :=
  List.Forall₂.mp
    (fun _ _ matched bound =>
      BendAction.locallySound_of_matchesTranscriptStep matched bound)
    witness.alignment creation

/-- Forget the left-hand transcript index after proving subaction soundness. -/
private theorem all_right_of_forall₂
    {α : Type*} {actions : List BendAction}
    {property : BendAction → Prop} {indices : List α}
    (paired :
      List.Forall₂ (fun _ action => property action) indices actions) :
    ∀ action ∈ actions, property action := by
  induction paired with
  | nil =>
      simp
  | @cons index action indices actions head tail ih =>
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact ih candidate member

/--
Pointwise form consumed by the existing numerical telescope.
-/
theorem all_actions_locallySound_of_nonZigZagCreation
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript)
    (creation :
      List.Forall₂
        (BendAction.NonZigZagCreationBound constants)
        kinds witness.actions) :
    ∀ action ∈ witness.actions, action.LocallySound constants :=
  all_right_of_forall₂
    (witness.actions_locallySound_of_nonZigZagCreation creation)

/--
The concrete transcript construction stores the zig/zig-zig geometry, so all
of its chronological subactions are locally sound without an extra premise.
-/
theorem all_actions_locallySound
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript) :
    ∀ action ∈ witness.actions, action.LocallySound constants :=
  witness.all_actions_locallySound_of_nonZigZagCreation
    witness.nonZigZagCreation

/--
Legacy endpoint compression of a complete access.  It has the true endpoint
bend sets and exact orientation counts, but it forgets an identity that is
removed and later recreated.  The multiplicity-preserving replacement is
`chronologicalAction` in `WholeSplayBendAggregation`.
-/
noncomputable def wholeSplayAction
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (_witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript) :
    BendAction :=
  BendAction.between .splay zigZig zigZag
    (bends snapshot before) (bends snapshot after)

/-- The legacy endpoint action has an exact singleton finite-set history. -/
theorem wholeSplayAction_history
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript) :
    FiniteBendHistory n (bends snapshot before)
      [witness.wholeSplayAction] (bends snapshot after) := by
  simpa [wholeSplayAction] using
    (FiniteBendHistory.cons .splay zigZig zigZag
      (FiniteBendHistory.nil (bends snapshot after)))

/--
Legacy endpoint aggregation proposition.

This is not valid for all genuine splay transcripts:
`WholeSplayBendCounterexample.not_wholeSplayAggregationLaw` gives a checked
two-zig-zag refutation.  It is retained only as a compatibility boundary for
older finite-endpoint clients.  New accounting should use
`WholeSplayCreationLaw` and the multiplicity-preserving chronological action.
-/
def WholeSplayAggregationLaw
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript) : Prop :=
  (∀ action ∈ witness.actions, action.LocallySound constants) →
    witness.wholeSplayAction.LocallySound constants

/--
Compatibility packaging for the former endpoint-based API.  Its aggregation
field is deliberately explicit and is not claimed to hold universally.
-/
structure CompletionResidue
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript) :
    Prop where
  nonZigZagCreation :
    List.Forall₂
      (BendAction.NonZigZagCreationBound constants)
      kinds witness.actions
  wholeSplayAggregation :
    WholeSplayAggregationLaw witness

/-- Package a caller-supplied legacy endpoint aggregation proof. -/
theorem CompletionResidue.ofWholeSplayAggregation
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript)
    (aggregation : WholeSplayAggregationLaw witness) :
    CompletionResidue witness where
  nonZigZagCreation := witness.nonZigZagCreation
  wholeSplayAggregation := aggregation

/-- A supplied legacy residue makes the endpoint-compressed action sound. -/
theorem wholeSplayAction_locallySound
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript)
    (residue : CompletionResidue witness) :
    witness.wholeSplayAction.LocallySound constants :=
  residue.wholeSplayAggregation
    (witness.all_actions_locallySound_of_nonZigZagCreation
      residue.nonZigZagCreation)

end SplayExecutionFiniteBendWitness

namespace SplayExecutionTranscript

/--
Chronologically realize every transcript step as a transition between the
actual finite bend sets of its two proof-indexed endpoint trees.

The comparison tree is fixed at the serving state for this access.  Its root
certificate makes every genuine zig-zag head locally sound through
`ContextualBendGeometry`; `NonZigZagBendGeometry` supplies the creation
estimates for every zig and contextual zig-zig.
-/
theorem exists_finiteBendWitness
    {constants : BendConstants}
    {n : ℕ} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key.val execution
        kinds zig zigZig zigZag)
    (comparison : BST 0 n)
    (comparisonRoot : comparison.HasRoot key.val)
    (splayAllowance : 7 ≤ constants.splay) :
    Nonempty
      (SplayExecutionFiniteBendWitness
        constants (Snapshot.ofTree comparison) transcript) := by
  cases transcript with
  | @done lower upper tree root =>
      exact ⟨{
        actions := []
        history := .nil _
        alignment := .nil
        nonZigZagCreation := .nil
        each_created_le_seven := by simp
        zigZig_eq := rfl
        zigZag_eq := rfl
        splayActions_eq := rfl
      }⟩
  | @zig lower upper before middle after kinds zig zigZig zigZag
      step tail transcript =>
      obtain ⟨tailWitness⟩ :=
        exists_finiteBendWitness transcript comparison comparisonRoot
          splayAllowance
      let action :=
        BendAction.between .splay 0 0
          (bends (Snapshot.ofTree comparison) before)
          (bends (Snapshot.ofTree comparison) middle)
      have headCreated : action.created ≤ 7 := by
        simpa [action, BendAction.between] using
          NonZigZagBendGeometry.Zig.bends_created_le_seven
            step (Snapshot.ofTree comparison)
      refine ⟨{
        actions := action :: tailWitness.actions
        history := .cons .splay 0 0 tailWitness.history
        alignment := .cons ?_ tailWitness.alignment
        nonZigZagCreation :=
          .cons ?_ tailWitness.nonZigZagCreation
        each_created_le_seven := ?_
        zigZig_eq := ?_
        zigZag_eq := ?_
        splayActions_eq := ?_
      }⟩
      · simp [BendAction.MatchesTranscriptStep, action,
          BendAction.between]
      · intro _
        simpa [action, BendAction.between] using
          headCreated.trans splayAllowance
      · intro candidate member
        rcases List.mem_cons.mp member with rfl | member
        · exact headCreated
        · exact tailWitness.each_created_le_seven candidate member
      · simpa [totalActionZigZig, action, BendAction.between] using
          tailWitness.zigZig_eq
      · simpa [totalActionZigZag, action, BendAction.between] using
          tailWitness.zigZag_eq
      · have tailCount := tailWitness.splayActions_eq
        simp [totalSplayActions, action, BendAction.between]
        omega
  | @zigZig depth lower upper before middle after kinds zig zigZig zigZag
      step orientation tail transcript =>
      obtain ⟨tailWitness⟩ :=
        exists_finiteBendWitness transcript comparison comparisonRoot
          splayAllowance
      let action :=
        BendAction.between .splay 1 0
          (bends (Snapshot.ofTree comparison) before)
          (bends (Snapshot.ofTree comparison) middle)
      have headCreated : action.created ≤ 7 := by
        simpa [action, BendAction.between] using
          NonZigZagBendGeometry.DoubleOrientationAt.true_bends_created_le_seven
            orientation (Snapshot.ofTree comparison)
      refine ⟨{
        actions := action :: tailWitness.actions
        history := .cons .splay 1 0 tailWitness.history
        alignment := .cons ?_ tailWitness.alignment
        nonZigZagCreation :=
          .cons ?_ tailWitness.nonZigZagCreation
        each_created_le_seven := ?_
        zigZig_eq := ?_
        zigZag_eq := ?_
        splayActions_eq := ?_
      }⟩
      · simp [BendAction.MatchesTranscriptStep, action,
          BendAction.between]
      · intro _
        exact headCreated.trans (by omega)
      · intro candidate member
        rcases List.mem_cons.mp member with rfl | member
        · exact headCreated
        · exact tailWitness.each_created_le_seven candidate member
      · have tailCount := tailWitness.zigZig_eq
        simp [totalActionZigZig, action, BendAction.between]
        omega
      · simpa [totalActionZigZag, action, BendAction.between] using
          tailWitness.zigZag_eq
      · have tailCount := tailWitness.splayActions_eq
        simp [totalSplayActions, action, BendAction.between]
        omega
  | @zigZag depth lower upper before middle after kinds zig zigZig zigZag
      step orientation tail transcript =>
      obtain ⟨tailWitness⟩ :=
        exists_finiteBendWitness transcript comparison comparisonRoot
          splayAllowance
      let geometry := orientation.false_toZigZagAt
      let action :=
        BendAction.between .splay 0 1
          (bends (Snapshot.ofTree comparison) before)
          (bends (Snapshot.ofTree comparison) middle)
      have headSound :
          action.LocallySound constants := by
        simpa [action,
          ContextualBendGeometry.ZigZagAt.bendAction,
          BendAction.between] using
          ContextualBendGeometry.ZigZagAt.bendAction_locallySound_of_comparisonRoot
            geometry comparison constants splayAllowance comparisonRoot
      have headCreated : action.created ≤ 7 := by
        have created :=
          geometry.created_le_seven
            (Snapshot.ofTree comparison) (Nat.le_refl n) none
        simpa [action, bends, BendAction.between] using created
      refine ⟨{
        actions := action :: tailWitness.actions
        history := .cons .splay 0 1 tailWitness.history
        alignment := .cons ?_ tailWitness.alignment
        nonZigZagCreation :=
          .cons ?_ tailWitness.nonZigZagCreation
        each_created_le_seven := ?_
        zigZig_eq := ?_
        zigZag_eq := ?_
        splayActions_eq := ?_
      }⟩
      · refine ⟨rfl, by simp [action, BendAction.between],
          by simp [action, BendAction.between], ?_⟩
        intro _
        exact headSound
      · simp [BendAction.NonZigZagCreationBound]
      · intro candidate member
        rcases List.mem_cons.mp member with rfl | member
        · exact headCreated
        · exact tailWitness.each_created_le_seven candidate member
      · simpa [totalActionZigZig, action, BendAction.between] using
          tailWitness.zigZig_eq
      · have tailCount := tailWitness.zigZag_eq
        simp [totalActionZigZag, action, BendAction.between]
        omega
      · have tailCount := tailWitness.splayActions_eq
        simp [totalSplayActions, action, BendAction.between]
        omega

/-- A canonical chosen form of `exists_finiteBendWitness` for downstream use. -/
noncomputable def finiteBendWitness
    {constants : BendConstants}
    {n : ℕ} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key.val execution
        kinds zig zigZig zigZag)
    (comparison : BST 0 n)
    (comparisonRoot : comparison.HasRoot key.val)
    (splayAllowance : 7 ≤ constants.splay) :
    SplayExecutionFiniteBendWitness
      constants (Snapshot.ofTree comparison) transcript :=
  Classical.choice
    (transcript.exists_finiteBendWitness comparison comparisonRoot
      splayAllowance)

end SplayExecutionTranscript

end Splay.Accounting
