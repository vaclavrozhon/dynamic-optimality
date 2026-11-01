import Splay.Accounting.SplayBendTranscript

namespace Splay.Accounting

open Splay.Accounting.LocalBendGeometry
open Splay.Rank
open Splay.Tree.BST

namespace SplayExecutionFiniteBendWitness

/--
One complete-access action that preserves the multiplicity of chronological
bend events.

Unlike `wholeSplayAction`, this does not collapse creation and removal to the
endpoint set differences.  A bend removed by one substep and recreated by a
later substep is counted once in each field, exactly as required by the
potential telescope.
-/
def chronologicalAction
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript) :
    BendAction where
  kind := .splay
  zigZig := zigZig
  zigZag := zigZag
  created := totalBendsCreated witness.actions
  removed := totalBendsRemoved witness.actions

/--
The only complete-splay estimate still required after chronological removal
events are retained: all creation occurrences are paid by one administrative
allowance plus one unit per zig-zig.
-/
def WholeSplayCreationLaw
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript) : Prop :=
  totalBendsCreated witness.actions ≤ zigZig + constants.splay

/--
The exact finite substep history telescopes to a singleton numerical history
for the chronological complete-access action.
-/
theorem chronologicalAction_history
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript) :
    BendHistory (bends snapshot before).card
      [witness.chronologicalAction] (bends snapshot after).card := by
  refine .cons witness.chronologicalAction [] ?_ (.nil _)
  simpa [chronologicalAction, totalBendsCreated, totalBendsRemoved] using
    witness.history.toBendHistory.telescope

/--
Chronological removals compose without any endpoint-persistence premise.
This is exactly why the complete action must retain event multiplicity.
-/
theorem zigZag_le_chronological_removed
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript) :
    zigZag ≤ witness.chronologicalAction.removed := by
  change zigZag ≤ totalBendsRemoved witness.actions
  calc
    zigZag = totalActionZigZag witness.actions :=
      witness.zigZag_eq.symm
    _ ≤ totalBendsRemoved witness.actions :=
      totalActionZigZag_le_totalBendsRemoved
        witness.all_actions_locallySound

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

/-- Every chronological action in a splay transcript is a splay action. -/
theorem all_actions_kind_eq_splay
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript) :
    ∀ action ∈ witness.actions, action.kind = .splay :=
  all_right_of_forall₂
    (witness.alignment.imp (fun _ _ matched => matched.1))

private theorem comparisonActions_eq_zero_of_all_splay
    {actions : List BendAction}
    (allSplay : ∀ action ∈ actions, action.kind = .splay) :
    totalComparisonRotationActions actions = 0 := by
  induction actions with
  | nil =>
      rfl
  | cons action actions ih =>
      have head := allSplay action (by simp)
      have tail :
          ∀ tailAction ∈ actions, tailAction.kind = .splay := by
        intro tailAction member
        exact allSplay tailAction (by simp [member])
      simp [totalComparisonRotationActions, head, ih tail]

/-- No comparison action is hidden inside a chronological splay history. -/
@[simp]
theorem comparisonActions_eq_zero
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript) :
    totalComparisonRotationActions witness.actions = 0 :=
  comparisonActions_eq_zero_of_all_splay witness.all_actions_kind_eq_splay

/--
The currently unconditional creation fallback pays the administrative
allowance once per chronological substep.
-/
theorem created_le_zigZig_add_allowance_mul_steps
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript) :
    totalBendsCreated witness.actions ≤
      zigZig + constants.splay * kinds.length := by
  have bound :=
    totalBendsCreated_le witness.all_actions_locallySound
  rw [witness.zigZig_eq, witness.splayActions_eq,
    witness.comparisonActions_eq_zero] at bound
  simpa using bound

/--
A creation law makes the chronological complete-access action locally sound;
the zig-zag removal half is already automatic.
-/
theorem chronologicalAction_locallySound
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript)
    (creation : WholeSplayCreationLaw witness) :
    witness.chronologicalAction.LocallySound constants := by
  exact ⟨witness.zigZag_le_chronological_removed, creation⟩

/-- Ordinal names for all chronological bend-creation occurrences. -/
abbrev CreationOccurrence
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript) :=
  Fin (totalBendsCreated witness.actions)

/--
A sufficient charging witness for fixed-snapshot chronological creation.

At most `budget` chronological creation occurrences are administrative.
Every other occurrence injects into a genuine zig-zig, expressing that each
zig-zig pays for at most one non-administrative creation.  The budget is
explicit because a fixed value seven is false for arbitrary comparison-root
snapshots.

The manuscript's temporary-neighbor-rank route may instead construct a
different aggregate numerical action.  It is not claimed here that such a
route implies this stronger fixed-snapshot occurrence charging statement.
-/
structure WholeSplayCreationCharging
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript)
    (budget : ℕ) where
  administrative : Finset (CreationOccurrence witness)
  administrative_card_le :
    administrative.card ≤ budget
  zigZigCharge :
    ↥((Finset.univ : Finset (CreationOccurrence witness)) \
      administrative) → Fin zigZig
  zigZigCharge_injective :
    Function.Injective zigZigCharge

namespace WholeSplayCreationCharging

/-- The charging witness gives the sharp raw bound for its stated budget. -/
theorem total_created_le
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript}
    {budget : ℕ}
    (charging : WholeSplayCreationCharging witness budget) :
    totalBendsCreated witness.actions ≤ zigZig + budget := by
  have chargedBound :
      totalBendsCreated witness.actions ≤
        zigZig + charging.administrative.card := by
    simpa using
      Fintype.card_le_of_injective
        charging.zigZigCharge charging.zigZigCharge_injective
  have administrativeBound := charging.administrative_card_le
  omega

/-- A certified administrative budget fits any larger advertised allowance. -/
theorem creationLaw
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript}
    {budget : ℕ}
    (charging : WholeSplayCreationCharging witness budget)
    (splayAllowance : budget ≤ constants.splay) :
    WholeSplayCreationLaw witness :=
  charging.total_created_le.trans
    (Nat.add_le_add_left splayAllowance zigZig)

/--
A charging witness whose budget fits the advertised splay allowance packages
the complete chronological action as locally sound.
-/
theorem chronologicalAction_locallySound
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript}
    {budget : ℕ}
    (charging : WholeSplayCreationCharging witness budget)
    (splayAllowance : budget ≤ constants.splay) :
    witness.chronologicalAction.LocallySound constants :=
  witness.chronologicalAction_locallySound
    (charging.creationLaw splayAllowance)

end WholeSplayCreationCharging

private theorem total_created_le_seven_mul_length_aux
    {actions : List BendAction}
    (eachCreated :
      ∀ action ∈ actions, action.created ≤ 7) :
    totalBendsCreated actions ≤ 7 * actions.length := by
  induction actions with
  | nil =>
      rfl
  | cons action actions ih =>
      have head := eachCreated action (by simp)
      have tail :
          ∀ tailAction ∈ actions, tailAction.created ≤ 7 := by
        intro tailAction member
        exact eachCreated tailAction (by simp [member])
      simp only [totalBendsCreated, List.length_cons]
      have tailBound := ih tail
      omega

/--
Unconditional finite-transcript fallback: each chronological splay substep
creates at most seven bends.

This is deliberately a per-step bound.  It does not assert that seven is a
uniform administrative allowance for a whole access.
-/
theorem total_created_le_seven_mul_length
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript) :
    totalBendsCreated witness.actions ≤ 7 * kinds.length := by
  rw [← witness.actions_length_eq]
  exact total_created_le_seven_mul_length_aux
    witness.each_created_le_seven

/--
The same unconditional fallback with the nonnegative zig-zig term exposed,
matching the shape expected by later bounded-instance certificates.
-/
theorem total_created_le_zigZig_add_seven_mul_length
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript) :
    totalBendsCreated witness.actions ≤ zigZig + 7 * kinds.length :=
  witness.total_created_le_seven_mul_length.trans (Nat.le_add_left _ _)

/-- A transcript with at most one substep creates at most seven bends. -/
theorem total_created_le_seven_of_length_le_one
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript)
    (short : kinds.length ≤ 1) :
    totalBendsCreated witness.actions ≤ 7 := by
  have bound := witness.total_created_le_seven_mul_length
  omega

/-- Short splays satisfy the desired once-per-access creation law outright. -/
theorem creationLaw_of_length_le_one
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript)
    (short : kinds.length ≤ 1)
    (splayAllowance : 7 ≤ constants.splay) :
    WholeSplayCreationLaw witness := by
  have created := witness.total_created_le_seven_of_length_le_one short
  exact created.trans (by omega)

/-- Consequently every zero- or one-step chronological action is sound. -/
theorem chronologicalAction_locallySound_of_length_le_one
    {constants : BendConstants}
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {snapshot : Snapshot n}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    (witness :
      SplayExecutionFiniteBendWitness constants snapshot transcript)
    (short : kinds.length ≤ 1)
    (splayAllowance : 7 ≤ constants.splay) :
    witness.chronologicalAction.LocallySound constants :=
  witness.chronologicalAction_locallySound
    (witness.creationLaw_of_length_le_one short splayAllowance)

end SplayExecutionFiniteBendWitness

end Splay.Accounting
