import Splay.Accounting.WholeSplayTemporaryCoreClassification

namespace Splay.Accounting.WholeSplayTemporaryCreationGeometry

open Splay.Rank
open Splay.Tree.BST
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.WholeSplayTemporaryPriorityReduction
open Splay.Accounting.WholeSplayTemporaryBoundaryGeometry
open Splay.Accounting.WholeSplayTemporaryCoreGeometry
open Splay.Accounting.WholeSplayTemporaryCoreClassification

/--
An actual zig-zig numbered among the zig-zigs of one chronological
transcript.

Unlike the ordinary list position, this ordinal skips zigs and zig-zags.
The endpoints and contextual depth are retained, so a later persistence
statement names the concrete LL/RR rotation which created its winner bend.
-/
inductive ZigZigOrdinalAt {key lower upper : ℕ} :
    {before after : BST lower upper} →
      {execution : SplayExecution key before after} →
        {kinds : List SplayStepKind} → {zig zigZig zigZag : ℕ} →
          SplayExecutionTranscript key execution kinds zig zigZig zigZag →
            ℕ → BST lower upper → BST lower upper → ℕ → Prop
  | here {before middle after : BST lower upper}
      {kinds : List SplayStepKind} {zig zigZig zigZag depth : ℕ}
      (step : DoubleRotationAt depth key before middle)
      (orientation :
        DoubleOrientationAt true
          (depth := depth) (key := key) before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag) :
      ZigZigOrdinalAt
        (.zigZig step orientation tail tailTranscript)
        0 before middle depth
  | afterZig {before middle after : BST lower upper}
      {kinds : List SplayStepKind} {zig zigZig zigZag ordinal depth : ℕ}
      (head : Zig key before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag)
      {stepBefore stepAfter : BST lower upper}
      (occurrence :
        ZigZigOrdinalAt tailTranscript ordinal
          stepBefore stepAfter depth) :
      ZigZigOrdinalAt
        (.zig head tail tailTranscript)
        ordinal stepBefore stepAfter depth
  | afterZigZig {before middle after : BST lower upper}
      {kinds : List SplayStepKind} {zig zigZig zigZag ordinal depth : ℕ}
      {headDepth : ℕ}
      (head : DoubleRotationAt headDepth key before middle)
      (orientation :
        DoubleOrientationAt true
          (depth := headDepth) (key := key) before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag)
      {stepBefore stepAfter : BST lower upper}
      (occurrence :
        ZigZigOrdinalAt tailTranscript ordinal
          stepBefore stepAfter depth) :
      ZigZigOrdinalAt
        (.zigZig head orientation tail tailTranscript)
        ordinal.succ stepBefore stepAfter depth
  | afterZigZag {before middle after : BST lower upper}
      {kinds : List SplayStepKind} {zig zigZig zigZag ordinal depth : ℕ}
      {headDepth : ℕ}
      (head : DoubleRotationAt headDepth key before middle)
      (orientation :
        DoubleOrientationAt false
          (depth := headDepth) (key := key) before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag)
      {stepBefore stepAfter : BST lower upper}
      (occurrence :
        ZigZigOrdinalAt tailTranscript ordinal
          stepBefore stepAfter depth) :
      ZigZigOrdinalAt
        (.zigZag head orientation tail tailTranscript)
        ordinal stepBefore stepAfter depth

namespace ZigZigOrdinalAt

/-- A numbered occurrence is backed by a genuine contextual LL/RR step. -/
theorem geometry
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {ordinal depth : ℕ} {stepBefore stepAfter : BST lower upper}
    (occurrence :
      ZigZigOrdinalAt transcript ordinal stepBefore stepAfter depth) :
    DoubleRotationAt depth key stepBefore stepAfter ∧
      DoubleOrientationAt true
        (depth := depth) (key := key) stepBefore stepAfter := by
  induction occurrence with
  | here step orientation =>
      exact ⟨step, orientation⟩
  | afterZig _ _ _ _ ih =>
      exact ih
  | afterZigZig _ _ _ _ _ ih =>
      exact ih
  | afterZigZag _ _ _ _ _ ih =>
      exact ih

/-- The zig-zig ordinal is strictly below the recorded zig-zig count. -/
theorem ordinal_lt
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {ordinal depth : ℕ} {stepBefore stepAfter : BST lower upper}
    (occurrence :
      ZigZigOrdinalAt transcript ordinal stepBefore stepAfter depth) :
    ordinal < zigZig := by
  induction occurrence <;> simp_all

/--
Every ordinal below the recorded zig-zig count exposes its concrete
chronological LL/RR rotation.
-/
theorem exists_of_lt
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (ordinal : ℕ) (ordinal_lt : ordinal < zigZig) :
    ∃ stepBefore stepAfter depth,
      ZigZigOrdinalAt transcript ordinal
        stepBefore stepAfter depth := by
  induction transcript generalizing ordinal with
  | done root =>
      omega
  | zig head tail tailTranscript ih =>
      obtain ⟨stepBefore, stepAfter, depth, occurrence⟩ :=
        ih ordinal ordinal_lt
      exact
        ⟨stepBefore, stepAfter, depth,
          .afterZig head tail tailTranscript occurrence⟩
  | zigZig head orientation tail tailTranscript ih =>
      cases ordinal with
      | zero =>
          exact
            ⟨_, _, _, .here head orientation tail tailTranscript⟩
      | succ ordinal =>
          obtain ⟨stepBefore, stepAfter, depth, occurrence⟩ :=
            ih ordinal (by omega)
          exact
            ⟨stepBefore, stepAfter, depth,
              .afterZigZig head orientation tail tailTranscript occurrence⟩
  | zigZag head orientation tail tailTranscript ih =>
      obtain ⟨stepBefore, stepAfter, depth, occurrence⟩ :=
        ih ordinal (by omega)
      exact
        ⟨stepBefore, stepAfter, depth,
          .afterZigZag head orientation tail tailTranscript occurrence⟩

end ZigZigOrdinalAt

/--
A final newly created bend is tied to one concrete zig-zig when that bend
was absent immediately before the LL/RR rotation and present immediately
after it.

Because `identity` belongs to the endpoint set difference, presence in the
final shape and absence from the initial shape are part of its type.  The
existential data below adds the missing causal link to an actual
chronological LL/RR step.  Continuous presence through every intermediate
tree is neither asserted nor needed for the endpoint cardinality argument.
-/
def EndpointPersistentWinnerAt
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    (transcript : SplayExecutionTranscriptWitness execution)
    (snapshot : Snapshot n)
    (identity :
      CreatedIdentity (before := before) (after := after) snapshot)
    (slot : Fin transcript.zigZig) : Prop :=
  ∃ stepBefore stepAfter depth,
    ZigZigOrdinalAt transcript.transcript slot.val
        stepBefore stepAfter depth ∧
      identity.val ∈
        (bends snapshot stepAfter) \ (bends snapshot stepBefore)

/--
The exact final-spine residue for the sharp creation inequality.

`attachment` contains the optional left and right administrative bends, so
there are at most two.  Every other final newly created bend must have been
created by a concrete zig-zig and also be present at the endpoint.  The last
field states the sharp monotone-spine fact: among the nonattachment
identities, one LL/RR rotation has at most one endpoint winner.

An attachment may itself have been created by the same LL/RR step as that
step's winner.  It is therefore deliberately excluded from `winner_unique`;
the endpoint injection below only invokes uniqueness after both identities
have already been proved nonadministrative.

There is deliberately no cardinality premise in this structure.  In
particular, LR/RL steps cannot be sources for nonadministrative bends.
-/
structure FinalSpinePersistence
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    (transcript : SplayExecutionTranscriptWitness execution)
    (snapshot : Snapshot n) : Type where
  attachment :
    Fin 2 →
      Option
        (CreatedIdentity (before := before) (after := after) snapshot)
  attachment_side :
    ∀ (side : Fin 2)
      (identity :
        CreatedIdentity (before := before) (after := after) snapshot),
      attachment side = some identity →
        if side.val = 0 then identity.val.val < key
        else key < identity.val.val
  winner_of_not_attachment :
    ∀ identity :
        CreatedIdentity (before := before) (after := after) snapshot,
      (¬ ∃ side, attachment side = some identity) →
        ∃ slot, EndpointPersistentWinnerAt
          transcript snapshot identity slot
  winner_unique :
    ∀ {slot : Fin transcript.zigZig}
      {first second :
        CreatedIdentity (before := before) (after := after) snapshot},
      (¬ ∃ side, attachment side = some first) →
      (¬ ∃ side, attachment side = some second) →
      EndpointPersistentWinnerAt transcript snapshot first slot →
      EndpointPersistentWinnerAt transcript snapshot second slot →
        first = second

namespace FinalSpinePersistence

/--
The exact final-spine persistence statement implies the sharp endpoint
creation bound: one slot per genuine zig-zig and two attachment slots.
-/
theorem created_le_zigZig_add_two
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {transcript : SplayExecutionTranscriptWitness execution}
    {snapshot : Snapshot n}
    (persistence : FinalSpinePersistence transcript snapshot) :
    ((bends snapshot after) \ (bends snapshot before)).card ≤
      transcript.zigZig + 2 := by
  classical
  let Created :=
    CreatedIdentity (before := before) (after := after) snapshot
  let source :
      Created → Sum (Fin 2) (Fin transcript.zigZig) :=
    fun identity =>
      if attached :
          ∃ side, persistence.attachment side = some identity
      then
        Sum.inl (Classical.choose attached)
      else
        Sum.inr
          (Classical.choose
            (persistence.winner_of_not_attachment identity attached))
  have source_injective : Function.Injective source := by
    intro first second equal
    by_cases firstAttached :
        ∃ side, persistence.attachment side = some first
    · by_cases secondAttached :
          ∃ side, persistence.attachment side = some second
      · have sideEqual :
            Classical.choose firstAttached =
              Classical.choose secondAttached := by
          dsimp only [source] at equal
          rw [dif_pos firstAttached, dif_pos secondAttached] at equal
          exact Sum.inl.inj equal
        have firstAt :=
          Classical.choose_spec firstAttached
        have secondAt :=
          Classical.choose_spec secondAttached
        rw [sideEqual] at firstAt
        rw [firstAt] at secondAt
        exact Option.some.inj secondAt
      · dsimp only [source] at equal
        rw [dif_pos firstAttached, dif_neg secondAttached] at equal
        contradiction
    · by_cases secondAttached :
          ∃ side, persistence.attachment side = some second
      · dsimp only [source] at equal
        rw [dif_neg firstAttached, dif_pos secondAttached] at equal
        contradiction
      · have slotEqual :
            Classical.choose
                (persistence.winner_of_not_attachment
                  first firstAttached) =
              Classical.choose
                (persistence.winner_of_not_attachment
                  second secondAttached) := by
          dsimp only [source] at equal
          rw [dif_neg firstAttached, dif_neg secondAttached] at equal
          exact Sum.inr.inj equal
        apply persistence.winner_unique firstAttached secondAttached
        · exact
            Classical.choose_spec
              (persistence.winner_of_not_attachment
                first firstAttached)
        · rw [slotEqual]
          exact
            Classical.choose_spec
              (persistence.winner_of_not_attachment
                second secondAttached)
  have charged :
      Fintype.card Created ≤
        Fintype.card (Sum (Fin 2) (Fin transcript.zigZig)) :=
    Fintype.card_le_of_injective source source_injective
  simpa only [Created, Fintype.card_coe, Fintype.card_sum,
    Fintype.card_fin, Nat.add_comm] using charged

end FinalSpinePersistence

/--
Canonical temporary-snapshot specialization of the creation reduction.

The selected boundaries are definitionally the minima of the accessed
node's actual child intervals.  Thus the only premise is the precise
final-spine persistence invariant above, not arbitrary ordered boundary
positions and not the desired cardinality inequality itself.
-/
theorem canonical_created_le
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : comparison.HasRoot key.val)
    (persistence :
      let transcript := splayExecutionTranscriptWitness execution
      let selection :=
        KeyFocus.boundaryMinimumSelection
          (Snapshot.ofTree comparison) before key
      FinalSpinePersistence transcript
        (temporarySnapshot comparison key comparisonRoot
          selection.left selection.right selection.ordered)) :
    let transcript := splayExecutionTranscriptWitness execution
    let selection :=
      KeyFocus.boundaryMinimumSelection
        (Snapshot.ofTree comparison) before key
    ((bends
        (temporarySnapshot comparison key comparisonRoot
          selection.left selection.right selection.ordered)
        after) \
      (bends
        (temporarySnapshot comparison key comparisonRoot
          selection.left selection.right selection.ordered)
        before)).card ≤
      transcript.zigZig + 2 := by
  exact FinalSpinePersistence.created_le_zigZig_add_two persistence

end Splay.Accounting.WholeSplayTemporaryCreationGeometry
