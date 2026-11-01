import Splay.Accounting.WholeSplayTemporaryCreationGeometry

namespace Splay.Accounting.WholeSplayTemporaryCreationChronology

open Splay.Rank
open Splay.Tree.BST
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.WholeSplayTemporaryCoreGeometry
open Splay.Accounting.WholeSplayTemporaryCreationGeometry

/--
The first chronological transcript step at which one bend identity is
present.

The relation is proof-relevant but lives in `Prop`, matching the
proof-indexed `SplayExecutionTranscript`.  A `here` constructor records the
exact local set difference.  An `after` constructor may skip an earlier
step only after recording that the identity was absent before that step.
Consequently a proof describes a genuine first appearance, rather than an
arbitrary later re-creation.

The `kind`, local endpoint trees, and optional contextual depth are indices.
Ordinary zigs have depth `none`; both double-rotation classes retain their
actual contextual depth.
-/
inductive FirstCreationAt {n key : ℕ} (snapshot : Snapshot n)
    (identity : Fin n) :
    {before after : BST 0 n} →
      {execution : SplayExecution key before after} →
        {kinds : List SplayStepKind} → {zig zigZig zigZag : ℕ} →
          SplayExecutionTranscript key execution kinds zig zigZig zigZag →
            SplayStepKind → BST 0 n → BST 0 n → Option ℕ → Prop
  | hereZig {before middle after : BST 0 n}
      {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
      (head : Zig key before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag)
      (created :
        identity ∈
          (bends snapshot middle) \ (bends snapshot before)) :
      FirstCreationAt snapshot identity
        (.zig head tail tailTranscript) .zig before middle none
  | hereZigZig {before middle after : BST 0 n}
      {kinds : List SplayStepKind} {zig zigZig zigZag depth : ℕ}
      (head : DoubleRotationAt depth key before middle)
      (orientation :
        DoubleOrientationAt true
          (depth := depth) (key := key) before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag)
      (created :
        identity ∈
          (bends snapshot middle) \ (bends snapshot before)) :
      FirstCreationAt snapshot identity
        (.zigZig head orientation tail tailTranscript)
        .zigZig before middle (some depth)
  | hereZigZag {before middle after : BST 0 n}
      {kinds : List SplayStepKind} {zig zigZig zigZag depth : ℕ}
      (head : DoubleRotationAt depth key before middle)
      (orientation :
        DoubleOrientationAt false
          (depth := depth) (key := key) before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag)
      (created :
        identity ∈
          (bends snapshot middle) \ (bends snapshot before)) :
      FirstCreationAt snapshot identity
        (.zigZag head orientation tail tailTranscript)
        .zigZag before middle (some depth)
  | afterZig {before middle after : BST 0 n}
      {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
      (head : Zig key before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag)
      (absent : identity ∉ bends snapshot before)
      {kind : SplayStepKind} {stepBefore stepAfter : BST 0 n}
      {depth : Option ℕ}
      (occurrence :
        FirstCreationAt snapshot identity tailTranscript kind
          stepBefore stepAfter depth) :
      FirstCreationAt snapshot identity
        (.zig head tail tailTranscript) kind
          stepBefore stepAfter depth
  | afterZigZig {before middle after : BST 0 n}
      {kinds : List SplayStepKind} {zig zigZig zigZag headDepth : ℕ}
      (head : DoubleRotationAt headDepth key before middle)
      (orientation :
        DoubleOrientationAt true
          (depth := headDepth) (key := key) before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag)
      (absent : identity ∉ bends snapshot before)
      {kind : SplayStepKind} {stepBefore stepAfter : BST 0 n}
      {depth : Option ℕ}
      (occurrence :
        FirstCreationAt snapshot identity tailTranscript kind
          stepBefore stepAfter depth) :
      FirstCreationAt snapshot identity
        (.zigZig head orientation tail tailTranscript) kind
          stepBefore stepAfter depth
  | afterZigZag {before middle after : BST 0 n}
      {kinds : List SplayStepKind} {zig zigZig zigZag headDepth : ℕ}
      (head : DoubleRotationAt headDepth key before middle)
      (orientation :
        DoubleOrientationAt false
          (depth := headDepth) (key := key) before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag)
      (absent : identity ∉ bends snapshot before)
      {kind : SplayStepKind} {stepBefore stepAfter : BST 0 n}
      {depth : Option ℕ}
      (occurrence :
        FirstCreationAt snapshot identity tailTranscript kind
          stepBefore stepAfter depth) :
      FirstCreationAt snapshot identity
        (.zigZag head orientation tail tailTranscript) kind
          stepBefore stepAfter depth

namespace FirstCreationAt

/-- The identity is absent at the initial endpoint of the transcript. -/
theorem absent_initial
    {n key : ℕ} {snapshot : Snapshot n} {identity : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {kind : SplayStepKind} {stepBefore stepAfter : BST 0 n}
    {depth : Option ℕ}
    (occurrence :
      FirstCreationAt snapshot identity transcript kind
        stepBefore stepAfter depth) :
    identity ∉ bends snapshot before := by
  induction occurrence with
  | hereZig _ _ _ created
  | hereZigZig _ _ _ _ created
  | hereZigZag _ _ _ _ created =>
      exact (Finset.mem_sdiff.mp created).2
  | afterZig _ _ _ absent _ _
  | afterZigZig _ _ _ _ absent _ _
  | afterZigZag _ _ _ _ absent _ _ =>
      exact absent

/-- The retained local endpoints really create the selected identity. -/
theorem mem_local_sdiff
    {n key : ℕ} {snapshot : Snapshot n} {identity : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {kind : SplayStepKind} {stepBefore stepAfter : BST 0 n}
    {depth : Option ℕ}
    (occurrence :
      FirstCreationAt snapshot identity transcript kind
        stepBefore stepAfter depth) :
    identity ∈
      (bends snapshot stepAfter) \ (bends snapshot stepBefore) := by
  induction occurrence with
  | hereZig _ _ _ created
  | hereZigZig _ _ _ _ created
  | hereZigZag _ _ _ _ created =>
      exact created
  | afterZig _ _ _ _ _ ih
  | afterZigZig _ _ _ _ _ _ ih
  | afterZigZag _ _ _ _ _ _ ih =>
      exact ih

/--
All three source classes retain their exact local geometry.  In the
zig-zig branch, wrapping past an earlier zig-zig increments the existing
zig-zig ordinal and wrapping past either other kind leaves it unchanged.
-/
theorem source_geometry
    {n key : ℕ} {snapshot : Snapshot n} {identity : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {kind : SplayStepKind} {stepBefore stepAfter : BST 0 n}
    {sourceDepth : Option ℕ}
    (occurrence :
      FirstCreationAt snapshot identity transcript kind
        stepBefore stepAfter sourceDepth) :
    (kind = .zig → sourceDepth = none →
      Zig key stepBefore stepAfter) ∧
    (∀ depth, kind = .zigZig → sourceDepth = some depth →
      ∃ ordinal,
        ZigZigOrdinalAt transcript ordinal
          stepBefore stepAfter depth) ∧
    (∀ depth, kind = .zigZag → sourceDepth = some depth →
      DoubleRotationAt depth key stepBefore stepAfter ∧
        DoubleOrientationAt false
          (depth := depth) (key := key)
          stepBefore stepAfter) := by
  induction occurrence with
  | hereZig head =>
      refine ⟨?_, ?_, ?_⟩
      · intro _ _
        exact head
      · intro _ impossible
        contradiction
      · intro _ impossible
        contradiction
  | hereZigZig head orientation tail tailTranscript =>
      refine ⟨?_, ?_, ?_⟩
      · intro impossible
        contradiction
      · intro depth _ depthEqual
        cases depthEqual
        exact
          ⟨0, .here head orientation tail tailTranscript⟩
      · intro _ impossible
        contradiction
  | hereZigZag head orientation =>
      refine ⟨?_, ?_, ?_⟩
      · intro impossible
        contradiction
      · intro _ impossible
        contradiction
      · intro depth _ depthEqual
        cases depthEqual
        exact ⟨head, orientation⟩
  | afterZig head tail tailTranscript _ _ ih =>
      refine ⟨ih.1, ?_, ih.2.2⟩
      intro depth kindEqual depthEqual
      obtain ⟨ordinal, ordinalAt⟩ :=
        ih.2.1 depth kindEqual depthEqual
      exact
        ⟨ordinal,
          .afterZig head tail tailTranscript ordinalAt⟩
  | afterZigZig head orientation tail tailTranscript _ _ ih =>
      refine ⟨ih.1, ?_, ih.2.2⟩
      intro depth kindEqual depthEqual
      obtain ⟨ordinal, ordinalAt⟩ :=
        ih.2.1 depth kindEqual depthEqual
      exact
        ⟨ordinal.succ,
          .afterZigZig head orientation tail tailTranscript ordinalAt⟩
  | afterZigZag head orientation tail tailTranscript _ _ ih =>
      refine ⟨ih.1, ?_, ih.2.2⟩
      intro depth kindEqual depthEqual
      obtain ⟨ordinal, ordinalAt⟩ :=
        ih.2.1 depth kindEqual depthEqual
      exact
        ⟨ordinal,
          .afterZigZag head orientation tail tailTranscript ordinalAt⟩

/-- A zig-classified first creation retains its concrete ordinary rotation. -/
theorem zig_geometry
    {n key : ℕ} {snapshot : Snapshot n} {identity : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {stepBefore stepAfter : BST 0 n}
    (occurrence :
      FirstCreationAt snapshot identity transcript .zig
        stepBefore stepAfter none) :
    Zig key stepBefore stepAfter :=
  occurrence.source_geometry.1 rfl rfl

/--
A zig-zig-classified creation determines the existing zig-zig ordinal
relation at exactly the retained local endpoints and depth.
-/
theorem exists_zigZigOrdinalAt
    {n key : ℕ} {snapshot : Snapshot n} {identity : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {stepBefore stepAfter : BST 0 n} {depth : ℕ}
    (occurrence :
      FirstCreationAt snapshot identity transcript .zigZig
        stepBefore stepAfter (some depth)) :
    ∃ ordinal,
      ZigZigOrdinalAt transcript ordinal
        stepBefore stepAfter depth := by
  exact occurrence.source_geometry.2.1 depth rfl rfl

/--
A zig-zag-classified first creation retains its concrete contextual
double rotation and false orientation.
-/
theorem zigZag_geometry
    {n key : ℕ} {snapshot : Snapshot n} {identity : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {stepBefore stepAfter : BST 0 n} {depth : ℕ}
    (occurrence :
      FirstCreationAt snapshot identity transcript .zigZag
        stepBefore stepAfter (some depth)) :
    DoubleRotationAt depth key stepBefore stepAfter ∧
      DoubleOrientationAt false
        (depth := depth) (key := key) stepBefore stepAfter := by
  exact occurrence.source_geometry.2.2 depth rfl rfl

/-- The indices of an occurrence expose a clean three-way source shape. -/
theorem source_cases
    {n key : ℕ} {snapshot : Snapshot n} {identity : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {kind : SplayStepKind} {stepBefore stepAfter : BST 0 n}
    {depth : Option ℕ}
    (occurrence :
      FirstCreationAt snapshot identity transcript kind
        stepBefore stepAfter depth) :
    (kind = .zig ∧ depth = none) ∨
      (∃ sourceDepth, kind = .zigZig ∧ depth = some sourceDepth) ∨
      (∃ sourceDepth, kind = .zigZag ∧ depth = some sourceDepth) := by
  induction occurrence with
  | hereZig =>
      exact Or.inl ⟨rfl, rfl⟩
  | hereZigZig =>
      exact Or.inr (Or.inl ⟨_, rfl, rfl⟩)
  | hereZigZag =>
      exact Or.inr (Or.inr ⟨_, rfl, rfl⟩)
  | afterZig _ _ _ _ _ ih
  | afterZigZig _ _ _ _ _ _ ih
  | afterZigZag _ _ _ _ _ _ ih =>
      exact ih

end FirstCreationAt

/--
Every endpoint-created identity has a concrete first local creation in the
supplied chronological transcript.
-/
theorem CreatedIdentity.exists_firstCreationAt
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (snapshot : Snapshot n)
    (identity :
      CreatedIdentity (before := before) (after := after) snapshot) :
    ∃ kind stepBefore stepAfter depth,
      FirstCreationAt snapshot identity.val transcript kind
        stepBefore stepAfter depth := by
  cases transcript with
  | done root =>
      exact False.elim
        ((Finset.mem_sdiff.mp identity.property).2
          (Finset.mem_sdiff.mp identity.property).1)
  | @zig lower upper before middle after kinds zig zigZig zigZag
      head tail tailTranscript =>
      have finalPresent :
          identity.val ∈ bends snapshot after :=
        (Finset.mem_sdiff.mp identity.property).1
      have initialAbsent :
          identity.val ∉ bends snapshot before :=
        (Finset.mem_sdiff.mp identity.property).2
      by_cases created :
          identity.val ∈
            (bends snapshot middle) \ (bends snapshot before)
      · exact
          ⟨.zig, before, middle, none,
            .hereZig head tail tailTranscript created⟩
      · have middleAbsent :
            identity.val ∉ bends snapshot middle := by
          intro present
          exact created
            (Finset.mem_sdiff.mpr ⟨present, initialAbsent⟩)
        let tailIdentity :
            CreatedIdentity
              (before := middle) (after := after) snapshot :=
          ⟨identity.val,
            Finset.mem_sdiff.mpr ⟨finalPresent, middleAbsent⟩⟩
        obtain ⟨kind, stepBefore, stepAfter, depth, occurrence⟩ :=
          CreatedIdentity.exists_firstCreationAt
            tailTranscript snapshot tailIdentity
        exact
          ⟨kind, stepBefore, stepAfter, depth,
            .afterZig head tail tailTranscript initialAbsent occurrence⟩
  | @zigZig depth lower upper before middle after kinds zig zigZig zigZag
      head orientation tail tailTranscript =>
      have finalPresent :
          identity.val ∈ bends snapshot after :=
        (Finset.mem_sdiff.mp identity.property).1
      have initialAbsent :
          identity.val ∉ bends snapshot before :=
        (Finset.mem_sdiff.mp identity.property).2
      by_cases created :
          identity.val ∈
            (bends snapshot middle) \ (bends snapshot before)
      · exact
          ⟨.zigZig, before, middle, some depth,
            .hereZigZig head orientation tail tailTranscript created⟩
      · have middleAbsent :
            identity.val ∉ bends snapshot middle := by
          intro present
          exact created
            (Finset.mem_sdiff.mpr ⟨present, initialAbsent⟩)
        let tailIdentity :
            CreatedIdentity
              (before := middle) (after := after) snapshot :=
          ⟨identity.val,
            Finset.mem_sdiff.mpr ⟨finalPresent, middleAbsent⟩⟩
        obtain ⟨kind, stepBefore, stepAfter, sourceDepth, occurrence⟩ :=
          CreatedIdentity.exists_firstCreationAt
            tailTranscript snapshot tailIdentity
        exact
          ⟨kind, stepBefore, stepAfter, sourceDepth,
            .afterZigZig head orientation tail tailTranscript
              initialAbsent occurrence⟩
  | @zigZag depth lower upper before middle after kinds zig zigZig zigZag
      head orientation tail tailTranscript =>
      have finalPresent :
          identity.val ∈ bends snapshot after :=
        (Finset.mem_sdiff.mp identity.property).1
      have initialAbsent :
          identity.val ∉ bends snapshot before :=
        (Finset.mem_sdiff.mp identity.property).2
      by_cases created :
          identity.val ∈
            (bends snapshot middle) \ (bends snapshot before)
      · exact
          ⟨.zigZag, before, middle, some depth,
            .hereZigZag head orientation tail tailTranscript created⟩
      · have middleAbsent :
            identity.val ∉ bends snapshot middle := by
          intro present
          exact created
            (Finset.mem_sdiff.mpr ⟨present, initialAbsent⟩)
        let tailIdentity :
            CreatedIdentity
              (before := middle) (after := after) snapshot :=
          ⟨identity.val,
            Finset.mem_sdiff.mpr ⟨finalPresent, middleAbsent⟩⟩
        obtain ⟨kind, stepBefore, stepAfter, sourceDepth, occurrence⟩ :=
          CreatedIdentity.exists_firstCreationAt
            tailTranscript snapshot tailIdentity
        exact
          ⟨kind, stepBefore, stepAfter, sourceDepth,
            .afterZigZag head orientation tail tailTranscript
              initialAbsent occurrence⟩
termination_by kinds.length

/--
Clean source trichotomy for an endpoint-created identity: its first local
appearance is caused by exactly one of the three transcript step classes.
-/
theorem createdIdentity_firstCreation_cases
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (snapshot : Snapshot n)
    (identity :
      CreatedIdentity (before := before) (after := after) snapshot) :
    (∃ stepBefore stepAfter,
      FirstCreationAt snapshot identity.val transcript .zig
        stepBefore stepAfter none) ∨
    (∃ stepBefore stepAfter depth,
      FirstCreationAt snapshot identity.val transcript .zigZig
        stepBefore stepAfter (some depth)) ∨
    (∃ stepBefore stepAfter depth,
      FirstCreationAt snapshot identity.val transcript .zigZag
        stepBefore stepAfter (some depth)) := by
  obtain ⟨kind, stepBefore, stepAfter, depth, occurrence⟩ :=
    CreatedIdentity.exists_firstCreationAt transcript snapshot identity
  rcases occurrence.source_cases with
      ⟨kindEqual, depthEqual⟩ |
      ⟨⟨sourceDepth, kindEqual, depthEqual⟩ |
        ⟨sourceDepth, kindEqual, depthEqual⟩⟩
  · subst kind
    subst depth
    exact Or.inl ⟨stepBefore, stepAfter, occurrence⟩
  · subst kind
    subst depth
    exact Or.inr (Or.inl
      ⟨stepBefore, stepAfter, sourceDepth, occurrence⟩)
  · subst kind
    subst depth
    exact Or.inr (Or.inr
      ⟨stepBefore, stepAfter, sourceDepth, occurrence⟩)

/--
If the first source is a zig-zig, its computed ordinal is in range and the
endpoint identity satisfies the existing `EndpointPersistentWinnerAt`
predicate at precisely that slot.
-/
theorem FirstCreationAt.exists_endpointPersistentWinnerAt_of_zigZig
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    (transcript : SplayExecutionTranscriptWitness execution)
    (snapshot : Snapshot n)
    (identity :
      CreatedIdentity (before := before) (after := after) snapshot)
    {stepBefore stepAfter : BST 0 n} {depth : ℕ}
    (occurrence :
      FirstCreationAt snapshot identity.val transcript.transcript .zigZig
        stepBefore stepAfter (some depth)) :
    ∃ slot : Fin transcript.zigZig,
      EndpointPersistentWinnerAt transcript snapshot identity slot := by
  obtain ⟨ordinal, ordinalAt⟩ :=
    occurrence.exists_zigZigOrdinalAt
  let slot : Fin transcript.zigZig :=
    ⟨ordinal, ordinalAt.ordinal_lt⟩
  refine ⟨slot, stepBefore, stepAfter, depth, ?_, ?_⟩
  · exact ordinalAt
  · exact occurrence.mem_local_sdiff

end Splay.Accounting.WholeSplayTemporaryCreationChronology
