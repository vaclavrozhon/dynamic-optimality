import Splay.Accounting.WholeSplayTemporaryCreationGeometry

namespace Splay.Accounting.WholeSplayTemporaryCreationSetDecomposition

open Splay.Rank
open Splay.Tree.BST
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.WholeSplayTemporaryCoreGeometry
open Splay.Accounting.WholeSplayTemporaryCreationGeometry

/--
Endpoint-created identities which were also created locally by one numbered
zig-zig occurrence.

The endpoint condition is carried by `CreatedIdentity`; the filter adds the
proof-relevant chronological occurrence and its local set difference.
-/
noncomputable def persistentCreatedAt
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    (transcript : SplayExecutionTranscriptWitness execution)
    (snapshot : Snapshot n)
    (slot : Fin transcript.zigZig) :
    Finset
      (CreatedIdentity (before := before) (after := after) snapshot) :=
  by
    classical
    exact Finset.univ.filter fun identity =>
      EndpointPersistentWinnerAt transcript snapshot identity slot

@[simp]
theorem mem_persistentCreatedAt_iff
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {transcript : SplayExecutionTranscriptWitness execution}
    {snapshot : Snapshot n}
    {slot : Fin transcript.zigZig}
    {identity :
      CreatedIdentity (before := before) (after := after) snapshot} :
    identity ∈ persistentCreatedAt transcript snapshot slot ↔
      EndpointPersistentWinnerAt transcript snapshot identity slot := by
  classical
  simp [persistentCreatedAt]

/--
The finite image of the two optional attachment slots.

Using a membership filter rather than `Option.toFinset` keeps the definition
uniform when the two slots happen to name the same identity.
-/
noncomputable def attachmentSet
    {n : ℕ} {before after : BST 0 n}
    {snapshot : Snapshot n}
    (attachment :
      Fin 2 →
        Option
          (CreatedIdentity
            (before := before) (after := after) snapshot)) :
    Finset
      (CreatedIdentity (before := before) (after := after) snapshot) :=
  Finset.univ.filter fun identity =>
    ∃ side, attachment side = some identity

@[simp]
theorem mem_attachmentSet_iff
    {n : ℕ} {before after : BST 0 n}
    {snapshot : Snapshot n}
    {attachment :
      Fin 2 →
        Option
          (CreatedIdentity
            (before := before) (after := after) snapshot)}
    {identity :
      CreatedIdentity (before := before) (after := after) snapshot} :
    identity ∈ attachmentSet attachment ↔
      ∃ side, attachment side = some identity := by
  classical
  simp [attachmentSet]

/-- Two optional attachment slots name at most two distinct identities. -/
theorem attachmentSet_card_le_two
    {n : ℕ} {before after : BST 0 n}
    {snapshot : Snapshot n}
    (attachment :
      Fin 2 →
        Option
          (CreatedIdentity
            (before := before) (after := after) snapshot)) :
    (attachmentSet attachment).card ≤ 2 := by
  classical
  let sideOf : ↥(attachmentSet attachment) → Fin 2 :=
    fun identity =>
      Classical.choose
        ((mem_attachmentSet_iff).mp identity.property)
  have sideOf_injective : Function.Injective sideOf := by
    intro first second equal
    apply Subtype.ext
    have firstAt :
        attachment (sideOf first) = some first.val :=
      Classical.choose_spec
        ((mem_attachmentSet_iff).mp first.property)
    have secondAt :
        attachment (sideOf second) = some second.val :=
      Classical.choose_spec
        ((mem_attachmentSet_iff).mp second.property)
    rw [equal] at firstAt
    rw [firstAt] at secondAt
    exact Option.some.inj secondAt
  simpa only [Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_le_of_injective sideOf sideOf_injective

/--
Pure finite-set form of the corrected final-spine creation residue.

After deleting the image of the two attachment slots:

* every endpoint-created identity is covered by the local creation set of
  some chronological zig-zig slot;
* each slot covers at most one remaining endpoint identity.

The second clause deliberately removes the attachment set before asserting
uniqueness.  A single LL/RR rotation may create both its genuine winner and
one administrative attachment bend.
-/
structure FinalSpineSetDecomposition
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
  cover :
    ((Finset.univ :
        Finset
          (CreatedIdentity
            (before := before) (after := after) snapshot)) \
      attachmentSet attachment) ⊆
      (Finset.univ : Finset (Fin transcript.zigZig)).biUnion
        (fun slot =>
          persistentCreatedAt transcript snapshot slot \
            attachmentSet attachment)
  one_per_slot :
    ∀ slot : Fin transcript.zigZig,
      (persistentCreatedAt transcript snapshot slot \
        attachmentSet attachment).card ≤ 1

namespace FinalSpineSetDecomposition

/--
Convert the finite-set cover into the proof-relevant source maps expected by
`FinalSpinePersistence`.
-/
noncomputable def toFinalSpinePersistence
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {transcript : SplayExecutionTranscriptWitness execution}
    {snapshot : Snapshot n}
    (decomposition :
      FinalSpineSetDecomposition transcript snapshot) :
    FinalSpinePersistence transcript snapshot := by
  classical
  refine
    { attachment := decomposition.attachment
      attachment_side := decomposition.attachment_side
      winner_of_not_attachment := ?_
      winner_unique := ?_ }
  · intro identity notAttachment
    have outside :
        identity ∈
          (Finset.univ :
              Finset
                (CreatedIdentity
                  (before := before) (after := after) snapshot)) \
            attachmentSet decomposition.attachment := by
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, by
          simpa only [mem_attachmentSet_iff] using notAttachment⟩
    have covered := decomposition.cover outside
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at covered
    obtain ⟨slot, member⟩ := covered
    refine ⟨slot, ?_⟩
    exact mem_persistentCreatedAt_iff.mp
      (Finset.mem_sdiff.mp member).1
  · intro slot first second firstNotAttachment secondNotAttachment
      firstWinner secondWinner
    have firstMember :
        first ∈
          persistentCreatedAt transcript snapshot slot \
            attachmentSet decomposition.attachment := by
      exact Finset.mem_sdiff.mpr
        ⟨mem_persistentCreatedAt_iff.mpr firstWinner, by
          simpa only [mem_attachmentSet_iff] using firstNotAttachment⟩
    have secondMember :
        second ∈
          persistentCreatedAt transcript snapshot slot \
            attachmentSet decomposition.attachment := by
      exact Finset.mem_sdiff.mpr
        ⟨mem_persistentCreatedAt_iff.mpr secondWinner, by
          simpa only [mem_attachmentSet_iff] using secondNotAttachment⟩
    exact
      Finset.card_le_one_iff.mp
        (decomposition.one_per_slot slot)
        firstMember secondMember

/-- The set decomposition yields the sharp endpoint creation inequality. -/
theorem created_le_zigZig_add_two
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {transcript : SplayExecutionTranscriptWitness execution}
    {snapshot : Snapshot n}
    (decomposition :
      FinalSpineSetDecomposition transcript snapshot) :
    ((bends snapshot after) \ (bends snapshot before)).card ≤
      transcript.zigZig + 2 :=
  decomposition.toFinalSpinePersistence.created_le_zigZig_add_two

end FinalSpineSetDecomposition

end Splay.Accounting.WholeSplayTemporaryCreationSetDecomposition
