import Splay.Accounting.WholeSplayTemporaryFinalSpineBends

namespace Splay.Accounting.WholeSplayTemporaryFinalSpineAttachments

open Splay.Rank
open Splay.Tree.BST
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.WholeSplayTemporaryCoreGeometry
open Splay.Accounting.WholeSplayTemporaryCreationGeometry
open Splay.Accounting.WholeSplayTemporarySpineGeometry

/-!
Canonical realization of the two administrative attachment slots.

Changing the incoming edge of either fixed base child can create at most one
bend.  We filter the endpoint-created identities by those two base deltas and
choose the unique member, when it exists.  This turns the set-level final
spine decomposition into the `Fin 2 → Option CreatedIdentity` interface used
by `FinalSpinePersistence`.
-/

section UniqueOptional

variable {α : Type*}

/-- Choose the unique member of a finite set, returning `none` when empty. -/
noncomputable def optionalOfFinset (elements : Finset α) : Option α :=
  if nonempty : elements.Nonempty then
    some (Classical.choose nonempty)
  else
    none

/-- A value returned by `optionalOfFinset` belongs to the source set. -/
theorem mem_of_optionalOfFinset_eq_some
    {elements : Finset α} {element : α}
    (chosen : optionalOfFinset elements = some element) :
    element ∈ elements := by
  classical
  unfold optionalOfFinset at chosen
  split at chosen
  next nonempty =>
    have equal :
        Classical.choose nonempty = element :=
      Option.some.inj chosen
    rw [← equal]
    exact Classical.choose_spec nonempty
  next empty =>
    contradiction

/--
When the source set has cardinality at most one, every one of its members is
the value returned by `optionalOfFinset`.
-/
theorem optionalOfFinset_eq_some_of_mem
    {elements : Finset α} (card : elements.card ≤ 1)
    {element : α} (member : element ∈ elements) :
    optionalOfFinset elements = some element := by
  classical
  unfold optionalOfFinset
  rw [dif_pos ⟨element, member⟩]
  apply congrArg some
  exact
    Finset.card_le_one_iff.mp card
      (Classical.choose_spec ⟨element, member⟩) member

end UniqueOptional

/--
Endpoint-created identities lying in the possible incoming-edge delta of the
fixed left child.
-/
noncomputable def leftCandidates
    {n key baseLower baseUpper : ℕ}
    {before : BST 0 n} {snapshot : Snapshot n}
    {leftBase : BST baseLower key}
    {rightBase : BST (key + 1) baseUpper}
    {left : BST 0 key}
    {right : BST (key + 1) n}
    (leftSpine : LeftSpine snapshot leftBase left)
    (_rightSpine : RightSpine snapshot rightBase right) :
    Finset
      (CreatedIdentity
        (before := before) (after := .node left right) snapshot) :=
  Finset.univ.filter fun identity =>
    identity.val ∈
      (bendsFrom snapshot leftBase leftSpine.base_le_n
          (WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
            leftSpine)) \
        (bendsFrom snapshot leftBase leftSpine.base_le_n none)

/--
Endpoint-created identities lying in the possible incoming-edge delta of the
fixed right child.
-/
noncomputable def rightCandidates
    {n key baseLower baseUpper : ℕ}
    {before : BST 0 n} {snapshot : Snapshot n}
    {leftBase : BST baseLower key}
    {rightBase : BST (key + 1) baseUpper}
    {left : BST 0 key}
    {right : BST (key + 1) n}
    (_leftSpine : LeftSpine snapshot leftBase left)
    (rightSpine : RightSpine snapshot rightBase right) :
    Finset
      (CreatedIdentity
        (before := before) (after := .node left right) snapshot) :=
  Finset.univ.filter fun identity =>
    identity.val ∈
      (bendsFrom snapshot rightBase rightSpine.base_le_n
          (WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
            rightSpine)) \
        (bendsFrom snapshot rightBase rightSpine.base_le_n none)

@[simp]
theorem mem_leftCandidates_iff
    {n key baseLower baseUpper : ℕ}
    {before : BST 0 n} {snapshot : Snapshot n}
    {leftBase : BST baseLower key}
    {rightBase : BST (key + 1) baseUpper}
    {left : BST 0 key}
    {right : BST (key + 1) n}
    {leftSpine : LeftSpine snapshot leftBase left}
    {rightSpine : RightSpine snapshot rightBase right}
    {identity :
      CreatedIdentity
        (before := before) (after := .node left right) snapshot} :
    identity ∈ leftCandidates leftSpine rightSpine ↔
      identity.val ∈
        (bendsFrom snapshot leftBase leftSpine.base_le_n
            (WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
              leftSpine)) \
          (bendsFrom snapshot leftBase leftSpine.base_le_n none) := by
  classical
  simp [leftCandidates]

@[simp]
theorem mem_rightCandidates_iff
    {n key baseLower baseUpper : ℕ}
    {before : BST 0 n} {snapshot : Snapshot n}
    {leftBase : BST baseLower key}
    {rightBase : BST (key + 1) baseUpper}
    {left : BST 0 key}
    {right : BST (key + 1) n}
    {leftSpine : LeftSpine snapshot leftBase left}
    {rightSpine : RightSpine snapshot rightBase right}
    {identity :
      CreatedIdentity
        (before := before) (after := .node left right) snapshot} :
    identity ∈ rightCandidates leftSpine rightSpine ↔
      identity.val ∈
        (bendsFrom snapshot rightBase rightSpine.base_le_n
            (WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
              rightSpine)) \
          (bendsFrom snapshot rightBase rightSpine.base_le_n none) := by
  classical
  simp [rightCandidates]

/-- The left attachment candidate set contains at most one identity. -/
theorem leftCandidates_card_le_one
    {n key baseLower baseUpper : ℕ}
    {before : BST 0 n} {snapshot : Snapshot n}
    {leftBase : BST baseLower key}
    {rightBase : BST (key + 1) baseUpper}
    {left : BST 0 key}
    {right : BST (key + 1) n}
    (leftSpine : LeftSpine snapshot leftBase left)
    (rightSpine : RightSpine snapshot rightBase right) :
    (leftCandidates
      (before := before) leftSpine rightSpine).card ≤ 1 := by
  classical
  apply Finset.card_le_one_iff.mpr
  intro first second firstMember secondMember
  apply Subtype.ext
  exact
    Finset.card_le_one_iff.mp
      (bendsFrom_sdiff_le_one snapshot leftBase leftSpine.base_le_n _ _)
      (mem_leftCandidates_iff.mp firstMember)
      (mem_leftCandidates_iff.mp secondMember)

/-- The right attachment candidate set contains at most one identity. -/
theorem rightCandidates_card_le_one
    {n key baseLower baseUpper : ℕ}
    {before : BST 0 n} {snapshot : Snapshot n}
    {leftBase : BST baseLower key}
    {rightBase : BST (key + 1) baseUpper}
    {left : BST 0 key}
    {right : BST (key + 1) n}
    (leftSpine : LeftSpine snapshot leftBase left)
    (rightSpine : RightSpine snapshot rightBase right) :
    (rightCandidates
      (before := before) leftSpine rightSpine).card ≤ 1 := by
  classical
  apply Finset.card_le_one_iff.mpr
  intro first second firstMember secondMember
  apply Subtype.ext
  exact
    Finset.card_le_one_iff.mp
      (bendsFrom_sdiff_le_one snapshot rightBase rightSpine.base_le_n _ _)
      (mem_rightCandidates_iff.mp firstMember)
      (mem_rightCandidates_iff.mp secondMember)

/-- Canonical left/right attachment slots of the two final spines. -/
noncomputable def attachment
    {n key baseLower baseUpper : ℕ}
    {before : BST 0 n} {snapshot : Snapshot n}
    {leftBase : BST baseLower key}
    {rightBase : BST (key + 1) baseUpper}
    {left : BST 0 key}
    {right : BST (key + 1) n}
    (leftSpine : LeftSpine snapshot leftBase left)
    (rightSpine : RightSpine snapshot rightBase right) :
    Fin 2 →
      Option
        (CreatedIdentity
          (before := before) (after := .node left right) snapshot) :=
  fun side =>
    if side.val = 0 then
      optionalOfFinset (leftCandidates leftSpine rightSpine)
    else
      optionalOfFinset (rightCandidates leftSpine rightSpine)

/-- Every left candidate is named by slot zero. -/
theorem attachment_zero_eq_some_of_mem_left
    {n key baseLower baseUpper : ℕ}
    {before : BST 0 n} {snapshot : Snapshot n}
    {leftBase : BST baseLower key}
    {rightBase : BST (key + 1) baseUpper}
    {left : BST 0 key}
    {right : BST (key + 1) n}
    (leftSpine : LeftSpine snapshot leftBase left)
    (rightSpine : RightSpine snapshot rightBase right)
    {identity :
      CreatedIdentity
        (before := before) (after := .node left right) snapshot}
    (member : identity ∈ leftCandidates leftSpine rightSpine) :
    attachment leftSpine rightSpine ⟨0, by omega⟩ =
      some identity := by
  simp only [attachment, if_pos]
  exact
    optionalOfFinset_eq_some_of_mem
      (leftCandidates_card_le_one leftSpine rightSpine) member

/-- Every right candidate is named by slot one. -/
theorem attachment_one_eq_some_of_mem_right
    {n key baseLower baseUpper : ℕ}
    {before : BST 0 n} {snapshot : Snapshot n}
    {leftBase : BST baseLower key}
    {rightBase : BST (key + 1) baseUpper}
    {left : BST 0 key}
    {right : BST (key + 1) n}
    (leftSpine : LeftSpine snapshot leftBase left)
    (rightSpine : RightSpine snapshot rightBase right)
    {identity :
      CreatedIdentity
        (before := before) (after := .node left right) snapshot}
    (member : identity ∈ rightCandidates leftSpine rightSpine) :
    attachment leftSpine rightSpine ⟨1, by omega⟩ =
      some identity := by
  simp only [attachment, one_ne_zero, if_false]
  exact
    optionalOfFinset_eq_some_of_mem
      (rightCandidates_card_le_one leftSpine rightSpine) member

/-- Slot zero lies strictly to the left and slot one strictly to the right. -/
theorem attachment_side
    {n key baseLower baseUpper : ℕ}
    {before : BST 0 n} {snapshot : Snapshot n}
    {leftBase : BST baseLower key}
    {rightBase : BST (key + 1) baseUpper}
    {left : BST 0 key}
    {right : BST (key + 1) n}
    (leftSpine : LeftSpine snapshot leftBase left)
    (rightSpine : RightSpine snapshot rightBase right)
    (side : Fin 2)
    (identity :
      CreatedIdentity
        (before := before) (after := .node left right) snapshot)
    (chosen :
      attachment leftSpine rightSpine side = some identity) :
    if side.val = 0 then identity.val.val < key
    else key < identity.val.val := by
  by_cases zero : side.val = 0
  · rw [if_pos zero]
    have choice :
        optionalOfFinset (leftCandidates leftSpine rightSpine) =
          some identity := by
      simpa [attachment, zero] using chosen
    have candidate :=
      mem_leftCandidates_iff.mp
        (mem_of_optionalOfFinset_eq_some choice)
    exact
      (mem_bendsFrom_bounds snapshot leftBase leftSpine.base_le_n _
        (Finset.mem_sdiff.mp candidate).1).2
  · rw [if_neg zero]
    have choice :
        optionalOfFinset (rightCandidates leftSpine rightSpine) =
          some identity := by
      simpa [attachment, zero] using chosen
    have candidate :=
      mem_rightCandidates_iff.mp
        (mem_of_optionalOfFinset_eq_some choice)
    have bounds :=
      mem_bendsFrom_bounds snapshot rightBase rightSpine.base_le_n _
        (Finset.mem_sdiff.mp candidate).1
    omega

end Splay.Accounting.WholeSplayTemporaryFinalSpineAttachments
