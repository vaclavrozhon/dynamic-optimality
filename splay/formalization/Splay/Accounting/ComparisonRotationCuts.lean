import Splay.Rank.RotationCutProfile
import Splay.Accounting.BorderCutPreparation
import Splay.Rank.TemporaryBoundarySnapshot

namespace Splay.Tree.BST.RotationCutProfile

open Splay.Rank Splay.Accounting Splay.Accounting.JunctionBendReduction

variable {n depth : ℕ} {before after : BST 0 n} (profile : RotationCutProfile before after depth)

def cutSet : Finset ℕ := (profile.entries.map Prod.fst).toFinset

theorem mem_cutSet {cut : ℕ} : cut ∈ profile.cutSet ↔ ∃ entry ∈ profile.entries, entry.1 = cut := by
  simp [cutSet]

theorem cutSet_card_le : profile.cutSet.card ≤ depth + 2 :=
  (List.toFinset_card_le _).trans (by simpa using profile.length_le)

noncomputable def borderAt (cut : ℕ) (member : cut ∈ profile.cutSet) : External n :=
  let entry := Classical.choose (profile.mem_cutSet.mp member)
  let inEntries := (Classical.choose_spec (profile.mem_cutSet.mp member)).1
  ⟨entry.2, by have bound := (profile.borders entry inEntries).2.1; omega⟩

theorem borderAt_spec (cut : ℕ) (member : cut ∈ profile.cutSet) :
    ((profile.borderAt cut member).val = cut ∨ (profile.borderAt cut member).val + 1 = cut) ∧
      before.externalDepth (profile.borderAt cut member).val ≤ depth + 1 ∧
      after.externalDepth (profile.borderAt cut member).val ≤ depth + 1 := by
  let entry := Classical.choose (profile.mem_cutSet.mp member)
  have chosen := Classical.choose_spec (profile.mem_cutSet.mp member)
  have spec := profile.borders entry chosen.1
  change (entry.2 = cut ∨ entry.2 + 1 = cut) ∧ before.externalDepth entry.2 ≤ depth + 1 ∧ after.externalDepth entry.2 ≤ depth + 1
  rw [← chosen.2]
  exact spec.2.2

noncomputable def border (cut : ℕ) : External n :=
  if member : cut ∈ profile.cutSet then profile.borderAt cut member else ⟨0, by omega⟩

theorem border_spec (cut : ℕ) (member : cut ∈ profile.cutSet) :
    ((profile.border cut).val = cut ∨ (profile.border cut).val + 1 = cut) ∧
      before.externalDepth (profile.border cut).val ≤ depth + 1 ∧
      after.externalDepth (profile.border cut).val ≤ depth + 1 := by
  simpa [border, member] using profile.borderAt_spec cut member

/-- Equal cells imply equal actual signed changes of the doubled numeric
rank function used by the complete article request construction. -/
theorem doubled_shift_eq {first second : External n} (same : SameCutCell profile.cutSet first second) :
    ((Snapshot.ofTree after).withTruePriority.rank first : ℤ) - (Snapshot.ofTree before).withTruePriority.rank first =
      ((Snapshot.ofTree after).withTruePriority.rank second : ℤ) - (Snapshot.ofTree before).withTruePriority.rank second := by
  have equal := profile.uniform first.val second.val (fun entry member =>
    same entry.1 (profile.mem_cutSet.mpr ⟨entry, member, rfl⟩))
  change ((2 * after.externalDepth first.val : ℕ) : ℤ) - (2 * before.externalDepth first.val : ℕ) =
    ((2 * after.externalDepth second.val : ℕ) : ℤ) - (2 * before.externalDepth second.val : ℕ)
  push_cast
  omega

/-- The actual owner support for all rank-update cuts has constant size
when comparison rotations occur at bounded depth. -/
theorem before_borderOwners_card_le :
    (borderCutOwners (Snapshot.ofTree before).withTruePriority profile.cutSet profile.border).card ≤
      (depth + 2) * (2 * (depth + 1) + 1) := by
  have bound := borderCutOwners_card_le (Snapshot.ofTree before).withTruePriority profile.cutSet profile.border
    (2 * (depth + 1)) (by
      intro cut member
      have rankBound := (profile.border_spec cut member).2.1
      change 2 * before.externalDepth (profile.border cut).val ≤ 2 * (depth + 1)
      omega)
  exact bound.trans (Nat.mul_le_mul_right _ profile.cutSet_card_le)

end Splay.Tree.BST.RotationCutProfile
