import HeapSubtreeGeometry
import Splay.Rank.RotationCutProfile
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Concrete rank-sector preparation for a comparator rotation. The existing
rotation cut profile has at most depth+2 cuts, each adjacent to a record of
rank at most depth+1. Actual canonical heap owners affected at a cut lie
on that border record's heap-ancestor path. Thus the census is quadratic
in rotation depth, which is constant in the restricted comparator normal
form. The paper's sharper four-cut census is not needed by this module.
-/

namespace GreedyMerge.AdminCuts

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open HeapGeometry
open scoped BigOperators

noncomputable def border {n depth : ℕ} {before after : BST 0 n}
    (_profile : RotationCutProfile before after depth) (entry : ℕ × ℕ) : External n :=
  if bound : entry.2 < 2 * n + 1 then ⟨entry.2, bound⟩ else ⟨0, by omega⟩

theorem border_spec {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (entry : ℕ × ℕ)
    (member : entry ∈ profile.entries) :
    (border profile entry).val = entry.2 ∧
    (entry.2 = entry.1 ∨ entry.2 + 1 = entry.1) ∧
    (Snapshot.ofTree before).rank (border profile entry) ≤ depth + 1 := by
  have spec := profile.borders entry member
  have bound : entry.2 < 2 * n + 1 := by omega
  refine ⟨by simp only [border, dif_pos bound], spec.2.2.1, ?_⟩
  change before.externalDepth (border profile entry).val ≤ depth + 1
  simpa only [border, dif_pos bound] using spec.2.2.2.1

/-- The exact census counts cut/owner incidences, retaining multiplicity
when one owner needs preparation at more than one cut. -/
noncomputable def cutOwnerIncidences {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n) :
    Finset ((ℕ × ℕ) × External n) := by
  classical
  exact profile.entries.toFinset.biUnion fun entry =>
    (Ancestors (Snapshot.ofTree before) tree (border profile entry)).image fun owner => (entry, owner)

theorem cut_owner_incidence_card {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n) :
    (cutOwnerIncidences profile tree).card ≤ (depth + 2) ^ 2 := by
  classical
  unfold cutOwnerIncidences
  apply le_trans (Finset.card_biUnion_le)
  calc
    (∑ entry ∈ profile.entries.toFinset,
      ((Ancestors (Snapshot.ofTree before) tree (border profile entry)).image
        fun owner => (entry, owner)).card) ≤
      ∑ _entry ∈ profile.entries.toFinset, (depth + 2) := by
      apply Finset.sum_le_sum
      intro entry member
      have bound := (border_spec profile entry (List.mem_toFinset.mp member)).2.2
      have ancestors := ancestor_card_le_rank_succ (Snapshot.ofTree before) tree (border profile entry)
      exact (Finset.card_image_le).trans (by omega)
    _ = profile.entries.toFinset.card * (depth + 2) := by simp
    _ ≤ (depth + 2) * (depth + 2) := by
      apply Nat.mul_le_mul_right
      exact (List.toFinset_card_le _).trans profile.length_le
    _ = (depth + 2) ^ 2 := by rw [pow_two]

/-- Integer positions straddling a cut also straddle either adjacent border. -/
theorem border_between {first second cut border : ℕ}
    (adjacent : border = cut ∨ border + 1 = cut)
    (different : ¬ (first < cut ↔ second < cut)) :
    (first ≤ border ∧ border ≤ second) ∨ (second ≤ border ∧ border ≤ first) := by
  omega

theorem parent_cut_supported {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (entry : ℕ × ℕ) (member : entry ∈ profile.entries)
    {child owner : External n}
    (parent : canonicalParent (Snapshot.ofTree before) tree child = some owner)
    (different : ¬ (owner.val < entry.1 ↔ child.val < entry.1)) :
    (entry, owner) ∈ cutOwnerIncidences profile tree := by
  classical
  have spec := border_spec profile entry member
  have between := border_between spec.2.1 different
  have path : Ancestor (canonicalParent (Snapshot.ofTree before) tree) owner (border profile entry) := by
    apply parent_spans_ancestor (Snapshot.ofTree before) tree parent
    simpa only [Fin.le_def, spec.1] using between
  apply Finset.mem_biUnion.mpr
  refine ⟨entry, List.mem_toFinset.mpr member, Finset.mem_image.mpr ?_⟩
  exact ⟨owner, Finset.mem_filter.mpr ⟨Finset.mem_univ _, path⟩, rfl⟩

theorem children_cut_supported {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (entry : ℕ × ℕ) (member : entry ∈ profile.entries)
    {first second owner : External n}
    (firstParent : canonicalParent (Snapshot.ofTree before) tree first = some owner)
    (secondParent : canonicalParent (Snapshot.ofTree before) tree second = some owner)
    (different : ¬ (first.val < entry.1 ↔ second.val < entry.1)) :
    (entry, owner) ∈ cutOwnerIncidences profile tree := by
  classical
  have spec := border_spec profile entry member
  have between := border_between spec.2.1 different
  have path : Ancestor (canonicalParent (Snapshot.ofTree before) tree) owner (border profile entry) := by
    rcases between with h | h
    · apply children_span_ancestor (Snapshot.ofTree before) tree firstParent secondParent
      · simpa only [Fin.le_def, spec.1] using h.1
      · simpa only [Fin.le_def, spec.1] using h.2
    · apply children_span_ancestor (Snapshot.ofTree before) tree secondParent firstParent
      · simpa only [Fin.le_def, spec.1] using h.1
      · simpa only [Fin.le_def, spec.1] using h.2
  apply Finset.mem_biUnion.mpr
  refine ⟨entry, List.mem_toFinset.mpr member, Finset.mem_image.mpr ?_⟩
  exact ⟨owner, Finset.mem_filter.mpr ⟨Finset.mem_univ _, path⟩, rfl⟩

/-- Different actual rank shifts must be separated by a profile cut. -/
theorem unequal_shift_cut {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (first second : External n)
    (different : (after.externalDepth first.val : ℤ) - before.externalDepth first.val ≠
      (after.externalDepth second.val : ℤ) - before.externalDepth second.val) :
    ∃ entry ∈ profile.entries, ¬ (first.val < entry.1 ↔ second.val < entry.1) := by
  classical
  by_contra none
  push Not at none
  exact different (profile.uniform first.val second.val none)

/-- Any parent/child rank-shift mismatch belongs to the explicit small
cut-owner census. -/
theorem parent_shift_supported {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    {child owner : External n}
    (parent : canonicalParent (Snapshot.ofTree before) tree child = some owner)
    (different : (after.externalDepth owner.val : ℤ) - before.externalDepth owner.val ≠
      (after.externalDepth child.val : ℤ) - before.externalDepth child.val) :
    ∃ entry, (entry, owner) ∈ cutOwnerIncidences profile tree := by
  obtain ⟨entry, member, split⟩ := unequal_shift_cut profile owner child different
  exact ⟨entry, parent_cut_supported profile tree entry member parent split⟩

end GreedyMerge.AdminCuts

#print axioms GreedyMerge.AdminCuts.cut_owner_incidence_card
#print axioms GreedyMerge.AdminCuts.parent_shift_supported
