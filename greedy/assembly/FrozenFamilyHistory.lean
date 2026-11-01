import OrderedBlockPrimitives
import BlockLifetime

/-!
The actual immutable Entry records in spatial blocks project to the
join-ticket sets used by the finite accounting histories. Splits, deletion,
rebasing and whole-block permutations preserve this projection literally.
The retrospectively completed prefix before conversion is handled below;
it is not the growing family's current member set.
-/

namespace GreedyMerge.FrozenHistory

open OrderedBlocks GreedyForest

def joins (block : Frozen) : Finset ℕ :=
  (block.members.map Primitives.Entry.joined).toFinset

noncomputable def familyView (family : ℕ) (blocks : List Frozen) : Family ℕ :=
  ((blocks.filter (fun block => block.family = family)).map joins).toFinset

theorem mem_familyView {family : ℕ} {blocks : List Frozen} {members : Finset ℕ} :
    members ∈ familyView family blocks ↔
      ∃ block ∈ blocks, block.family = family ∧ joins block = members := by
  simp only [familyView, List.mem_toFinset, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  aesop

theorem descends_joins {after before : Frozen} (descends : Descends after before) :
    joins after ⊆ joins before := by
  intro joined member
  obtain ⟨entry, present, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  exact List.mem_toFinset.mpr (List.mem_map.mpr
    ⟨entry, descends.2.2.subset present, rfl⟩)

/-- The abstract refinement relation is derived from actual Entry
subsequences with preserved family identity. -/
theorem family_refines (family : ℕ) (before after : List Frozen)
    (descendants : ∀ block ∈ after, ∃ old ∈ before, Descends block old) :
    Refines (familyView family after) (familyView family before) := by
  intro members present
  obtain ⟨block, member, same, rfl⟩ := mem_familyView.mp present
  obtain ⟨old, oldMember, descends⟩ := descendants block member
  exact ⟨joins old, mem_familyView.mpr ⟨old, oldMember, descends.1.symm.trans same, rfl⟩,
    descends_joins descends⟩

theorem replacement_refines (family : ℕ) (pre post pieces : List Frozen) (focus : Frozen)
    (descendants : ∀ piece ∈ pieces, Descends piece focus) :
    Refines (familyView family (pre ++ pieces ++ post))
      (familyView family (pre ++ [focus] ++ post)) := by
  apply family_refines
  intro block member
  simp only [List.mem_append] at member
  rcases member with (left | middle) | right
  · exact ⟨block, by simp [left], descends_refl block⟩
  · exact ⟨focus, by simp, descendants block middle⟩
  · exact ⟨block, by simp [right], descends_refl block⟩

theorem split_family_refines (family leftId rightId cut : ℕ)
    (pre post : List Frozen) (focus : Frozen) :
    Refines (familyView family (pre ++ splitFresh leftId rightId focus cut ++ post))
      (familyView family (pre ++ [focus] ++ post)) := by
  apply replacement_refines
  intro piece member
  simp only [splitFresh, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨rfl, rfl, List.take_sublist _ _⟩
  · exact ⟨rfl, rfl, List.drop_sublist _ _⟩

theorem erase_family_refines (family key : ℕ) (pre post : List Frozen) (focus : Frozen) :
    Refines (familyView family (pre ++ [eraseMember key focus] ++ post))
      (familyView family (pre ++ [focus] ++ post)) := by
  apply replacement_refines
  intro piece member
  have same := List.mem_singleton.mp member
  subst piece
  exact erase_descends focus key

theorem rebase_family_refines (family : ℕ) (base : ℕ)
    (pre post : List Frozen) (focus : Frozen) :
    Refines (familyView family (pre ++ [rebase base focus] ++ post))
      (familyView family (pre ++ [focus] ++ post)) := by
  apply replacement_refines
  intro piece member
  have same := List.mem_singleton.mp member
  subst piece
  exact rebase_descends focus base

/-- Moving complete blocks between owner lists, or reordering the global
enumeration of owners, does not alter any family of historical tickets. -/
theorem familyView_perm (family : ℕ) {before after : List Frozen}
    (permutation : after.Perm before) : familyView family after = familyView family before := by
  ext members
  simp only [mem_familyView]
  constructor <;> rintro ⟨block, member, same, equal⟩
  · exact ⟨block, permutation.mem_iff.mp member, same, equal⟩
  · exact ⟨block, permutation.mem_iff.mpr member, same, equal⟩

theorem ordered_partitioned (blocks : Family ℕ) (ordered : OrderedFamily blocks) :
    Partitioned blocks := by
  intro first firstMember second secondMember ticket firstContains secondContains
  by_contra different
  rcases ordered first firstMember second secondMember different with forward | backward
  · exact lt_irrefl ticket (forward ticket firstContains ticket secondContains)
  · exact lt_irrefl ticket (backward ticket secondContains ticket firstContains)

/-- A split/delete replaces one historical fragment by ordered subsets;
all other fragments retain their order. Empty fragments cause no problem. -/
theorem ordered_replace (before pieces : Family ℕ) (focus : Finset ℕ)
    (focusMember : focus ∈ before) (ordered : OrderedFamily before)
    (subsets : ∀ piece ∈ pieces, piece ⊆ focus)
    (pieceOrder : OrderedFamily pieces) :
    OrderedFamily (before.erase focus ∪ pieces) := by
  intro first firstMember second secondMember different
  rcases Finset.mem_union.mp firstMember with oldFirst | newFirst
  · have firstOld := (Finset.mem_erase.mp oldFirst).2
    have firstNot := (Finset.mem_erase.mp oldFirst).1
    rcases Finset.mem_union.mp secondMember with oldSecond | newSecond
    · exact ordered first firstOld second (Finset.mem_erase.mp oldSecond).2 different
    · rcases ordered first firstOld focus focusMember firstNot with forward | backward
      · exact Or.inl (fun x hx y hy => forward x hx y (subsets second newSecond hy))
      · exact Or.inr (fun x hx y hy => backward x (subsets second newSecond hx) y hy)
  · rcases Finset.mem_union.mp secondMember with oldSecond | newSecond
    · have secondOld := (Finset.mem_erase.mp oldSecond).2
      have secondNot := (Finset.mem_erase.mp oldSecond).1
      rcases ordered second secondOld focus focusMember secondNot with forward | backward
      · exact Or.inr (fun x hx y hy => forward x hx y (subsets first newFirst hy))
      · exact Or.inl (fun x hx y hy => backward x (subsets first newFirst hx) y hy)
    · exact pieceOrder first newFirst second newSecond different

/-- Before conversion use all eventual family tickets, including future
entries. At and after conversion use actual shrinking fragments. -/
def completed (allTickets : Finset ℕ) (conversion : ℕ)
    (actual : ℕ → Family ℕ) (time : ℕ) : Family ℕ :=
  if time < conversion then {allTickets} else actual time

theorem completed_refines (allTickets : Finset ℕ) (conversion : ℕ)
    (actual : ℕ → Family ℕ)
    (contained : ∀ time block, block ∈ actual time → block ⊆ allTickets)
    (shrinks : ∀ time, conversion ≤ time → Refines (actual (time + 1)) (actual time))
    (time : ℕ) :
    Refines (completed allTickets conversion actual (time + 1))
      (completed allTickets conversion actual time) := by
  by_cases before : time < conversion
  · by_cases stillBefore : time + 1 < conversion
    · simp only [completed, before, stillBefore, if_pos]
      intro block member
      exact ⟨block, member, Finset.Subset.refl _⟩
    · simp only [completed, before, stillBefore, if_pos]
      intro block member
      exact ⟨allTickets, Finset.mem_singleton_self _, contained _ block member⟩
  · have after : ¬time + 1 < conversion := by omega
    simpa [completed, before, after] using shrinks time (by omega)

theorem completed_ordered (allTickets : Finset ℕ) (conversion : ℕ)
    (actual : ℕ → Family ℕ)
    (ordered : ∀ time, conversion ≤ time → OrderedFamily (actual time)) (time : ℕ) :
    OrderedFamily (completed allTickets conversion actual time) := by
  by_cases before : time < conversion
  · simp only [completed, before, if_pos]
    intro first hfirst second hsecond different
    have same := (Finset.mem_singleton.mp hfirst).trans (Finset.mem_singleton.mp hsecond).symm
    exact False.elim (different same)
  · simpa [completed, before] using ordered time (by omega)

end GreedyMerge.FrozenHistory

#print axioms GreedyMerge.FrozenHistory.split_family_refines
#print axioms GreedyMerge.FrozenHistory.familyView_perm
#print axioms GreedyMerge.FrozenHistory.completed_refines
