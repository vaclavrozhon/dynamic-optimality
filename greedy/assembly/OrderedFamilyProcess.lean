import FrozenFamilyHistory

/-!
The immutable histories of actual frozen blocks remain ordered under the
allowed closed-family operations. This derives the abstract ordered-family
condition from concrete split/delete/rebase/permutation histories. A family
starts this process at conversion; its earlier growing prefix is supplied
by FrozenFamilyHistory.completed.
-/

namespace GreedyMerge.HistoryProcess

open OrderedBlocks FrozenHistory GreedyForest

def Separated (first second : Frozen) : Prop :=
  first.family ≠ second.family ∨
    BeforeInOrder (joins first) (joins second) ∨ BeforeInOrder (joins second) (joins first)

theorem separated_symm {first second : Frozen} (separated : Separated first second) :
    Separated second first := by
  rcases separated with different | forward | backward
  · exact Or.inl different.symm
  · exact Or.inr (Or.inr forward)
  · exact Or.inr (Or.inl backward)

theorem separated_descendants {a b first second : Frozen}
    (aDescends : Descends a first) (bDescends : Descends b second)
    (separated : Separated first second) : Separated a b := by
  rcases separated with different | forward | backward
  · exact Or.inl (by simpa only [aDescends.1, bDescends.1] using different)
  · exact Or.inr (Or.inl (beforeInOrder_of_subsets _ _ _ _
      (descends_joins aDescends) (descends_joins bDescends) forward))
  · exact Or.inr (Or.inr (beforeInOrder_of_subsets _ _ _ _
      (descends_joins bDescends) (descends_joins aDescends) backward))

def Valid (blocks : List Frozen) : Prop :=
  blocks.Pairwise Separated ∧ ∀ block ∈ blocks,
    ∃ orientation, HistMonotone orientation block.members

theorem separated_of_members (blocks : List Frozen) (ordered : blocks.Pairwise Separated)
    (first second : Frozen) (firstMember : first ∈ blocks) (secondMember : second ∈ blocks)
    (different : first ≠ second) : Separated first second := by
  induction blocks with
  | nil => simp at firstMember
  | cons block rest ih =>
      rcases List.pairwise_cons.mp ordered with ⟨head, tail⟩
      rcases List.mem_cons.mp firstMember with rfl | firstTail
      · rcases List.mem_cons.mp secondMember with rfl | secondTail
        · exact False.elim (different rfl)
        · exact head second secondTail
      · rcases List.mem_cons.mp secondMember with rfl | secondTail
        · exact separated_symm (head first firstTail)
        · exact ih tail firstTail secondTail

theorem family_ordered (family : ℕ) (blocks : List Frozen) (valid : Valid blocks) :
    OrderedFamily (familyView family blocks) := by
  intro first firstMember second secondMember different
  obtain ⟨a, aMember, aFamily, rfl⟩ := mem_familyView.mp firstMember
  obtain ⟨b, bMember, bFamily, rfl⟩ := mem_familyView.mp secondMember
  have distinct : a ≠ b := fun same => different (congrArg joins same)
  rcases separated_of_members blocks valid.1 a b aMember bMember distinct with other | order
  · exact False.elim (other (aFamily.trans bFamily.symm))
  · exact order

theorem split_separated (focus : Frozen) (cut leftId rightId : ℕ)
    (history : ∃ orientation, HistMonotone orientation focus.members) :
    (splitFresh leftId rightId focus cut).Pairwise Separated := by
  obtain ⟨orientation, monotone⟩ := history
  have pair : ((focus.members.take cut) ++ focus.members.drop cut).Pairwise
      (fun first second : Primitives.Entry => if orientation then
        first.joined < second.joined else second.joined < first.joined) := by
    simpa only [HistMonotone, List.take_append_drop] using monotone
  have cross := (List.pairwise_append.mp pair).2.2
  unfold splitFresh
  apply List.pairwise_cons.mpr
  refine ⟨?_, List.pairwise_singleton _ _⟩
  intro piece member
  have equal := List.mem_singleton.mp member
  subst piece
  right
  cases orientation with
  | false =>
      right
      intro earlier hEarlier later hLater
      obtain ⟨rightEntry, rightMem, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hEarlier)
      obtain ⟨leftEntry, leftMem, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hLater)
      exact cross leftEntry leftMem rightEntry rightMem
  | true =>
      left
      intro earlier hEarlier later hLater
      obtain ⟨leftEntry, leftMem, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hEarlier)
      obtain ⟨rightEntry, rightMem, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hLater)
      exact cross leftEntry leftMem rightEntry rightMem

theorem replacement_valid (pre post pieces : List Frozen) (focus : Frozen)
    (valid : Valid (pre ++ focus :: post))
    (descendants : ∀ piece ∈ pieces, Descends piece focus)
    (siblings : pieces.Pairwise Separated) : Valid (pre ++ (pieces ++ post)) := by
  rcases List.pairwise_append.mp valid.1 with ⟨preOrder, focusPost, cross⟩
  rcases List.pairwise_cons.mp focusPost with ⟨focusBefore, postOrder⟩
  have focusMem : focus ∈ pre ++ focus :: post := by simp
  obtain ⟨orientation, focusHistory⟩ := valid.2 focus focusMem
  refine ⟨?_, ?_⟩
  · apply List.pairwise_append.mpr
    refine ⟨preOrder, ?_, ?_⟩
    · apply List.pairwise_append.mpr
      refine ⟨siblings, postOrder, ?_⟩
      intro piece pieceMember old oldMember
      exact separated_descendants (descendants piece pieceMember) (descends_refl old)
        (focusBefore old oldMember)
    · intro old oldMember other otherMember
      rcases List.mem_append.mp otherMember with piece | postMember
      · exact separated_descendants (descends_refl old) (descendants other piece)
          (cross old oldMember focus (List.mem_cons_self))
      · exact cross old oldMember other (List.mem_cons_of_mem _ postMember)
  · intro block member
    rcases List.mem_append.mp member with before | later
    · exact valid.2 block (List.mem_append_left _ before)
    · rcases List.mem_append.mp later with piece | after
      · exact ⟨orientation, descends_preserves_history_orientation
          (descendants block piece) orientation focusHistory⟩
      · exact valid.2 block (List.mem_append_right _ (List.mem_cons_of_mem _ after))

inductive Edit : List Frozen → List Frozen → Prop
  | split (pre post : List Frozen) (focus : Frozen) (cut leftId rightId : ℕ) :
      Edit (pre ++ focus :: post) (pre ++ (splitFresh leftId rightId focus cut ++ post))
  | erase (pre post : List Frozen) (focus : Frozen) (key : ℕ) :
      Edit (pre ++ focus :: post) (pre ++ eraseMember key focus :: post)
  | rebase (pre post : List Frozen) (focus : Frozen) (base : ℕ) :
      Edit (pre ++ focus :: post) (pre ++ OrderedBlocks.rebase base focus :: post)
  | perm {before after : List Frozen} (permutation : after.Perm before) : Edit before after

theorem Edit.valid {before after : List Frozen} (edit : Edit before after)
    (valid : Valid before) : Valid after := by
  cases edit with
  | split pre post focus cut leftId rightId =>
      exact replacement_valid pre post _ focus valid
        (splitFresh_descends leftId rightId focus cut)
        (split_separated focus cut leftId rightId (valid.2 focus (by simp)))
  | erase pre post focus key =>
      apply replacement_valid pre post [eraseMember key focus] focus valid
      · intro piece member
        have equal := List.mem_singleton.mp member
        subst piece
        exact erase_descends focus key
      · exact List.pairwise_singleton _ _
  | rebase pre post focus base =>
      apply replacement_valid pre post [OrderedBlocks.rebase base focus] focus valid
      · intro piece member
        have equal := List.mem_singleton.mp member
        subst piece
        exact rebase_descends focus base
      · exact List.pairwise_singleton _ _
  | perm permutation =>
      exact ⟨(permutation.pairwise_iff separated_symm).mpr valid.1,
        fun block member => valid.2 block (permutation.mem_iff.mp member)⟩

theorem Edit.refines {before after : List Frozen} (edit : Edit before after) (family : ℕ) :
    Refines (familyView family after) (familyView family before) := by
  cases edit with
  | split pre post focus cut leftId rightId =>
      simpa only [List.append_assoc, List.singleton_append] using
        split_family_refines family leftId rightId cut pre post focus
  | erase pre post focus key =>
      simpa only [List.append_assoc, List.singleton_append] using
        erase_family_refines family key pre post focus
  | rebase pre post focus base =>
      simpa only [List.append_assoc, List.singleton_append] using
        rebase_family_refines family base pre post focus
  | perm permutation =>
      rw [familyView_perm family permutation]
      intro block member
      exact ⟨block, member, Finset.Subset.refl _⟩

inductive Run : List Frozen → List Frozen → Prop
  | nil (blocks : List Frozen) : Run blocks blocks
  | cons {before middle after : List Frozen} (step : Edit before middle)
      (rest : Run middle after) : Run before after

theorem Run.valid {before after : List Frozen} (run : Run before after)
    (valid : Valid before) : Valid after := by
  induction run with
  | nil _ => exact valid
  | cons step rest ih => exact ih (step.valid valid)

/-- The ordered-family and unique-historical-cut conditions follow for
every actual closed-family edit run starting from its conversion block. -/
theorem closed_run_ordered (initial : Frozen) (after : List Frozen)
    (history : ∃ orientation, HistMonotone orientation initial.members)
    (run : Run [initial] after) (family cut : ℕ) :
    OrderedFamily (familyView family after) ∧
    Partitioned (familyView family after) ∧
    UniqueStraddler (fun joined => decide (cut ≤ joined)) (familyView family after) := by
  have initialValid : Valid [initial] := by
    refine ⟨List.pairwise_singleton _ _, ?_⟩
    intro block member
    simpa only [List.mem_singleton.mp member] using history
  have ordered := family_ordered family after (run.valid initialValid)
  exact ⟨ordered, ordered_partitioned _ ordered, orderedFamily_uniqueStraddler _ _ ordered⟩

end GreedyMerge.HistoryProcess

#print axioms GreedyMerge.HistoryProcess.Edit.refines
#print axioms GreedyMerge.HistoryProcess.closed_run_ordered
