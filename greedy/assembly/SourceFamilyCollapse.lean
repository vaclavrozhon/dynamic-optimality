import ConcreteHistoryEdits

/-!
Collapse at the family-history interface, using actual immutable block
members. At the end of a complete one-sided consolidation only its final
root can retain a source membership. Thus filtering a source block to
that root yields at most one historical ticket and the exact Collapses
witness used by the winner and creator-cut lifetime arguments.
-/

namespace GreedyMerge.HistoryProcess

open OrderedBlocks FrozenHistory GreedyForest

def retainRoot (root : ℕ) (block : Frozen) : Frozen :=
  { block with members := block.members.filter (fun entry => entry.key == root) }

theorem retainRoot_descends (root : ℕ) (block : Frozen) : Descends (retainRoot root block) block :=
  ⟨rfl, rfl, List.filter_sublist⟩

theorem retainRoot_card (root : ℕ) (block : Frozen)
    (unique : (block.members.map Primitives.Entry.key).Nodup) :
    (joins (retainRoot root block)).card ≤ 1 := by
  let kept := block.members.filter (fun entry => entry.key == root)
  have subset : (kept.map Primitives.Entry.key).toFinset ⊆ {root} := by
    intro key member
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    have equal := (List.mem_filter.mp present).2
    simpa only [Finset.mem_singleton, beq_iff_eq] using equal
  have keyUnique : (kept.map Primitives.Entry.key).Nodup :=
    unique.sublist (List.filter_sublist.map _)
  have count := Finset.card_le_card subset
  have small : kept.length ≤ 1 := by
    simpa only [List.toFinset_card_of_nodup keyUnique, List.length_map,
      Finset.card_singleton] using count
  have countJoins := List.toFinset_card_le (kept.map Primitives.Entry.joined)
  simp only [List.length_map] at countJoins
  simpa only [joins, retainRoot, kept] using countJoins.trans small

theorem separated_same_disjoint {first second : Frozen}
    (separated : Separated first second) (same : first.family = second.family) :
    Disjoint (joins first) (joins second) := by
  apply Finset.disjoint_left.mpr
  intro ticket firstContains secondContains
  rcases separated with different | forward | backward
  · exact different same
  · exact lt_irrefl ticket (forward ticket firstContains ticket secondContains)
  · exact lt_irrefl ticket (backward ticket secondContains ticket firstContains)

theorem source_context_disjoint (pre post : List Frozen) (focus : Frozen)
    (valid : Valid (pre ++ focus :: post)) (other : Frozen)
    (member : other ∈ pre ++ post) (same : focus.family = other.family) :
    Disjoint (joins focus) (joins other) := by
  rcases List.pairwise_append.mp valid.1 with ⟨_, tail, cross⟩
  apply separated_same_disjoint _ same
  rcases List.mem_append.mp member with before | after
  · exact separated_symm (cross other before focus (List.mem_cons_self))
  · exact (List.pairwise_cons.mp tail).1 other after

/-- Replacing a source by actual small surviving fragments supplies the
abstract collapse witness. Untouched fragments cannot duplicate its
nonempty ticket set, by the concrete ordered-history invariant. -/
theorem replacement_collapses (pre post pieces : List Frozen) (focus : Frozen)
    (valid : Valid (pre ++ focus :: post))
    (descendants : ∀ piece ∈ pieces, Descends piece focus)
    (small : ∀ piece ∈ pieces, (joins piece).card ≤ 1) :
    Collapses (joins focus)
      (familyView focus.family (pre ++ focus :: post))
      (familyView focus.family (pre ++ (pieces ++ post))) := by
  intro members member
  obtain ⟨block, present, family, rfl⟩ := mem_familyView.mp member
  have outside : ∀ block ∈ pre ++ post, block.family = focus.family →
      ∃ parent ∈ familyView focus.family (pre ++ focus :: post),
        joins block ⊆ parent ∧ (parent = joins focus → (joins block).card ≤ 1) := by
    intro old oldMember oldFamily
    refine ⟨joins old, mem_familyView.mpr ⟨old, ?_, oldFamily, rfl⟩,
      Finset.Subset.refl _, ?_⟩
    · rcases List.mem_append.mp oldMember with before | after
      · exact List.mem_append_left _ before
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ after)
    · intro equal
      have separate := source_context_disjoint pre post focus valid old oldMember oldFamily.symm
      apply Finset.card_le_one.mpr
      intro first firstMem second secondMem
      exact False.elim (Finset.disjoint_left.mp separate
        (equal ▸ firstMem) firstMem)
  rcases List.mem_append.mp present with before | later
  · exact outside block (List.mem_append_left _ before) family
  · rcases List.mem_append.mp later with piece | after
    · exact ⟨joins focus, mem_familyView.mpr ⟨focus, by simp, rfl, rfl⟩,
        descends_joins (descendants block piece), fun _ => small block piece⟩
    · exact outside block (List.mem_append_right _ after) family

theorem retainRoot_collapses (pre post : List Frozen) (focus : Frozen) (root : ℕ)
    (valid : Valid (pre ++ focus :: post))
    (unique : (focus.members.map Primitives.Entry.key).Nodup) :
    Collapses (joins focus)
      (familyView focus.family (pre ++ focus :: post))
      (familyView focus.family (pre ++ retainRoot root focus :: post)) := by
  apply replacement_collapses pre post [retainRoot root focus] focus valid
  · intro piece member
    have equal := List.mem_singleton.mp member
    subst piece
    exact retainRoot_descends root focus
  · intro piece member
    have equal := List.mem_singleton.mp member
    subst piece
    exact retainRoot_card root focus unique

/-- Two distinct source memberships witnessing an internal win rule out
the singleton-isolated case in the family lifetime theorem. -/
theorem internal_pair_not_isolated (family : ℕ) (blocks : List Frozen) (source : Frozen)
    (present : source ∈ blocks) (same : source.family = family)
    (winner loser : ℕ) (winnerMember : winner ∈ joins source)
    (loserMember : loser ∈ joins source) (different : winner ≠ loser) :
    ¬ Isolated winner (familyView family blocks) := by
  intro isolated
  have small := isolated (joins source) (mem_familyView.mpr ⟨source, present, same, rfl⟩) winnerMember
  have equal := Finset.mem_singleton.mp (small loserMember)
  exact different equal.symm

end GreedyMerge.HistoryProcess

#print axioms GreedyMerge.HistoryProcess.retainRoot_collapses
#print axioms GreedyMerge.HistoryProcess.internal_pair_not_isolated
