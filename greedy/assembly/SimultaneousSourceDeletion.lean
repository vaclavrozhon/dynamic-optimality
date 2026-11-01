import ActualSourceDeletion

/-!
A complete consolidation erases its departing records from every frozen
fragment at once. This module proves the source collapse against that
literal simultaneous deletion, including arbitrary subsequent closed
family administration. It does not assume that other source blocks stay
unchanged while the selected source is consolidated.
-/
namespace GreedyMerge.HistoryProcess

open OrderedBlocks FrozenHistory GreedyForest

@[simp] theorem eraseKeys_family (keys : List ℕ) (block : Frozen) :
    (eraseKeys keys block).family = block.family := by
  rw [eraseKeys_eq]

theorem eraseKeys_descends (keys : List ℕ) (block : Frozen) :
    Descends (eraseKeys keys block) block := by
  rw [eraseKeys_eq]
  exact ⟨rfl,rfl,List.filter_sublist⟩

def eraseAll (keys : List ℕ) (blocks : List Frozen) : List Frozen :=
  blocks.map (eraseKeys keys)

theorem eraseAll_history (keys : List ℕ) (blocks : List Frozen) :
    Run blocks (eraseAll keys blocks) := by
  induction blocks with
  | nil => exact .nil []
  | cons block rest ih =>
      have first := (eraseKeys_history keys block).context [] rest
      have second := ih.context [eraseKeys keys block] []
      simp only [List.nil_append,List.singleton_append,List.append_nil] at first second
      exact first.trans second

theorem eraseAll_refines (keys : List ℕ) (family : ℕ) (blocks : List Frozen) :
    Refines (familyView family (eraseAll keys blocks)) (familyView family blocks) :=
  (eraseAll_history keys blocks).refines family

/-- Refining the whole result cannot undo a source collapse. -/
theorem collapse_after_refines {source : Finset ℕ} {before middle after : Family ℕ}
    (collapse : Collapses source before middle) (refines : Refines after middle) :
    Collapses source before after := by
  intro final finalMember
  obtain ⟨intermediate,intermediateMember,finalSubset⟩ := refines final finalMember
  obtain ⟨original,originalMember,intermediateSubset,small⟩ := collapse intermediate intermediateMember
  exact ⟨original,originalMember,finalSubset.trans intermediateSubset,
    fun same => (Finset.card_le_card finalSubset).trans (small same)⟩

/-- Ordered history makes duplicate nonempty historical source sets
impossible, so a small surviving selected source suffices even though
all other blocks are simultaneously erased as well. -/
theorem eraseAll_collapses (keys : List ℕ) (blocks : List Frozen) (source : Frozen)
    (valid : Valid blocks) (present : source ∈ blocks)
    (small : (joins (eraseKeys keys source)).card ≤ 1) :
    Collapses (joins source) (familyView source.family blocks)
      (familyView source.family (eraseAll keys blocks)) := by
  intro members member
  obtain ⟨block,blockMember,same,rfl⟩ := mem_familyView.mp member
  obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp blockMember
  have family : old.family=source.family := by simpa using same
  refine ⟨joins old,mem_familyView.mpr ⟨old,oldMember,family,rfl⟩,
    descends_joins (eraseKeys_descends keys old),?_⟩
  intro equal
  by_cases oldSame : old=source
  · subst old
    exact small
  · have separate := separated_same_disjoint
      (separated_of_members blocks valid.1 old source oldMember present oldSame) family
    have empty : joins old=∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro ticket ticketMember
      exact Finset.disjoint_left.mp separate ticketMember (equal ▸ ticketMember)
    have card := Finset.card_le_card (descends_joins (eraseKeys_descends keys old))
    rw [empty,Finset.card_empty] at card
    omega

/-- The exact simultaneous deletion of a complete actual adjacent-root
run collapses every covered source, with mapped actual record keys. -/
theorem actual_all_deletions_collapse {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {roots : List ℕ} {survivor : ℕ}
    (run : Fringe.Schedule.Run rank events roots [survivor]) (unique : roots.Nodup)
    (record : ℕ → ℕ) (injective : Set.InjOn record {key | key ∈ roots})
    (blocks : List Frozen) (source : Frozen) (valid : Valid blocks)
    (present : source ∈ blocks) (keysUnique : (source.members.map Primitives.Entry.key).Nodup)
    (covered : ∀ entry ∈ source.members, ∃ key ∈ roots, record key=entry.key) :
    Collapses (joins source) (familyView source.family blocks)
      (familyView source.family (eraseAll (events.map (fun event => record event.2)) blocks)) := by
  apply eraseAll_collapses _ blocks source valid present
  rw [actual_deletions_eq_retainRoot run unique record injective source covered]
  exact retainRoot_card (record survivor) source keysUnique

theorem actual_all_deletions_then_admin_collapse {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {roots : List ℕ} {survivor : ℕ}
    (run : Fringe.Schedule.Run rank events roots [survivor]) (unique : roots.Nodup)
    (record : ℕ → ℕ) (injective : Set.InjOn record {key | key ∈ roots})
    (before after : List Frozen) (source : Frozen) (valid : Valid before)
    (present : source ∈ before) (keysUnique : (source.members.map Primitives.Entry.key).Nodup)
    (covered : ∀ entry ∈ source.members, ∃ key ∈ roots, record key=entry.key)
    (post : Run (eraseAll (events.map (fun event => record event.2)) before) after) :
    Collapses (joins source) (familyView source.family before) (familyView source.family after) :=
  collapse_after_refines (actual_all_deletions_collapse run unique record injective before source
    valid present keysUnique covered) (post.refines source.family)

end GreedyMerge.HistoryProcess

#print axioms GreedyMerge.HistoryProcess.eraseAll_history
#print axioms GreedyMerge.HistoryProcess.actual_all_deletions_then_admin_collapse
