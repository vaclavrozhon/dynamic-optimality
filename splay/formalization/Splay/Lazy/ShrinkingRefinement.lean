import Splay.Lazy.Operations

namespace Splay.Lazy.State

/-- Pairing phases preserve the physical ID of every shrinking interval.
Its payload only shrinks; its placement and creator stay fixed. Only
sources owned by an active owner may advance their pass counter. -/
def ShrinkingRefinement {n : ℕ} (active : Element n → Prop) (before after : State n) : Prop :=
  ∀ (id : Interface.BlockId) (next : Block n), after.blocks[id]? = some next → next.mode = .shrinking →
    ∃ old : Block n, before.blocks[id]? = some old ∧ old.mode = .shrinking ∧
      next.owner = old.owner ∧ next.side = old.side ∧ next.creator = old.creator ∧
      next.elements.Sublist old.elements ∧ old.passCount ≤ next.passCount ∧
      (next.passCount = old.passCount ∨ active old.owner)

namespace ShrinkingRefinement

theorem refl {n : ℕ} (active : Element n → Prop) (state : State n) :
    ShrinkingRefinement active state state := by
  intro id block found shrinking
  exact ⟨block, found, shrinking, rfl, rfl, rfl, List.Sublist.refl _, Nat.le_refl _, Or.inl rfl⟩

theorem trans {n : ℕ} {active : Element n → Prop} {first middle last : State n}
    (left : ShrinkingRefinement active first middle) (right : ShrinkingRefinement active middle last) :
    ShrinkingRefinement active first last := by
  intro id next found shrinking
  obtain ⟨inter, interFound, interShrinking, owner, side, creator, sublist, count, changed⟩ := right id next found shrinking
  obtain ⟨old, oldFound, oldShrinking, oldOwner, oldSide, oldCreator, oldSublist, oldCount, oldChanged⟩ :=
    left id inter interFound interShrinking
  refine ⟨old, oldFound, oldShrinking, owner.trans oldOwner, side.trans oldSide, creator.trans oldCreator,
    sublist.trans oldSublist, oldCount.trans count, ?_⟩
  rcases changed with same | activeInter
  · rcases oldChanged with oldSame | activeOld
    · exact Or.inl (same.trans oldSame)
    · exact Or.inr activeOld
  · exact Or.inr (oldOwner ▸ activeInter)

theorem mono {n : ℕ} {active other : Element n → Prop} {before after : State n}
    (refinement : ShrinkingRefinement active before after) (subset : ∀ owner, active owner → other owner) :
    ShrinkingRefinement other before after := by
  intro id next found shrinking
  obtain ⟨old, oldFound, oldShrinking, owner, side, creator, sublist, count, changed⟩ := refinement id next found shrinking
  exact ⟨old, oldFound, oldShrinking, owner, side, creator, sublist, count, changed.imp_right (subset old.owner)⟩

theorem of_blocks_eq {n : ℕ} (active : Element n → Prop) {before after : State n}
    (equal : after.blocks = before.blocks) : ShrinkingRefinement active before after := by
  intro id block found shrinking
  exact ⟨block, equal ▸ found, shrinking, rfl, rfl, rfl, List.Sublist.refl _, Nat.le_refl _, Or.inl rfl⟩

end ShrinkingRefinement

/-- A growing insertion cannot create a new shrinking interval. -/
theorem insert_shrinkingRefinement {n : ℕ} (active : Element n → Prop) (state : State n)
    (destinationId : Interface.BlockId) (destination : Block n) (element : Element n)
    (destinationFound : state.blocks[destinationId]? = some destination)
    (growing : destination.mode = .growing) :
    ShrinkingRefinement active state (state.insert destinationId element) := by
  intro id next found shrinking
  change (state.blocks.modify destinationId (fun block => block.inserted element))[id]? = some next at found
  rw [List.getElem?_modify] at found
  split at found
  next same =>
    subst id
    simp [destinationFound] at found
    subst next
    change destination.mode = .shrinking at shrinking
    rw [growing] at shrinking
    contradiction
  next =>
    exact ⟨next, by simpa using found, shrinking, rfl, rfl, rfl, List.Sublist.refl _, Nat.le_refl _, Or.inl rfl⟩

theorem delete_shrinkingRefinement {n : ℕ} (active : Element n → Prop) (state : State n)
    (sourceId : Interface.BlockId) (element : Element n) (gap : ℤ) :
    ShrinkingRefinement active state (state.delete sourceId element gap) := by
  intro id next found shrinking
  change (state.blocks.modify sourceId (fun block => block.deleted element gap))[id]? = some next at found
  rw [List.getElem?_modify] at found
  split at found
  · obtain ⟨old, oldFound, equal⟩ := Option.map_eq_some_iff.mp found
    subst next
    exact ⟨old, oldFound, shrinking, rfl, rfl, rfl, List.erase_sublist, Nat.le_refl _, Or.inl rfl⟩
  · exact ⟨next, by simpa using found, shrinking, rfl, rfl, rfl, List.Sublist.refl _, Nat.le_refl _, Or.inl rfl⟩

/-- The exact rich pass changes the selected shrinking source and inserts
only into growing destinations. -/
theorem passAtView_shrinkingRefinement {n : ℕ} (state : State n) (afterView : HeapView n)
    (sourceId : Interface.BlockId) (source : Block n) (matching : List (Interface.Pairing n)) (gap : ℤ)
    (sourceFound : state.blocks[sourceId]? = some source) (shrinking : source.mode = .shrinking)
    (destinationsNodup : (matching.map fun pairing => pairing.destination).Nodup)
    (destinations : ∀ pairing ∈ matching, ∃ block, state.blocks[pairing.destination]? = some block ∧ block.mode = .growing) :
    ShrinkingRefinement (fun owner => owner = source.owner) state (state.passAtView afterView sourceId source matching gap) := by
  intro id next found nextShrinking
  change (Block.passBlocks state.blocks sourceId source matching gap)[id]? = some next at found
  have destinationsNe : ∀ pairing ∈ matching, pairing.destination ≠ sourceId := by
    intro pairing member eq
    obtain ⟨block, blockFound, growing⟩ := destinations pairing member
    rw [eq, sourceFound] at blockFound
    have same := Option.some.inj blockFound
    rw [← same, shrinking] at growing
    contradiction
  by_cases same : id = sourceId
  · subst id
    rw [Block.passBlocks_source_getElem? _ _ _ _ _ sourceFound destinationsNe] at found
    have equal := Option.some.inj found
    subst next
    refine ⟨source, sourceFound, shrinking, rfl, rfl, rfl, ?_, Nat.le_add_right _ _, Or.inr rfl⟩
    change (Interface.removeLosers source.elements matching).Sublist source.elements
    have removes : ∀ (elements : List (Element n)) (pairs : List (Interface.Pairing n)),
        (Interface.removeLosers elements pairs).Sublist elements := by
      intro elements pairs
      induction pairs generalizing elements with
      | nil => exact List.Sublist.refl _
      | cons pair pairs ih => exact (ih (elements.erase pair.loser)).trans List.erase_sublist
    exact removes _ _
  · obtain ⟨old, oldFound⟩ : ∃ old, state.blocks[id]? = some old := by
      have lt := (List.getElem?_eq_some_iff.mp found).1
      rw [Block.length_passBlocks] at lt
      exact ⟨state.blocks[id], by simp⟩
    obtain ⟨updated, updatedFound, mode, _, _, _⟩ := Block.passBlocks_preserves_metadata_of_ne_source
      state.blocks sourceId id source matching gap destinationsNodup oldFound same
    have equal := Option.some.inj (updatedFound.symm.trans found)
    have oldShrinking : old.mode = .shrinking := mode.symm.trans (equal ▸ nextShrinking)
    have notDestination : ∀ pairing ∈ matching, pairing.destination ≠ id := by
      intro pairing member eq
      obtain ⟨block, blockFound, growing⟩ := destinations pairing member
      rw [eq, oldFound] at blockFound
      have same := Option.some.inj blockFound
      rw [← same, oldShrinking] at growing
      contradiction
    rw [Block.passBlocks_getElem?_of_ne _ _ _ _ _ _ same notDestination, oldFound] at found
    have equal := Option.some.inj found
    rw [← equal]
    exact ⟨old, oldFound, oldShrinking, rfl, rfl, rfl, List.Sublist.refl _, Nat.le_refl _, Or.inl rfl⟩

end Splay.Lazy.State
