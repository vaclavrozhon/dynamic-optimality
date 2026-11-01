import OrderedIdSupport
import FreshCutIds

/-!
Concrete fresh allocation for a finite table of side states. The counter
tracks reserved names, while the existing actual birth journals track the
logical instances that are created. Both frozen and growing identities
participate in the same uniqueness invariant.
-/

namespace GreedyMerge.FreshIds

open OrderedBlocks

structure Inventory {slots : ℕ} (states : Fin slots → SideState) (next : ℕ) : Prop where
  localUnique : ∀ slot, (liveIds (states slot)).Nodup
  locations : ∀ first second id, id ∈ liveIds (states first) →
    id ∈ liveIds (states second) → first = second
  below : ∀ slot id, id ∈ liveIds (states slot) → id < next

theorem conversion_liveIds (owner family replacementId base : ℕ) (state : SideState) :
    liveIds (convert owner family replacementId base state) =
      liveIds state ++ conversionIds replacementId state := by
  cases grower : state.grower with
  | none => simp [convert, liveIds, conversionIds, grower]
  | some old =>
      by_cases empty : old.members = []
      · simp [convert, liveIds, conversionIds, grower, empty]
      · simp [convert, liveIds, conversionIds, grower, empty, freeze, emptyGrower, List.append_assoc]

theorem conversion_ids_unique (owner family replacementId base : ℕ) (state : SideState)
    (unique : (liveIds state).Nodup) (fresh : replacementId ∉ liveIds state) :
    (liveIds (convert owner family replacementId base state)).Nodup := by
  rw [conversion_liveIds]
  cases grower : state.grower with
  | none => simpa [conversionIds, grower] using unique
  | some old =>
      by_cases empty : old.members = []
      · simpa [conversionIds, grower, empty] using unique
      · simp only [conversionIds, grower, if_neg empty]
        apply List.nodup_append.mpr
        refine ⟨unique, by simp, ?_⟩
        intro first firstMember second secondMember equal
        have same := List.mem_singleton.mp secondMember
        exact fresh ((equal.trans same) ▸ firstMember)

theorem cutState_ids_unique (side : Bool) (cut fresh : ℕ) (state : SideState)
    (unique : (liveIds state).Nodup) (oldIds : ∀ id ∈ liveIds state, id < fresh) :
    (liveIds (cutState side cut fresh state)).Nodup := by
  have frozenUnique : (state.shrinking.map Frozen.id).Nodup :=
    (List.nodup_append.mp unique).1
  have growingUnique := (List.nodup_append.mp unique).2.1
  have oldDisjoint := (List.nodup_append.mp unique).2.2
  apply List.nodup_append.mpr
  refine ⟨cutList_ids_nodup side cut fresh state.shrinking frozenUnique ?_, growingUnique, ?_⟩
  · intro block member
    exact oldIds block.id (List.mem_append_left _ (List.mem_map.mpr ⟨block, member, rfl⟩))
  · intro id frozen other growing equalIds
    subst other
    obtain ⟨piece, member, rfl⟩ := List.mem_map.mp frozen
    rcases cutList_id_origin side cut fresh state.shrinking piece member with old | newRange
    · obtain ⟨old, oldMember, equal⟩ := old
      exact oldDisjoint piece.id (List.mem_map.mpr ⟨old, oldMember, equal.symm⟩) piece.id growing rfl
    · have oldBound := oldIds piece.id (List.mem_append_right _ growing)
      omega

/-- Old local identities or a disjoint reserved interval determine the
unique output location. The local primitive must separately prove that it
does not duplicate identities within that location. -/
theorem inventory_of_intervals {slots : ℕ} (before after : Fin slots → SideState)
    (start width : ℕ) (inventory : Inventory before start)
    (_positive : 0 < width)
    (localUnique : ∀ slot, (liveIds (after slot)).Nodup)
    (origin : ∀ slot id, id ∈ liveIds (after slot) →
      id ∈ liveIds (before slot) ∨
        start + width * slot.val ≤ id ∧ id < start + width * slot.val + width) :
    Inventory after (start + width * slots) := by
  refine ⟨localUnique, ?_, ?_⟩
  · intro first second id firstMember secondMember
    rcases origin first id firstMember with firstOld | firstNew
    · rcases origin second id secondMember with secondOld | secondNew
      · exact inventory.locations first second id firstOld secondOld
      · have oldBound := inventory.below first id firstOld
        omega
    · rcases origin second id secondMember with secondOld | secondNew
      · have oldBound := inventory.below second id secondOld
        omega
      · by_contra different
        exact reserve_disjoint (fun equal => different (Fin.ext equal))
          firstNew.1 firstNew.2 secondNew.1 secondNew.2 rfl
  · intro slot id member
    rcases origin slot id member with old | interval
    · have oldBound := inventory.below slot id old
      omega
    · have index := Nat.mul_le_mul_left width (Nat.succ_le_of_lt slot.isLt)
      nlinarith

noncomputable def freshCutStates {slots : ℕ} (side : Fin slots → Bool) (cut start : ℕ)
    (states : Fin slots → SideState) : (Fin slots → SideState) × ℕ :=
  let width := reserveWidth (fun slot => (states slot).shrinking)
  (fun slot => cutState (side slot) cut (start + width * slot.val) (states slot),
    start + width * slots)

theorem freshCutStates_inventory {slots : ℕ} (side : Fin slots → Bool) (cut start : ℕ)
    (states : Fin slots → SideState) (inventory : Inventory states start) :
    Inventory (freshCutStates side cut start states).1 (freshCutStates side cut start states).2 := by
  let width := reserveWidth (fun slot => (states slot).shrinking)
  apply inventory_of_intervals states _ start width inventory
    (reserveWidth_positive _) ?_ ?_
  · intro slot
    apply cutState_ids_unique (side slot) cut _ (states slot) (inventory.localUnique slot)
    intro id member
    exact lt_of_lt_of_le (inventory.below slot id member) (Nat.le_add_right _ _)
  · intro slot id member
    rcases List.mem_append.mp member with frozen | growing
    · obtain ⟨piece, pieceMember, rfl⟩ := List.mem_map.mp frozen
      rcases cutList_id_origin (side slot) cut _ _ piece pieceMember with old | interval
      · obtain ⟨old, oldMember, equal⟩ := old
        exact Or.inl (List.mem_append_left _ (List.mem_map.mpr ⟨old, oldMember, equal.symm⟩))
      · right
        have capacity := reserveWidth_capacity (fun slot => (states slot).shrinking) slot
        exact ⟨interval.1, lt_of_lt_of_le interval.2 (Nat.add_le_add_left capacity _)⟩
    · exact Or.inl (List.mem_append_right _ growing)

def freshConversions {slots : ℕ} (owner base : Fin slots → ℕ) (selected : Fin slots → Bool)
    (start : ℕ) (states : Fin slots → SideState) : (Fin slots → SideState) × ℕ :=
  (fun slot => if selected slot then
    convert (owner slot) (start + slot.val) (start + slot.val) (base slot) (states slot)
    else states slot, start + slots)

theorem freshConversions_inventory {slots : ℕ} (owner base : Fin slots → ℕ)
    (selected : Fin slots → Bool) (start : ℕ) (states : Fin slots → SideState)
    (inventory : Inventory states start) :
    Inventory (freshConversions owner base selected start states).1
      (freshConversions owner base selected start states).2 := by
  have result : Inventory (freshConversions owner base selected start states).1 (start + 1 * slots) := by
    apply inventory_of_intervals states _ start 1 inventory (by omega) ?_ ?_
    · intro slot
      dsimp only [freshConversions]
      split_ifs
      · apply conversion_ids_unique _ _ _ _ _ (inventory.localUnique slot)
        intro present
        have oldBound := inventory.below slot _ present
        omega
      · exact inventory.localUnique slot
    · intro slot id member
      dsimp only [freshConversions] at member
      split_ifs at member
      · rcases conversion_id_support (owner slot) (start + slot.val) (start + slot.val)
          (base slot) (states slot) id member with old | born
        · exact Or.inl old
        · right
          cases grower : (states slot).grower with
          | none => simp [conversionIds, grower] at born
          | some old =>
              by_cases empty : old.members = []
              · simp [conversionIds, grower, empty] at born
              · have equal : id = start + slot.val := by simpa [conversionIds, grower, empty] using born
                omega
      · exact Or.inl member
  change Inventory (freshConversions owner base selected start states).1 (start + slots)
  simpa only [Nat.one_mul] using result

end GreedyMerge.FreshIds

#print axioms GreedyMerge.FreshIds.freshCutStates_inventory
#print axioms GreedyMerge.FreshIds.freshConversions_inventory
