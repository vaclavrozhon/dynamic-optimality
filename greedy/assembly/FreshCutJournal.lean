import FreshInventory

/-! Fresh cut allocation and the actual creation journal agree. Unused
reserved names are absent from the journal. Actual born ids are distinct,
are new relative to the incoming counter, and remain below the next one. -/

namespace GreedyMerge.FreshIds

open OrderedBlocks BirthJournal

def locations (slots : ℕ) : List (Fin slots) := List.ofFn (fun slot : Fin slots => slot)

def gather {slots : ℕ} (states : Fin slots → SideState) : List ℕ :=
  (locations slots).flatMap (fun slot => liveIds (states slot))

theorem Inventory.gather_unique {slots next : ℕ} {states : Fin slots → SideState}
    (inventory : Inventory states next) : (gather states).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun slot _ => inventory.localUnique slot, ?_⟩
  have distinct : (GreedyMerge.FreshIds.locations slots).Pairwise (· ≠ ·) :=
    List.nodup_ofFn.mpr (fun _ _ equal => equal)
  apply distinct.imp
  intro first second different
  apply List.disjoint_left.mpr
  intro id firstMember secondMember
  exact different (inventory.locations first second id firstMember secondMember)

noncomputable def freshCutJournal {slots : ℕ} (cut start : ℕ)
    (states : Fin slots → SideState) : List ℕ :=
  (locations slots).flatMap (fun slot =>
    cutBirthIds cut (start + reserveWidth (fun slot => (states slot).shrinking) * slot.val)
      (states slot).shrinking)

theorem freshCutJournal_sublist {slots : ℕ} (side : Fin slots → Bool) (cut start : ℕ)
    (states : Fin slots → SideState) :
    (freshCutJournal cut start states).Sublist (gather (freshCutStates side cut start states).1) := by
  apply List.Sublist.flatMap_right
  intro slot _
  exact (cutBirthIds_sublist (side slot) cut _ _).trans (List.sublist_append_left _ _)

theorem freshCutJournal_unique {slots : ℕ} (side : Fin slots → Bool) (cut start : ℕ)
    (states : Fin slots → SideState) (inventory : Inventory states start) :
    (freshCutJournal cut start states).Nodup :=
  (freshCutStates_inventory side cut start states inventory).gather_unique.sublist
    (freshCutJournal_sublist side cut start states)

theorem freshCutJournal_new {slots : ℕ} (cut start : ℕ) (states : Fin slots → SideState)
    (id : ℕ) (member : id ∈ freshCutJournal cut start states) : start ≤ id := by
  obtain ⟨slot, _, present⟩ := List.mem_flatMap.mp member
  have bound := cutBirthIds_range cut _ (states slot).shrinking id present
  omega

theorem freshCutJournal_before_next {slots : ℕ} (side : Fin slots → Bool) (cut start : ℕ)
    (states : Fin slots → SideState) (inventory : Inventory states start)
    (id : ℕ) (member : id ∈ freshCutJournal cut start states) :
    id < (freshCutStates side cut start states).2 := by
  have present := (freshCutJournal_sublist side cut start states).subset member
  obtain ⟨slot, _, localMember⟩ := List.mem_flatMap.mp present
  exact (freshCutStates_inventory side cut start states inventory).below slot id localMember

/-- The cardinality parameter used by accounting is the actual sum of
cut births; it is unrelated to the size of the reserved name intervals. -/
theorem freshCutJournal_length {slots : ℕ} (cut start : ℕ) (states : Fin slots → SideState) :
    (freshCutJournal cut start states).length =
      ∑ slot, cutListBirths cut (states slot).shrinking := by
  simp [freshCutJournal, locations, List.length_flatMap, List.map_ofFn,
    cutBirthIds_length, List.sum_ofFn]

end GreedyMerge.FreshIds

#print axioms GreedyMerge.FreshIds.freshCutJournal_unique
#print axioms GreedyMerge.FreshIds.freshCutJournal_length
