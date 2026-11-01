import Greedy.RunGrowth

/-! At most two historical grower families of one creator grow at a time. -/

namespace Greedy.GrowthJournal

open Splay.Rank GreedyMerge.GrowthBook GreedyMerge.GrowthWindows

noncomputable def activeNames {n : ℕ} (books : HeapBooks n) (owner : External n)
    (time : ℕ) (names : Finset ℕ) : Finset ℕ := by
  classical
  exact names.filter (fun family => ∃ side,
    growthStart family (journal (books owner side)) ≤ time ∧
      time < growthEnd family (journal (books owner side)))

/-- The bound follows from two actual creator slots and chronological
batch disjointness in each slot. The finite name set is arbitrary. -/
theorem activeNames_card {n clock next : ℕ} {states : GreedyMerge.OrderedBlocks.HeapSides n}
    (books : HeapBooks n) (good : HeapGood clock next states books)
    (owner : External n) (time : ℕ) (names : Finset ℕ) : (activeNames books owner time names).card ≤ 2 := by
  classical
  let active := activeNames books owner time names
  have present : ∀ family ∈ active, ∃ side,
      growthStart family (journal (books owner side)) ≤ time ∧
        time < growthEnd family (journal (books owner side)) := by
    intro family member
    exact (Finset.mem_filter.mp member).2
  let slot : {family // family ∈ active} → Bool := fun family => (present family.val family.property).choose
  have slotActive (family : {family // family ∈ active}) :
      growthStart family.val (journal (books owner (slot family))) ≤ time ∧
        time < growthEnd family.val (journal (books owner (slot family))) :=
    (present family.val family.property).choose_spec
  have injective : Function.Injective slot := by
    intro first second same
    have firstActive := slotActive first
    have secondActive := slotActive second
    rw [same] at firstActive
    apply Subtype.ext
    exact one_active_family _ (good owner (slot second)).ordered first.val second.val time
      firstActive.1 firstActive.2 secondActive.1 secondActive.2
  have bound := Fintype.card_le_of_injective slot injective
  simpa only [Fintype.card_coe, Fintype.card_bool] using bound

end Greedy.GrowthJournal
