import FreshCutJournal

/-! An arbitrary finite sequence of actual cut passes, with its concrete
state-dependent allocator and exact creation journal. Names are never
reused, including when an intermediate instance has already been retired.
-/

namespace GreedyMerge.FreshIds

open OrderedBlocks

structure CutResult (slots : ℕ) where
  states : Fin slots → SideState
  next : ℕ
  born : List ℕ

noncomputable def freshCuts {slots : ℕ} (side : Fin slots → Bool) :
    List ℕ → ℕ → (Fin slots → SideState) → CutResult slots
  | [], start, states => ⟨states, start, []⟩
  | cut :: rest, start, states =>
      let step := freshCutStates side cut start states
      let tail := freshCuts side rest step.2 step.1
      ⟨tail.states, tail.next, freshCutJournal cut start states ++ tail.born⟩

theorem freshCuts_inventory {slots : ℕ} (side : Fin slots → Bool)
    (cuts : List ℕ) (start : ℕ) (states : Fin slots → SideState)
    (inventory : Inventory states start) :
    Inventory (freshCuts side cuts start states).states (freshCuts side cuts start states).next := by
  induction cuts generalizing start states with
  | nil => exact inventory
  | cons cut rest ih =>
      exact ih _ _ (freshCutStates_inventory side cut start states inventory)

theorem freshCuts_next {slots : ℕ} (side : Fin slots → Bool)
    (cuts : List ℕ) (start : ℕ) (states : Fin slots → SideState) :
    start ≤ (freshCuts side cuts start states).next := by
  induction cuts generalizing start states with
  | nil => exact le_refl _
  | cons cut rest ih =>
      exact (Nat.le_add_right _ _).trans (ih _ _)

theorem freshCuts_new {slots : ℕ} (side : Fin slots → Bool)
    (cuts : List ℕ) (start : ℕ) (states : Fin slots → SideState)
    (id : ℕ) (member : id ∈ (freshCuts side cuts start states).born) : start ≤ id := by
  induction cuts generalizing start states with
  | nil => simp [freshCuts] at member
  | cons cut rest ih =>
      rcases List.mem_append.mp member with head | tail
      · exact freshCutJournal_new cut start states id head
      · exact (Nat.le_add_right _ _).trans (ih _ _ tail)

theorem freshCuts_before_next {slots : ℕ} (side : Fin slots → Bool)
    (cuts : List ℕ) (start : ℕ) (states : Fin slots → SideState)
    (inventory : Inventory states start)
    (id : ℕ) (member : id ∈ (freshCuts side cuts start states).born) :
    id < (freshCuts side cuts start states).next := by
  induction cuts generalizing start states with
  | nil => simp [freshCuts] at member
  | cons cut rest ih =>
      rcases List.mem_append.mp member with head | tail
      · exact lt_of_lt_of_le (freshCutJournal_before_next side cut start states inventory id head)
          (freshCuts_next side rest _ _)
      · exact ih _ _ (freshCutStates_inventory side cut start states inventory) tail

theorem freshCuts_unique {slots : ℕ} (side : Fin slots → Bool)
    (cuts : List ℕ) (start : ℕ) (states : Fin slots → SideState)
    (inventory : Inventory states start) : (freshCuts side cuts start states).born.Nodup := by
  induction cuts generalizing start states with
  | nil => simp [freshCuts]
  | cons cut rest ih =>
      apply List.nodup_append.mpr
      refine ⟨freshCutJournal_unique side cut start states inventory,
        ih _ _ (freshCutStates_inventory side cut start states inventory), ?_⟩
      intro first firstMember second secondMember equal
      have before := freshCutJournal_before_next side cut start states inventory first firstMember
      have after := freshCuts_new side rest _ _ second secondMember
      omega

noncomputable def actualCutBirths {slots : ℕ} (side : Fin slots → Bool) :
    List ℕ → ℕ → (Fin slots → SideState) → ℕ
  | [], _, _ => 0
  | cut :: rest, start, states =>
      let step := freshCutStates side cut start states
      (∑ slot, cutListBirths cut (states slot).shrinking) + actualCutBirths side rest step.2 step.1

theorem freshCuts_length {slots : ℕ} (side : Fin slots → Bool)
    (cuts : List ℕ) (start : ℕ) (states : Fin slots → SideState) :
    (freshCuts side cuts start states).born.length = actualCutBirths side cuts start states := by
  induction cuts generalizing start states with
  | nil => rfl
  | cons cut rest ih => simp only [freshCuts, actualCutBirths, List.length_append,
      freshCutJournal_length, ih]

end GreedyMerge.FreshIds

#print axioms GreedyMerge.FreshIds.freshCuts_unique
#print axioms GreedyMerge.FreshIds.freshCuts_length
