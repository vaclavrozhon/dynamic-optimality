import ChaCha.GadgetAggregation
import ChaCha.OccurrenceAccounting

/-! Exact partition of the actual event budget by gadget. -/

namespace ChaCha
open Primary Witnesses

def EventTag.allowed (H : Nat) : EventTag → Prop
  | .inl _ => True
  | .inr (_, cell) => cell ∈ owners (H + 1)

theorem mem_activeEvents_iff {H : Nat} {qs : Finset Gadget} {history : List Key}
    {x : Key} {tag : EventTag} : tag ∈ activeEvents H qs history x ↔
      tag.gadget ∈ qs ∧ EventTag.allowed H tag ∧ ∃ y, EventRecord history x tag y := by
  classical
  cases tag with
  | inl q => simp [activeEvents, eventCandidates, EventTag.gadget, EventTag.allowed]
  | inr pair =>
    obtain ⟨q, cell⟩ := pair
    simp [activeEvents, eventCandidates, EventTag.gadget, EventTag.allowed, and_assoc]

theorem activeEvents_gadget_fiber (H : Nat) (qs : Finset Gadget) (history : List Key)
    (x : Key) {q : Gadget} (hq : q ∈ qs) :
    (activeEvents H qs history x).filter (fun tag => tag.gadget = q) =
      activeEvents H {q} history x := by
  classical
  ext tag
  simp only [Finset.mem_filter, mem_activeEvents_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨_, ha, he⟩, hq'⟩
    exact ⟨hq', ha, he⟩
  · rintro ⟨hq', ha, he⟩
    exact ⟨⟨hq'.symm ▸ hq, ha, he⟩, hq'⟩

theorem sum_singleton_activeEvents (H : Nat) (qs : Finset Gadget) (history : List Key)
    (x : Key) :
    (∑ q ∈ qs, (activeEvents H {q} history x).card) =
      (activeEvents H qs history x).card := by
  classical
  have hf : ∀ q ∈ qs, (activeEvents H {q} history x).card =
      ((activeEvents H qs history x).filter (fun tag => tag.gadget = q)).card := by
    intro q hq
    rw [activeEvents_gadget_fiber H qs history x hq]
  rw [Finset.sum_congr rfl hf]
  symm
  apply Finset.card_eq_sum_card_fiberwise
  intro tag htag
  exact (mem_activeEvents_iff.mp htag).1

theorem sum_singleton_eventSum (H : Nat) (qs : Finset Gadget) (history xs : List Key) :
    (∑ q ∈ qs, eventSum H {q} history xs) = eventSum H qs history xs := by
  classical
  induction xs generalizing history with
  | nil => simp [eventSum]
  | cons x xs ih =>
    simp only [eventSum, Finset.sum_add_distrib]
    rw [sum_singleton_activeEvents, ih]

/-- The first-free secondary bound omits the nonnegative terminal auxiliary
counts that are included when all hierarchy fragments are summed. -/
theorem secondaryDemands_le_allGadgets (H : Nat) (xs : List Key) :
    secondaryDemands H xs ≤ ∑ q ∈ allGadgets H, q.count xs := by
  exact Finset.sum_le_sum_of_subset (gadgets_subset_all H)

/-- Aggregate established local demand inequalities. This is an intermediate
summation lemma: callers must prove the concrete per-gadget occurrence bound. -/
theorem aggregate_local_demand_bounds_window (H : Nat) (xs history window : List Key)
    (hleaves : OnLeaves H xs)
    (local_bound : ∀ q ∈ allGadgets H,
      (q.count xs : ℤ) ≤ q.potentialDifference H xs +
        2 * (eventSum H {q} history window : ℤ)) :
    secondaryDemands H xs ≤ cyclicPrimary H xs + 2 * eventSum H (allGadgets H) history window := by
  have hsum := Finset.sum_le_sum local_bound
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hevents : (∑ q ∈ allGadgets H,
      (eventSum H {q} history window : ℤ)) = (eventSum H (allGadgets H) history window : ℤ) := by
    rw [← Nat.cast_sum, sum_singleton_eventSum]
  rw [hevents] at hsum
  have hpot := allGadgets_potential_le_primary H xs hleaves
  have hd := secondaryDemands_le_allGadgets H xs
  have hd' : (secondaryDemands H xs : ℤ) ≤ ∑ q ∈ allGadgets H, (q.count xs : ℤ) := by
    exact_mod_cast hd
  have hout : (secondaryDemands H xs : ℤ) ≤
      (cyclicPrimary H xs : ℤ) + 2 * (eventSum H (allGadgets H) history window : ℤ) := by omega
  exact_mod_cast hout

theorem aggregate_local_demand_bounds (H : Nat) (xs : List Key) (hleaves : OnLeaves H xs)
    (local_bound : ∀ q ∈ allGadgets H,
      (q.count xs : ℤ) ≤ q.potentialDifference H xs +
        2 * (eventSum H {q} xs (xs ++ (xs ++ xs)) : ℤ)) :
    secondaryDemands H xs ≤ cyclicPrimary H xs + 2 * threePeriodEvents H xs :=
  aggregate_local_demand_bounds_window H xs xs (xs ++ (xs ++ xs)) hleaves local_bound

end ChaCha
