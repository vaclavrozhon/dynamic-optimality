import MultiSplay.ClassicalSwitchAccountingWord
import MultiSplay.ClassicalSwitchCapacity
import MultiSplay.CommonForestSplayBound

/-!
# Splay comparison for the exact chronological classical MultiSplay word

The adapter derives distinctness at every intermediate checkpoint, component
capacity, all join-size checks, and the one-time initialization volume. The
actual comparator program and its budget remain explicit hypotheses. This is
not yet an unconditional competitive theorem for classical MultiSplay.
-/

namespace MultiSplay.ClassicalSwitch.Accounting

open DynamicOptimality (RawTree BST)
open TangoSquared.MTR.Tree (inorder size length_inorder)
open TangoSquared.Primary (Key)
open EndpointEncoding CommonForest

variable {α : Type*}

theorem otherComponents_length (state : State) (reference : RawTree α) :
    (otherComponents state reference).length = size reference := by
  induction reference generalizing state with
  | empty => rfl
  | node left pivot right ihl ihr => simp [otherComponents, ihl, ihr, size]; omega

theorem forest_length (state : State) (reference : RawTree α) :
    (forest state reference).length = size reference + 1 := by
  simp [forest, otherComponents_length]

theorem forest_size_sum (state : State) (reference : RawTree α) :
    ((forest state reference).map size).sum = size reference := by
  have lengths := (forest_keys state reference).length_eq
  simpa only [List.length_flatMap, length_inorder] using lengths

theorem initialization_from_domains {state : State} {reference : RawTree α}
    {initial : List (RawTree α)} (same : domains initial = domains (forest state reference)) :
    (initial.map size).sum + initial.length = 2 * size reference + 1 := by
  have sums := congrArg (fun keys : List (List α) => (keys.map List.length).sum) same
  have lengths := congrArg List.length same
  simp only [domains, List.map_map, Function.comp_def, length_inorder, forest_size_sum] at sums
  simp only [domains, List.length_map, forest_length] at lengths
  rw [sums, lengths]
  omega

theorem unique_from_domains {state : State} {reference : RawTree α}
    {initial : List (RawTree α)} (same : domains initial = domains (forest state reference))
    (unique : (inorder reference).Nodup) : UniqueKeys initial := by
  change ((domains initial).flatten).Nodup
  rw [same]
  exact forest_unique state unique

theorem capacity_from_domains {lower upper : Nat} (reference : BST lower upper) {state : State}
    {initial : List (RawTree Nat)} (same : domains initial = domains (forest state reference.toRaw)) :
    Capacity reference.height initial := by
  apply (capacity_iff_domains reference.height initial).mpr
  rw [same]
  exact (capacity_iff_domains reference.height (forest state reference.toRaw)).mp
    (forest_capacity state reference)

/-- One uniform constant bounds the supplied actual splay execution. The
comparator has precisely the same chronological split/join word and initial
component domains; its shapes, final shapes, and paid preparations are free
to differ. The comparator budget is not asserted to be small here. -/
theorem history_splay_bound :
    ∃ constant : Nat, 0 < constant ∧
      ∀ {lower upper : Nat} (reference : BST lower upper) (state : State) (addresses : List Key)
        {before after sources targets : List (RawTree Nat)} {cost budget : Nat},
        (∀ address ∈ addresses, referenceAt reference.toRaw address ≠ .empty) →
        domains before = domains (forest state reference.toRaw) →
        domains sources = domains (forest state reference.toRaw) →
        SplayTrace before (historyWord reference.toRaw state addresses) after cost →
        Program sources (historyWord reference.toRaw state addresses) targets budget →
        cost ≤ constant * (2 * reference.size + 1 + budget) *
          Splay.Analysis.targetFactor reference.height := by
  obtain ⟨constant,positive,bound⟩ := CommonForest.forest_splay_bound
  refine ⟨constant,positive,?_⟩
  intro lower upper reference state addresses before after sources targets cost budget real actualKeys comparatorKeys actual comparator
  have unique : (inorder reference.toRaw).Nodup :=
    reference.toRaw_ordered.imp (fun less => ne_of_lt less)
  have distinct := history_distinct actual (unique_from_domains actualKeys unique)
  have paid := bound Nat reference.height comparator (capacity_from_domains reference comparatorKeys)
    (history_joinFits reference state addresses real) distinct (actualKeys.trans comparatorKeys.symm)
  rw [initialization_from_domains actualKeys, DynamicOptimality.BST.toRaw_size] at paid
  exact paid

/-- Specialization to arbitrary requests from the actual finite key universe.
Reference addresses are generated from the keys, so no address-validity
premise remains. Empty universes and empty request lists are included. -/
theorem finite_history_splay_bound :
    ∃ constant : Nat, 0 < constant ∧
      ∀ {n : Nat} (reference : BST 0 n) (state : State) (requests : List (Fin n))
        {before after sources targets : List (RawTree Nat)} {cost budget : Nat},
        domains before = domains (forest state reference.toRaw) →
        domains sources = domains (forest state reference.toRaw) →
        SplayTrace before
          (historyWord reference.toRaw state (requests.map fun key => nodeAddress reference key.val)) after cost →
        Program sources
          (historyWord reference.toRaw state (requests.map fun key => nodeAddress reference key.val)) targets budget →
        cost ≤ constant * (2 * n + 1 + budget) * Splay.Analysis.targetFactor reference.height := by
  obtain ⟨constant,positive,bound⟩ := history_splay_bound
  refine ⟨constant,positive,?_⟩
  intro n reference state requests before after sources targets cost budget actualKeys comparatorKeys actual comparator
  have real : ∀ address ∈ requests.map (fun key => nodeAddress reference key.val),
      referenceAt reference.toRaw address ≠ .empty := by
    intro address member
    obtain ⟨key,_,rfl⟩ := List.mem_map.mp member
    obtain ⟨left,right,found⟩ := referenceAt_nodeAddress reference (Nat.zero_le key.val) key.isLt
    simp [found]
  simpa only [Splay.Tree.BST.size_eq_upper] using
    bound reference state _ real actualKeys comparatorKeys actual comparator

end MultiSplay.ClassicalSwitch.Accounting
