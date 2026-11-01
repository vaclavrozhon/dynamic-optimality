import Splay.Lazy.AtomicInitialization

namespace Splay.Lazy

private theorem totalInserts_append
    {n : ℕ} (first second : List (Interface.Operation n)) :
    Interface.totalInserts (first ++ second) =
      Interface.totalInserts first + Interface.totalInserts second := by
  simp [Interface.totalInserts]

private theorem totalIncreases_append
    {n : ℕ} (first second : List (Interface.Operation n)) :
    Interface.totalIncreases (first ++ second) =
      Interface.totalIncreases first + Interface.totalIncreases second := by
  simp [Interface.totalIncreases]

namespace Canonical

open Splay.Rank

/-- Creating empty placements contributes no insert operations. -/
theorem totalInserts_createPlacementEvents_eq_zero
    {n : ℕ} (placements : List (Element n × Side)) :
    Interface.totalInserts
        (eraseOperations (createPlacementEvents placements)) = 0 := by
  induction placements with
  | nil =>
      rfl
  | cons placement placements ih =>
      simpa [createPlacementEvents, eraseOperations, Event.operations,
        Interface.totalInserts, Interface.Operation.insertCount] using ih

/-- Creating empty placements contributes no increasing value operations. -/
theorem totalIncreases_createPlacementEvents_eq_zero
    {n : ℕ} (placements : List (Element n × Side)) :
    Interface.totalIncreases
        (eraseOperations (createPlacementEvents placements)) = 0 := by
  induction placements with
  | nil =>
      rfl
  | cons placement placements ih =>
      simpa [createPlacementEvents, eraseOperations, Event.operations,
        Interface.totalIncreases, Interface.Operation.increaseCount] using ih

/--
There are exactly `2 * n` canonical non-root endpoints.
-/
theorem canonicalAllElements_length
    {n : ℕ} (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (canonicalAllElements snapshot tree).length = 2 * n := by
  let root := canonicalRoot snapshot tree
  have subset :
      (canonicalAllElements snapshot tree).toFinset ⊆
        (Finset.univ.erase root : Finset (Element n)) := by
    intro element member
    rw [List.mem_toFinset] at member
    rw [Finset.mem_erase]
    exact
      ⟨(mem_canonicalAllElements_iff_ne_root
          snapshot tree element).mp member,
        Finset.mem_univ element⟩
  have reverseSubset :
      (Finset.univ.erase root : Finset (Element n)) ⊆
        (canonicalAllElements snapshot tree).toFinset := by
    intro element member
    rw [Finset.mem_erase] at member
    rw [List.mem_toFinset]
    exact
      (mem_canonicalAllElements_iff_ne_root
        snapshot tree element).mpr member.1
  have finsetEq :
      (canonicalAllElements snapshot tree).toFinset =
        (Finset.univ.erase root : Finset (Element n)) :=
    Finset.Subset.antisymm subset reverseSubset
  have rootMem :
      root ∈ (Finset.univ : Finset (Element n)) :=
    Finset.mem_univ root
  calc
    (canonicalAllElements snapshot tree).length =
        (canonicalAllElements snapshot tree).toFinset.card :=
      (List.toFinset_card_of_nodup
        (canonicalAllElements_nodup snapshot tree)).symm
    _ = (Finset.univ.erase root : Finset (Element n)).card := by
      rw [finsetEq]
    _ = (Finset.univ : Finset (Element n)).card - 1 :=
      Finset.card_erase_of_mem rootMem
    _ = 2 * n := by
      simp [Fintype.card_fin]

/-- The atomic initializer performs exactly one insert per non-root endpoint. -/
theorem atomicInitialization_totalInserts
    {n : ℕ} (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    Interface.totalInserts
        (eraseOperations
          (atomicInitialization snapshot tree params
            growingLimit valueBound).events) =
      2 * n := by
  let population :=
    atomicPopulation snapshot tree params growingLimit valueBound
  change
    Interface.totalInserts
        (eraseOperations
          (((emptyCanonicalState snapshot tree).adjustValuesToOneEvents
              (allInterfaceElements n) ++
            createPlacementEvents (ownerSidePairs n)) ++
          population.events)) =
      2 * n
  rw [eraseOperations_append, eraseOperations_append,
    totalInserts_append, totalInserts_append]
  rw [State.totalInserts_adjustValuesToOneEvents_eq_zero,
    totalInserts_createPlacementEvents_eq_zero,
    population.totalInserts_eq, zero_add, zero_add,
    canonicalAllElements_length]

/--
The atomic initializer performs exactly one increasing value operation per
non-root endpoint.  All preparation value changes are decreases.
-/
theorem atomicInitialization_totalIncreases
    {n : ℕ} (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    Interface.totalIncreases
        (eraseOperations
          (atomicInitialization snapshot tree params
            growingLimit valueBound).events) =
      2 * n := by
  let population :=
    atomicPopulation snapshot tree params growingLimit valueBound
  change
    Interface.totalIncreases
        (eraseOperations
          (((emptyCanonicalState snapshot tree).adjustValuesToOneEvents
              (allInterfaceElements n) ++
            createPlacementEvents (ownerSidePairs n)) ++
          population.events)) =
      2 * n
  rw [eraseOperations_append, eraseOperations_append,
    totalIncreases_append, totalIncreases_append]
  rw [State.totalIncreases_adjustValuesToOneEvents_eq_zero
      (valid :=
        emptyCanonicalState_valid snapshot tree params valueBound),
    totalIncreases_createPlacementEvents_eq_zero,
    population.totalIncreases_eq, zero_add, zero_add,
    canonicalAllElements_length]

end Canonical

end Splay.Lazy
