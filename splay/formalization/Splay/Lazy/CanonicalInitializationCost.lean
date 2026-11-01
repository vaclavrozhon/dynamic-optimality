import Splay.Lazy.CanonicalInitializationTrace
import Splay.Lazy.CanonicalBlockCount
import Splay.Lazy.SafeInsertCost

namespace Splay.Lazy.Canonical

open Splay.Rank

private theorem safeInsert_increases_le_of_values {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (block : Block n) (element : Element n) {bound : ℕ}
    (two : 2 ≤ bound) (values : ∀ element, 1 ≤ state.value element ∧ state.value element ≤ bound) :
    Interface.totalIncreases (eraseOperations (state.safeInsertEvents blockId block element)) ≤ 3 * bound := by
  have creatorPositive := (values block.creator).1
  have creatorBound := (values block.creator).2
  have elementBound := (values element).2
  simp only [State.safeInsertEvents, eraseOperations_append, Interface.totalIncreases_append,
    State.totalIncreases_adjustValueEvents]
  have noCreatorIncrease : 1 - state.value block.creator = 0 := by omega
  rw [noCreatorIncrease]
  change 0 + (2 - _) + 0 + (state.value element - _) + (state.value block.creator - _) ≤ _
  omega

@[simp] theorem insertManyEvents_inserts {n : ℕ} (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (elements : List (Element n)) :
    Interface.totalInserts (eraseOperations (insertManyEvents state blockId block elements)) = elements.length := by
  induction elements generalizing state block with
  | nil => rfl
  | cons element elements ih =>
      simp only [insertManyEvents, eraseOperations_append, Interface.totalInserts_append,
        State.safeInsertEvents_totalInserts, ih, List.length_cons]
      omega

@[simp] theorem insertManyEvents_activity {n : ℕ} (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (elements : List (Element n)) :
    Interface.totalActivity (eraseOperations (insertManyEvents state blockId block elements)) = 0 := by
  induction elements generalizing state block with
  | nil => rfl
  | cons element elements ih => simp only [insertManyEvents, eraseOperations_append,
      Interface.totalActivity_append, State.safeInsertEvents_totalActivity, ih, Nat.zero_add]

theorem insertManyEvents_increases {n : ℕ} (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (elements : List (Element n)) {bound : ℕ}
    (two : 2 ≤ bound) (values : ∀ element, 1 ≤ state.value element ∧ state.value element ≤ bound) :
    Interface.totalIncreases (eraseOperations (insertManyEvents state blockId block elements)) ≤ 3 * bound * elements.length := by
  induction elements generalizing state block with
  | nil => simp [insertManyEvents, eraseOperations, Interface.totalIncreases]
  | cons element elements ih =>
      have head := safeInsert_increases_le_of_values state blockId block element two values
      have tail := ih (state.insert blockId element) (block.inserted element) values
      simp only [insertManyEvents, eraseOperations_append, Interface.totalIncreases_append, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- Number of actual heap children inserted over the selected placements. -/
noncomputable def canonicalPlacementMass {n : ℕ} (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (placements : List (Element n × Side)) : ℕ :=
  (placements.map fun placement => (canonicalInsertionSequence snapshot tree placement).length).sum

@[simp] theorem populateCanonicalPlacementEvents_inserts {n : ℕ} (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (state : State n) (blockId : Interface.BlockId) (placements : List (Element n × Side)) :
    Interface.totalInserts (eraseOperations (populateCanonicalPlacementEvents snapshot tree state blockId placements)) =
      canonicalPlacementMass snapshot tree placements := by
  induction placements generalizing state blockId with
  | nil => rfl
  | cons placement placements ih =>
      simp only [populateCanonicalPlacementEvents, eraseOperations_append, Interface.totalInserts_append,
        insertManyEvents_inserts, ih, canonicalPlacementMass, List.map_cons, List.sum_cons]

@[simp] theorem populateCanonicalPlacementEvents_activity {n : ℕ} (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (state : State n) (blockId : Interface.BlockId) (placements : List (Element n × Side)) :
    Interface.totalActivity (eraseOperations (populateCanonicalPlacementEvents snapshot tree state blockId placements)) = 0 := by
  induction placements generalizing state blockId with
  | nil => rfl
  | cons placement placements ih => simp only [populateCanonicalPlacementEvents, eraseOperations_append,
      Interface.totalActivity_append, insertManyEvents_activity, ih, Nat.zero_add]

theorem populateCanonicalPlacementEvents_increases {n : ℕ} (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (state : State n) (blockId : Interface.BlockId) (placements : List (Element n × Side)) {bound : ℕ}
    (two : 2 ≤ bound) (values : ∀ element, 1 ≤ state.value element ∧ state.value element ≤ bound) :
    Interface.totalIncreases (eraseOperations (populateCanonicalPlacementEvents snapshot tree state blockId placements)) ≤
      3 * bound * canonicalPlacementMass snapshot tree placements := by
  induction placements generalizing state blockId with
  | nil => simp [populateCanonicalPlacementEvents, eraseOperations, Interface.totalIncreases, canonicalPlacementMass]
  | cons placement placements ih =>
      have head := insertManyEvents_increases state blockId (Block.emptyGrowing placement.1 placement.2)
        (canonicalInsertionSequence snapshot tree placement) two values
      have tail := ih (insertMany state blockId (canonicalInsertionSequence snapshot tree placement)) (blockId + 1)
        (by simpa only [insertMany_value] using values)
      simp only [populateCanonicalPlacementEvents, eraseOperations_append, Interface.totalIncreases_append,
        canonicalPlacementMass, List.map_cons, List.sum_cons, Nat.mul_add]
      change _ ≤ _ + 3 * bound * canonicalPlacementMass snapshot tree placements
      omega

theorem canonicalPlacementMass_all {n : ℕ} (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    canonicalPlacementMass snapshot tree (ownerSidePairs n) = (canonicalAllElements snapshot tree).length := by
  rw [canonicalAllElements_eq_flatMap_topDown, List.length_flatMap]
  simp only [canonicalPlacementMass, canonicalInsertionSequence, List.length_reverse]

theorem canonicalPlacementMass_le {n : ℕ} (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    canonicalPlacementMass snapshot tree (ownerSidePairs n) ≤ 2 * n + 1 := by
  rw [canonicalPlacementMass_all]
  simpa only [Fintype.card_fin] using (canonicalAllElements_nodup snapshot tree).length_le_card

@[simp] theorem createPlacementEvents_inserts {n : ℕ} (placements : List (Element n × Side)) :
    Interface.totalInserts (eraseOperations (createPlacementEvents placements)) = 0 := by
  induction placements with
  | nil => rfl
  | cons placement placements ih => simpa [createPlacementEvents, eraseOperations, Event.operations,
      Interface.totalInserts, Interface.Operation.insertCount] using ih

@[simp] theorem createPlacementEvents_increases {n : ℕ} (placements : List (Element n × Side)) :
    Interface.totalIncreases (eraseOperations (createPlacementEvents placements)) = 0 := by
  induction placements with
  | nil => rfl
  | cons placement placements ih => simpa [createPlacementEvents, eraseOperations, Event.operations,
      Interface.totalIncreases, Interface.Operation.increaseCount] using ih

@[simp] theorem createPlacementEvents_activity {n : ℕ} (placements : List (Element n × Side)) :
    Interface.totalActivity (eraseOperations (createPlacementEvents placements)) = 0 := by
  induction placements with
  | nil => rfl
  | cons placement placements ih => simpa [createPlacementEvents, eraseOperations, Event.operations,
      Interface.totalActivity, Interface.Operation.activity] using ih

theorem canonicalInitializationEvents_inserts {n : ℕ} (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    Interface.totalInserts (eraseOperations (canonicalInitializationEvents snapshot tree)) ≤ 2 * n + 1 := by
  simp only [canonicalInitializationEvents, eraseOperations_append, Interface.totalInserts_append,
    createPlacementEvents_inserts, populateCanonicalPlacementEvents_inserts, Nat.zero_add]
  exact canonicalPlacementMass_le snapshot tree

@[simp] theorem canonicalInitializationEvents_activity {n : ℕ} (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    Interface.totalActivity (eraseOperations (canonicalInitializationEvents snapshot tree)) = 0 := by
  simp only [canonicalInitializationEvents, eraseOperations_append, Interface.totalActivity_append,
    createPlacementEvents_activity, populateCanonicalPlacementEvents_activity, Nat.zero_add]

theorem canonicalInitializationEvents_increases {n : ℕ} (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters) (valueBound : Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    Interface.totalIncreases (eraseOperations (canonicalInitializationEvents snapshot tree)) ≤
      3 * params.valueBound * (2 * n + 1) := by
  simp only [canonicalInitializationEvents, eraseOperations_append, Interface.totalIncreases_append,
    createPlacementEvents_increases, Nat.zero_add]
  apply (populateCanonicalPlacementEvents_increases snapshot tree _ _ _ params.valueBound_ge_two ?_).trans
    (Nat.mul_le_mul_left _ (canonicalPlacementMass_le snapshot tree))
  intro element
  rw [emptyCanonicalBlocksState_value]
  exact ⟨canonicalValue_pos snapshot tree element,
    (canonicalValue_le_contractedGap_maxRank snapshot tree element).trans valueBound⟩

end Splay.Lazy.Canonical
