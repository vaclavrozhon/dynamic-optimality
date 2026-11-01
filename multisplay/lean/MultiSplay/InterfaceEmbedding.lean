import MultiSplay.InterfaceExcess
import Mathlib.Logic.Function.Basic

/-!
# One fixed interface universe for a changing forest

An injective embedding preserves every old block identifier, creator identity,
pass counter, and element order. New universe slots have neutral value one.
This permits a finite forest history to reserve all future pivot and gap slots
without introducing an initialization charge for those dormant slots.
-/

namespace MultiSplay.InterfaceEmbedding

open Splay.Interface

variable {n m : Nat}

def block (embedding : Element n → Element m) (source : Block n) : Block m :=
  ⟨embedding source.creator, source.passCount, source.mode, source.elements.map embedding⟩

def pairing (embedding : Element n → Element m) (source : Pairing n) : Pairing m :=
  ⟨embedding source.winner, embedding source.loser, source.destination⟩

def operation (embedding : Element n → Element m) : Operation n → Operation m
  | .convert id => .convert id
  | .create creator => .create (embedding creator)
  | .insert id element => .insert id (embedding element)
  | .delete id element => .delete id (embedding element)
  | .pass id pairs => .pass id (pairs.map (pairing embedding))
  | .split id count => .split id count
  | .valueChange element delta => .valueChange (embedding element) delta

noncomputable def state (embedding : Element n → Element m) (source : State n) : State m :=
  ⟨source.blocks.map (block embedding), Function.extend embedding source.value (fun _ => 1)⟩

@[simp] theorem value_image (embedding : Element n → Element m) (injective : Function.Injective embedding)
    (source : State n) (element : Element n) :
    (state embedding source).value (embedding element) = source.value element :=
  by simpa only [state] using injective.extend_apply source.value (fun _ => 1) element

theorem value_outside (embedding : Element n → Element m) (source : State n) (element : Element m)
    (outside : ¬ ∃ old, embedding old = element) : (state embedding source).value element = 1 :=
  by simpa only [state] using Function.extend_apply' source.value (fun _ => 1) element outside

@[simp] theorem allElements (embedding : Element n → Element m) (source : State n) :
    (state embedding source).allElements = source.allElements.map embedding := by
  simp only [state, State.allElements, List.flatMap_map, List.map_flatMap, block]

@[simp] theorem found (embedding : Element n → Element m) (source : State n) (id : BlockId) :
    (state embedding source).block? id = (source.block? id).map (block embedding) := by
  simp [state, State.block?]

@[simp] theorem growing_image (embedding : Element n → Element m) (injective : Function.Injective embedding)
    (source : State n) (creator : Element n) :
    (state embedding source).growingCount (embedding creator) = source.growingCount creator := by
  simp [state, State.growingCount, List.filter_map, Function.comp_def, block, injective.eq_iff]
  rfl

theorem growing_outside (embedding : Element n → Element m) (source : State n) (creator : Element m)
    (outside : ¬ ∃ old, embedding old = creator) : (state embedding source).growingCount creator = 0 := by
  have noCreator : ∀ old, embedding old ≠ creator := fun old same => outside ⟨old, same⟩
  simp [state, State.growingCount, List.filter_map, Function.comp_def, block, noCreator]

theorem valid (embedding : Element n → Element m) (injective : Function.Injective embedding)
    {params : Parameters} {source : State n} (valid : source.Valid params) :
    (state embedding source).Valid params := by
  refine ⟨?_, ?_, ?_⟩
  · rw [allElements]
    exact valid.1.map injective
  · intro element
    by_cases member : ∃ old, embedding old = element
    · obtain ⟨old, rfl⟩ := member
      simpa only [value_image embedding injective] using valid.2.1 old
    · rw [value_outside embedding source element member]
      have bound := params.valueBound_ge_two
      omega
  · intro creator
    by_cases member : ∃ old, embedding old = creator
    · obtain ⟨old, rfl⟩ := member
      simpa [growing_image embedding injective] using valid.2.2 old
    · rw [growing_outside embedding source creator member]
      exact Nat.zero_le _

theorem initial (embedding : Element n → Element m) (injective : Function.Injective embedding)
    {params : Parameters} {source : State n} (initialized : source.Initial params) :
    (state embedding source).Initial params :=
  ⟨valid embedding injective initialized.1, by simp [state, initialized.2]⟩

private theorem map_modify {α β : Type*} (map : α → β) (update : α → α) (newUpdate : β → β)
    (commutes : ∀ x, map (update x) = newUpdate (map x)) (values : List α) (id : Nat) :
    (values.modify id update).map map = (values.map map).modify id newUpdate := by
  induction values generalizing id with
  | nil => cases id <;> rfl
  | cons head tail ih => cases id <;> simp [commutes, ih]

theorem removeLosers_map (embedding : Element n → Element m) (injective : Function.Injective embedding)
    (elements : List (Element n)) (pairs : List (Pairing n)) :
    (removeLosers elements pairs).map embedding =
      removeLosers (elements.map embedding) (pairs.map (pairing embedding)) := by
  induction pairs generalizing elements with
  | nil => rfl
  | cons head tail ih =>
      simp only [removeLosers, List.foldl_cons, List.map_cons]
      simpa only [removeLosers, List.map_erase injective, pairing] using ih (elements.erase head.loser)

theorem insertAtDestinations_map (embedding : Element n → Element m)
    (blocks : List (Block n)) (pairs : List (Pairing n)) :
    (insertAtDestinations blocks pairs).map (block embedding) =
      insertAtDestinations (blocks.map (block embedding)) (pairs.map (pairing embedding)) := by
  induction pairs generalizing blocks with
  | nil => rfl
  | cons head tail ih =>
      simp only [insertAtDestinations, List.foldl_cons, List.map_cons, pairing]
      simp only [insertAtDestinations] at ih
      rw [ih]
      rw [map_modify (block embedding) _ (fun old => {old with elements := embedding head.loser :: old.elements})
        (fun _ => rfl)]

theorem passBlocks_map (embedding : Element n → Element m) (injective : Function.Injective embedding)
    (blocks : List (Block n)) (id : BlockId) (source : Block n) (pairs : List (Pairing n)) :
    (passBlocks blocks id source pairs).map (block embedding) =
      passBlocks (blocks.map (block embedding)) id (block embedding source) (pairs.map (pairing embedding)) := by
  unfold passBlocks
  rw [insertAtDestinations_map]
  rw [map_modify (block embedding) _ (fun _ => { (block embedding source) with
      passCount := source.passCount + 1
      elements := removeLosers (source.elements.map embedding) (pairs.map (pairing embedding)) })
    (fun _ => by simp [block, removeLosers_map embedding injective])]
  rfl

theorem splitBlocks_map (embedding : Element n → Element m)
    (blocks : List (Block n)) (id : BlockId) (source : Block n) (count : Nat) :
    (splitBlocks blocks id source count).map (block embedding) =
      splitBlocks (blocks.map (block embedding)) id (block embedding source) count := by
  unfold splitBlocks
  rw [List.map_append, map_modify (block embedding) _ (fun old => {old with elements := []}) (fun _ => rfl)]
  simp [block, List.map_take, List.map_drop]

theorem adjacent_map (embedding : Element n → Element m) {elements : List (Element n)} {a b : Element n}
    (adjacent : Adjacent elements a b) : Adjacent (elements.map embedding) (embedding a) (embedding b) := by
  obtain ⟨front, back, forward | backward⟩ := adjacent
  · exact ⟨front.map embedding, back.map embedding, Or.inl (by simp [forward])⟩
  · exact ⟨front.map embedding, back.map embedding, Or.inr (by simp [backward])⟩

theorem pairing_valid (embedding : Element n → Element m) (injective : Function.Injective embedding)
    (source : State n) (id : BlockId) (sourceBlock : Block n) (pair : Pairing n)
    (legal : PairingValid source id sourceBlock pair) :
    PairingValid (state embedding source) id (block embedding sourceBlock) (pairing embedding pair) := by
  obtain ⟨adjacent, order, different, destination, lookup, growing, creator⟩ := legal
  refine ⟨adjacent_map embedding adjacent, ?_, different, block embedding destination, ?_, growing, ?_⟩
  · simpa only [pairing, value_image embedding injective] using order
  · simp only [pairing, found, lookup, Option.map_some]
  · change embedding destination.creator = embedding pair.winner
    rw [creator]

theorem matching_valid (embedding : Element n → Element m) (injective : Function.Injective embedding)
    (params : Parameters) (source : State n) (id : BlockId) (sourceBlock : Block n) (pairs : List (Pairing n))
    (legal : MatchingValid params source id sourceBlock pairs) :
    MatchingValid params (state embedding source) id (block embedding sourceBlock) (pairs.map (pairing embedding)) := by
  refine ⟨legal.1, ?_, ?_, ?_, ?_⟩
  · simpa [List.flatMap_map, List.map_flatMap, pairing] using legal.2.1.map injective
  · simpa [List.map_map, Function.comp_def, pairing] using legal.2.2.1
  · intro pair member
    obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp member
    exact pairing_valid embedding injective source id sourceBlock old (legal.2.2.2.1 old oldMem)
  · simpa [block] using legal.2.2.2.2

theorem update_value (embedding : Element n → Element m) (injective : Function.Injective embedding)
    (values : Element n → Nat) (element : Element n) (value : Nat) :
    Function.extend embedding (Function.update values element value) (fun _ => 1) =
      Function.update (Function.extend embedding values (fun _ => 1)) (embedding element) value := by
  classical
  funext target
  by_cases member : ∃ old, embedding old = target
  · obtain ⟨old, rfl⟩ := member
    simp [injective.extend_apply, Function.update_apply, injective.eq_iff]
  · have different : target ≠ embedding element := fun same => member ⟨element, same.symm⟩
    simp [Function.extend_apply' _ _ _ member, different]

theorem effect (embedding : Element n → Element m) (injective : Function.Injective embedding)
    {params : Parameters} {before after : State n} {op : Operation n}
    (execution : Effect params before op after) :
    Effect params (state embedding before) (operation embedding op) (state embedding after) := by
  cases execution with
  | convert lookup growing blocksEq valuesEq =>
      rename_i id oldBlock
      refine .convert (block := block embedding oldBlock) (by simp only [found, lookup, Option.map_some]) growing ?_ ?_
      · change after.blocks.map (block embedding) = _
        rw [blocksEq, map_modify (block embedding) _ (fun old => {old with mode := .shrinking}) (fun _ => rfl)]
        rfl
      · simp only [state, valuesEq]
  | create room blocksEq valuesEq =>
      refine .create ?_ ?_ ?_
      · simpa only [growing_image embedding injective] using room
      · simp only [state, blocksEq, List.map_append, List.map_cons, List.map_nil, block]
      · simp only [state, valuesEq]
  | insert lookup growing unassigned ordered blocksEq valuesEq =>
      rename_i id oldBlock element
      refine .insert (block := block embedding oldBlock) (by simp only [found, lookup, Option.map_some]) growing ?_ ?_ ?_ ?_
      · simpa only [allElements, List.mem_map, injective.eq_iff, exists_eq_right] using unassigned
      · simpa only [block, value_image embedding injective] using ordered
      · change after.blocks.map (block embedding) = _
        rw [blocksEq, map_modify (block embedding) _ (fun old => {old with elements := embedding element :: old.elements}) (fun _ => rfl)]
        rfl
      · simp only [state, valuesEq]
  | delete lookup shrinking present blocksEq valuesEq =>
      rename_i id oldBlock element
      refine .delete (block := block embedding oldBlock) (by simp only [found, lookup, Option.map_some]) shrinking ?_ ?_ ?_
      · exact List.mem_map.mpr ⟨_, present, rfl⟩
      · change after.blocks.map (block embedding) = _
        rw [blocksEq, map_modify (block embedding) _ (fun old => {old with elements := old.elements.erase (embedding element)})
          (fun old => by simp [block, List.map_erase injective])]
        rfl
      · simp only [state, valuesEq]
  | pass lookup matching blocksEq valuesEq =>
      refine .pass (by simp only [found, lookup, Option.map_some]) (matching_valid embedding injective _ _ _ _ _ matching) ?_ ?_
      · change after.blocks.map (block embedding) = _
        rw [blocksEq, passBlocks_map embedding injective]
        rfl
      · simp only [state, valuesEq]
  | split lookup shrinking prefixLe blocksEq valuesEq =>
      rename_i id oldBlock count
      refine .split (source := block embedding oldBlock) (by simp only [found, lookup, Option.map_some]) shrinking ?_ ?_ ?_
      · simpa [block] using prefixLe
      · change after.blocks.map (block embedding) = _
        rw [blocksEq, splitBlocks_map]
        rfl
      · simp only [state, valuesEq]
  | decrease allowed blocksEq valuesEq =>
      refine .decrease ?_ ?_ ?_
      · simpa only [value_image embedding injective] using allowed
      · simp only [state, blocksEq]
      · simp only [state, valuesEq, update_value embedding injective, injective.extend_apply]
  | increase allowed blocksEq valuesEq =>
      refine .increase ?_ ?_ ?_
      · simpa only [value_image embedding injective] using allowed
      · simp only [state, blocksEq]
      · simp only [state, valuesEq, update_value embedding injective, injective.extend_apply]

theorem step (embedding : Element n → Element m) (injective : Function.Injective embedding)
    {params : Parameters} {before after : State n} {op : Operation n}
    (execution : Step params before op after) :
    Step params (state embedding before) (operation embedding op) (state embedding after) :=
  ⟨valid embedding injective execution.1, effect embedding injective execution.2.1,
    valid embedding injective execution.2.2⟩

/-- A whole chronological history is embedded at once, with precisely the
same block identifiers and no inserted operations. -/
theorem trace (embedding : Element n → Element m) (injective : Function.Injective embedding)
    {params : Parameters} {before after : State n} {word : List (Operation n)}
    (execution : Trace params before word after) :
    Trace params (state embedding before) (word.map (operation embedding)) (state embedding after) := by
  induction execution with
  | nil bounded => exact .nil (valid embedding injective bounded)
  | cons head tail ih => exact .cons (step embedding injective head) ih

@[simp] theorem activity (embedding : Element n → Element m) (word : List (Operation n)) :
    totalActivity (word.map (operation embedding)) = totalActivity word := by
  induction word with
  | nil => rfl
  | cons head tail ih => cases head <;> simp_all [totalActivity, operation, Operation.activity]

@[simp] theorem inserts (embedding : Element n → Element m) (word : List (Operation n)) :
    totalInserts (word.map (operation embedding)) = totalInserts word := by
  induction word with
  | nil => rfl
  | cons head tail ih => cases head <;> simp_all [totalInserts, operation, Operation.insertCount]

@[simp] theorem increases (embedding : Element n → Element m) (word : List (Operation n)) :
    totalIncreases (word.map (operation embedding)) = totalIncreases word := by
  induction word with
  | nil => rfl
  | cons head tail ih =>
      cases head <;> simp_all [totalIncreases, operation, Operation.increaseCount]
      rename_i element delta
      cases delta <;> rfl

@[simp] theorem decreases (embedding : Element n → Element m) (word : List (Operation n)) :
    totalDecreases (word.map (operation embedding)) = totalDecreases word := by
  induction word with
  | nil => rfl
  | cons head tail ih =>
      cases head <;> simp_all [totalDecreases, operation, Operation.decreaseCount]
      rename_i element delta
      cases delta <;> rfl

/-- Reserving arbitrarily many neutral slots preserves the exact initial
excess, not merely a bound proportional to the enlarged universe. -/
@[simp] theorem excess (embedding : Element n → Element m) (injective : Function.Injective embedding)
    (source : State n) : InterfaceForest.excess (state embedding source) = InterfaceForest.excess source := by
  classical
  unfold InterfaceForest.excess
  calc
    ∑ element : Element m, ((state embedding source).value element - 1) =
        ∑ element ∈ Finset.univ.image embedding, ((state embedding source).value element - 1) := by
      symm
      apply Finset.sum_subset (by simp)
      intro element member outside
      have notImage : ¬ ∃ old, embedding old = element := by
        rintro ⟨old, same⟩
        exact outside (Finset.mem_image.mpr ⟨old, Finset.mem_univ _, same⟩)
      rw [value_outside embedding source element notImage]
      rfl
    _ = ∑ old : Element n, ((state embedding source).value (embedding old) - 1) := by
      rw [Finset.sum_image]
      intro a _ b _ same
      exact injective same
    _ = ∑ old : Element n, (source.value old - 1) := by
      apply Finset.sum_congr rfl
      intro element _
      rw [value_image embedding injective]

end MultiSplay.InterfaceEmbedding
