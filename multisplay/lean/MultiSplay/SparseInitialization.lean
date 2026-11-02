import MultiSplay.SparseForest
import MultiSplay.OrdinalEncoding

/-!
# Initializing a sparse forest once

Initial representations are constructed from the exact source shapes. All later
splits, joins, rotations, and services use the compiler's persistent states.
-/

namespace MultiSplay.SparseHeavy

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (size)

variable {α : Type*} [Inhabited α]

theorem state_exists (capacity : Nat) (source : RawTree α) (fits : size source ≤ capacity) :
    ∃ state : State capacity α, state.source = source := by
  obtain ⟨upper, indexed, alphabet, same, upperEq⟩ := Alphabet.exists_encoding source
  have indexedFits : indexed.size ≤ capacity := by
    rw [indexed.size_eq_upper, upperEq]
    exact fits
  obtain ⟨actual, ⟨representation⟩⟩ :=
    Splay.Accounting.OfflineConnectedSupport.HeavyRepresentation.exists_representation capacity indexed indexedFits
  exact ⟨⟨.ofRepresentation representation indexedFits, alphabet⟩, same⟩

theorem initial_exists (capacity : Nat) (sources : List (RawTree α))
    (fits : CommonForest.Capacity capacity sources) :
    ∃ initial : List (State capacity α), initial.map State.source = sources := by
  induction sources with
  | nil => exact ⟨[], rfl⟩
  | cons head tail ih =>
      obtain ⟨state, sourceEq⟩ := state_exists capacity head (fits head (by simp))
      obtain ⟨initial, initialEq⟩ := ih (fun tree member => fits tree (by simp [member]))
      exact ⟨state :: initial, by simp [sourceEq, initialEq]⟩

/-- Complete existence statement from the actual input program; no normalizer
witnesses or favorable starting representations are assumptions. -/
theorem program_exists {capacity : Nat} {sources targets : List (RawTree α)}
    {word : List (CommonForest.Event α)} {charge : Nat}
    (program : CommonForest.Program sources word targets charge)
    (fits : CommonForest.Capacity capacity sources)
    (joins : ∀ event ∈ word, CommonForest.Domains.JoinFits capacity event) :
    ∃ initial final : List (State capacity α), ∃ cost : Nat,
      initial.map State.source = sources ∧ final.map State.source = targets ∧
      PhysicalTrace (initial.map State.actual) word (final.map State.actual) cost ∧
      cost ≤ 1152 * Forest.potential size sources + 8352 * charge := by
  obtain ⟨initial, sourceEq⟩ := initial_exists capacity sources fits
  obtain ⟨final, cost, targetEq, run, bound⟩ := forest_exists initial (sourceEq ▸ program) joins
  have initialSize : Forest.potential State.size initial = Forest.potential size sources := by
    rw [← sourceEq]
    simp only [Forest.potential, List.map_map, Function.comp_def, State.source_size]
  exact ⟨initial, final, cost, sourceEq, targetEq, run, by simpa [initialSize] using bound⟩

end MultiSplay.SparseHeavy

namespace MultiSplay.SparseRib

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (size)

variable {α : Type*} [Inhabited α]

theorem state_exists (capacity : Nat) (source : RawTree α) (fits : size source ≤ capacity) :
    ∃ state : State capacity α, state.source = source := by
  obtain ⟨upper, indexed, alphabet, same, upperEq⟩ := Alphabet.exists_encoding source
  have indexedFits : indexed.size ≤ capacity := by
    rw [indexed.size_eq_upper, upperEq]
    exact fits
  obtain ⟨actual, ⟨representation⟩⟩ :=
    Splay.Accounting.OfflineConnectedSupport.RibRepresentation.exists_representation capacity false indexed indexedFits
  exact ⟨⟨.ofRepresentation representation indexedFits, alphabet⟩, same⟩

theorem initial_exists (capacity : Nat) (sources : List (RawTree α))
    (fits : CommonForest.Capacity capacity sources) :
    ∃ initial : List (State capacity α), initial.map State.source = sources := by
  induction sources with
  | nil => exact ⟨[], rfl⟩
  | cons head tail ih =>
      obtain ⟨state, sourceEq⟩ := state_exists capacity head (fits head (by simp))
      obtain ⟨initial, initialEq⟩ := ih (fun tree member => fits tree (by simp [member]))
      exact ⟨state :: initial, by simp [sourceEq, initialEq]⟩

/-- Complete existence statement from the actual input program; no normalizer
witnesses or favorable starting representations are assumptions. -/
theorem program_exists {capacity : Nat} {sources targets : List (RawTree α)}
    {word : List (CommonForest.Event α)} {charge : Nat}
    (program : CommonForest.Program sources word targets charge)
    (fits : CommonForest.Capacity capacity sources)
    (joins : ∀ event ∈ word, CommonForest.Domains.JoinFits capacity event) :
    ∃ initial final : List (State capacity α), ∃ cost : Nat,
      initial.map State.source = sources ∧ final.map State.source = targets ∧
      PhysicalTrace (initial.map State.actual) word (final.map State.actual) cost ∧
      cost ≤ 4608 * Forest.potential size sources + 48492 * charge := by
  obtain ⟨initial, sourceEq⟩ := initial_exists capacity sources fits
  obtain ⟨final, cost, targetEq, run, bound⟩ := forest_exists initial (sourceEq ▸ program) joins
  have initialSize : Forest.potential State.size initial = Forest.potential size sources := by
    rw [← sourceEq]
    simp only [Forest.potential, List.map_map, Function.comp_def, State.source_size]
  exact ⟨initial, final, cost, sourceEq, targetEq, run, by simpa [initialSize] using bound⟩

end MultiSplay.SparseRib
