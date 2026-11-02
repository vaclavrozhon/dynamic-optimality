import MultiSplay.LayeredServices

/-!
# A complete sparse program through both persistent normalizer layers

Every primitive, split, and join is compiled chronologically. The representation
of each output component has height at most `30 * clog(2, K + 1)^3` and bounded
minor ribs, where `K` is the common component capacity. Its construction retains
both layers' child histories. The cost has one initial size term.

This endpoint-and-cost theorem does not yet assert the geometry of every
pointer intermediate, nor the lazy splay comparison against the compiled run.
-/

namespace MultiSplay.Layered

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (size)

variable {α : Type*}

theorem primitives (capacity : Nat) :
    ForestCompiler.Primitives capacity 180002304 (State.source (capacity := capacity) (α := α)) State.actual
      (fun state => 18 * state.potential) where
  rotate state {target} {depth} rotation := by
    obtain ⟨result, work, same, path, bound⟩ := rotate_exists state rotation
    exact ⟨result, 18 * work, same, CommonForest.Trace.single (.prepare path), by omega⟩
  service state {left} {right} {key} root := by
    obtain ⟨result, cost, same, run, bound⟩ := service_trace state root
    exact ⟨result, cost, same, run, by omega⟩
  split state {left} {right} {key} root := by
    obtain ⟨a, b, cost, aEq, bEq, run, bound⟩ := split_trace state root
    exact ⟨a, b, cost, aEq, bEq, run, by omega⟩
  join left right key fits := by
    have sizeBound : left.size + right.size + 1 ≤ capacity := by simpa using fits
    obtain ⟨result, cost, same, run, bound⟩ := join_trace left right key sizeBound
    exact ⟨result, cost, same, run, by omega⟩

theorem forest_exists {capacity : Nat} (initial : List (State capacity α))
    {finalSources : List (RawTree α)} {word : List (CommonForest.Event α)} {charge : Nat}
    (program : CommonForest.Program (initial.map State.source) word finalSources charge)
    (joins : ∀ event ∈ word, CommonForest.Domains.JoinFits capacity event) :
    ∃ final : List (State capacity α), ∃ cost : Nat,
      final.map State.source = finalSources ∧
      PhysicalTrace (initial.map State.actual) word (final.map State.actual) cost ∧
      cost ≤ 24832512 * Forest.potential State.size initial + 180002304 * charge := by
  obtain ⟨final, cost, same, run, bound⟩ :=
    ForestCompiler.trace (primitives capacity) program joins initial rfl
  have initialBound := Forest.potential_le_size (fun state : State capacity α => 18 * state.potential)
    State.size 24832512 (fun state => by have h := state.potential_le_size; omega) initial
  exact ⟨final, cost, same, run, by omega⟩

theorem state_exists [Inhabited α] (capacity : Nat) (source : RawTree α) (fits : size source ≤ capacity) :
    ∃ state : State capacity α, state.source = source := by
  obtain ⟨upper, indexed, alphabet, same, upperEq⟩ := Alphabet.exists_encoding source
  have indexedFits : indexed.size ≤ capacity := by
    rw [indexed.size_eq_upper, upperEq]
    exact fits
  obtain ⟨heavy, ⟨heavyRep⟩⟩ :=
    Splay.Accounting.OfflineConnectedSupport.HeavyRepresentation.exists_representation capacity indexed indexedFits
  have heavyFits : heavy.size ≤ capacity := (Rib.same_interval_size indexed heavy) ▸ indexedFits
  obtain ⟨actual, ⟨ribRep⟩⟩ :=
    Splay.Accounting.OfflineConnectedSupport.RibRepresentation.exists_representation capacity false heavy heavyFits
  exact ⟨⟨⟨0, upper, indexed, heavy, actual, heavyRep, false, ribRep, indexedFits⟩, alphabet⟩, same⟩

theorem initial_exists [Inhabited α] (capacity : Nat) (sources : List (RawTree α))
    (fits : CommonForest.Capacity capacity sources) :
    ∃ initial : List (State capacity α), initial.map State.source = sources := by
  induction sources with
  | nil => exact ⟨[], rfl⟩
  | cons head tail ih =>
      obtain ⟨state, sourceEq⟩ := state_exists capacity head (fits head (by simp))
      obtain ⟨initial, initialEq⟩ := ih (fun tree member => fits tree (by simp [member]))
      exact ⟨state :: initial, by simp [sourceEq, initialEq]⟩

/-- The two-layer witnesses are constructed from the input program itself,
with no assumed low-cost comparator or representation oracle. -/
theorem program_exists [Inhabited α] {capacity : Nat} {sources targets : List (RawTree α)}
    {word : List (CommonForest.Event α)} {charge : Nat}
    (program : CommonForest.Program sources word targets charge)
    (fits : CommonForest.Capacity capacity sources)
    (joins : ∀ event ∈ word, CommonForest.Domains.JoinFits capacity event) :
    ∃ initial final : List (State capacity α), ∃ cost : Nat,
      initial.map State.source = sources ∧ final.map State.source = targets ∧
      PhysicalTrace (initial.map State.actual) word (final.map State.actual) cost ∧
      cost ≤ 24832512 * Forest.potential size sources + 180002304 * charge := by
  obtain ⟨initial, sourceEq⟩ := initial_exists capacity sources fits
  obtain ⟨final, cost, targetEq, run, bound⟩ := forest_exists initial (sourceEq ▸ program) joins
  have initialSize : Forest.potential State.size initial = Forest.potential size sources := by
    rw [← sourceEq]
    simp only [Forest.potential, List.map_map, Function.comp_def, State.source_size]
  exact ⟨initial, final, cost, sourceEq, targetEq, run, by simpa [initialSize] using bound⟩

end MultiSplay.Layered
