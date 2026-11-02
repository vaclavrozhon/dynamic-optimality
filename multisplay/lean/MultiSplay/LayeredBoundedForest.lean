import MultiSplay.LayeredBoundedRotation

/-!
# Persistent forest normalization with bounded preparation paths

Every preparation segment consists of actual rotations at depth at most one,
with height at most `height capacity` and minor-rib bound twenty throughout.
The same run realizes the exact input search/split/join word and satisfies the
amortized pointer-cost bound. Arbitrary source rotation depths are allowed.

The comparison with the splay forest is a separate subsequent theorem.
-/

namespace MultiSplay.Layered.Bounded

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (size)

variable {α : Type*}

theorem primitives (capacity : Nat) :
    ForestCompiler.Interface CommonForest.RotationPreparation (Preparation capacity) capacity 2880036864 (State.source (capacity := capacity) (α := α)) State.actual
      (fun state => 18 * state.potential) (Access capacity) where
  prepare state {target} {charge} execution := by
    obtain ⟨depth, rotation, rfl⟩ := execution
    exact rotate_trace state rotation
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
      Trace capacity (initial.map State.actual) word (final.map State.actual) cost ∧
      cost ≤ 24832512 * Forest.potential State.size initial + 2880036864 * charge := by
  obtain ⟨final, cost, same, run, bound⟩ :=
    ForestCompiler.interface_trace (primitives capacity) program joins initial rfl
  have initialBound := Forest.potential_le_size (fun state : State capacity α => 18 * state.potential)
    State.size 24832512 (fun state => by have h := state.potential_le_size; omega) initial
  exact ⟨final, cost, same, run, by omega⟩

/-- The two-layer witnesses are constructed from the input program itself,
with no assumed low-cost comparator or representation oracle. -/
theorem program_exists [Inhabited α] {capacity : Nat} {sources targets : List (RawTree α)}
    {word : List (CommonForest.Event α)} {charge : Nat}
    (program : CommonForest.Program sources word targets charge)
    (fits : CommonForest.Capacity capacity sources)
    (joins : ∀ event ∈ word, CommonForest.Domains.JoinFits capacity event) :
    ∃ initial final : List (State capacity α), ∃ cost : Nat,
      initial.map State.source = sources ∧ final.map State.source = targets ∧
      Trace capacity (initial.map State.actual) word (final.map State.actual) cost ∧
      cost ≤ 24832512 * Forest.potential size sources + 2880036864 * charge := by
  obtain ⟨initial, sourceEq⟩ := initial_exists capacity sources fits
  obtain ⟨final, cost, targetEq, run, bound⟩ := forest_exists initial (sourceEq ▸ program) joins
  have initialSize : Forest.potential State.size initial = Forest.potential size sources := by
    rw [← sourceEq]
    simp only [Forest.potential, List.map_map, Function.comp_def, State.source_size]
  exact ⟨initial, final, cost, sourceEq, targetEq, run, by simpa [initialSize] using bound⟩

end MultiSplay.Layered.Bounded
