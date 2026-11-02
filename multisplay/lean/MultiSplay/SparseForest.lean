import MultiSplay.SparseServices
import MultiSplay.ForestCompiler

/-!
# Persistent normalization of complete sparse forest programs

The generic compiler is instantiated with the proved heavy and rib primitives.
These are unconditional existence results for complete chronological pointer
runs on the same common event word. They retain all component histories and
charge only the initial forest size. Intermediate height and rib bounds, and the
lazy splay comparison against these runs, are separate obligations.
-/

namespace MultiSplay.SparseHeavy

open DynamicOptimality (RawTree)
open ChaCha.Paper20261030.Auxiliary (Rearranges)
open CommonForest (RootAccess)

variable {α : Type*}

theorem primitives (capacity : Nat) :
    ForestCompiler.Primitives capacity 8352 (State.source (capacity := capacity) (α := α)) State.actual
      (fun state => 18 * state.potential) where
  rotate state {target} {depth} rotation := by
    obtain ⟨result, work, same, path, bound, sizeEq⟩ := rotate_exists state rotation
    refine ⟨result, 18 * work, same, CommonForest.Trace.single (.prepare path), ?_⟩
    omega
  service state {left} {right} {key} root := by
    obtain ⟨result, cost, same, run, bound⟩ := service_trace state root
    exact ⟨result, cost, same, run, by omega⟩
  split state {left} {right} {key} root := by
    obtain ⟨a, b, cost, aEq, bEq, run, bound⟩ := split_trace state root
    exact ⟨a, b, cost, aEq, bEq, run, by omega⟩
  join left right key fits := by
    have sizeBound : left.size + right.size + 1 ≤ capacity := by simpa using fits
    obtain ⟨result, cost, same, run, bound, sizeEq⟩ := join_trace left right key sizeBound
    refine ⟨result, cost, same, ?_, by omega⟩
    have physical := run.mapRelations (access' := RootAccess) (fun h => False.elim h) (fun h => h)
    simpa only [left.inorder_eq, right.inorder_eq] using physical

/-- Every input primitive is realized in order. The initial potential is paid
once, regardless of the number of later component births or joins. -/
theorem forest_exists {capacity : Nat} (initial : List (State capacity α))
    {finalSources : List (RawTree α)} {word : List (CommonForest.Event α)} {charge : Nat}
    (program : CommonForest.Program (initial.map State.source) word finalSources charge)
    (joins : ∀ event ∈ word, CommonForest.Domains.JoinFits capacity event) :
    ∃ final : List (State capacity α), ∃ cost : Nat,
      final.map State.source = finalSources ∧
      PhysicalTrace (initial.map State.actual) word (final.map State.actual) cost ∧
      cost ≤ 1152 * Forest.potential State.size initial + 8352 * charge := by
  obtain ⟨final, cost, same, run, bound⟩ :=
    ForestCompiler.trace (primitives capacity) program joins initial rfl
  have initialBound := Forest.potential_le_size (fun state : State capacity α => 18 * state.potential)
    State.size 1152 (fun state => by have h := state.potential_le_size; omega) initial
  exact ⟨final, cost, same, run, by omega⟩

end MultiSplay.SparseHeavy

namespace MultiSplay.SparseRib

open DynamicOptimality (RawTree)
open ChaCha.Paper20261030.Auxiliary (Rearranges)
open CommonForest (RootAccess)

variable {α : Type*}

theorem primitives (capacity : Nat) :
    ForestCompiler.Primitives capacity 48492 (State.source (capacity := capacity) (α := α)) State.actual
      (fun state => 18 * state.potential) where
  rotate state {target} {depth} rotation := by
    obtain ⟨result, work, same, path, bound, sizeEq⟩ := rotate_exists state rotation
    refine ⟨result, 18 * work, same, CommonForest.Trace.single (.prepare path), ?_⟩
    omega
  service state {left} {right} {key} root := by
    obtain ⟨result, cost, same, run, bound⟩ := service_trace state root
    exact ⟨result, cost, same, run, by omega⟩
  split state {left} {right} {key} root := by
    obtain ⟨a, b, cost, aEq, bEq, run, bound⟩ := split_trace state root
    exact ⟨a, b, cost, aEq, bEq, run, by omega⟩
  join left right key fits := by
    have sizeBound : left.size + right.size + 1 ≤ capacity := by simpa using fits
    obtain ⟨result, cost, same, run, bound, sizeEq⟩ := join_trace left right key sizeBound
    refine ⟨result, cost, same, ?_, by omega⟩
    have physical := run.mapRelations (access' := RootAccess) (fun h => False.elim h) (fun h => h)
    simpa only [left.inorder_eq, right.inorder_eq] using physical

/-- Every input primitive is realized in order. The initial potential is paid
once, regardless of the number of later component births or joins. -/
theorem forest_exists {capacity : Nat} (initial : List (State capacity α))
    {finalSources : List (RawTree α)} {word : List (CommonForest.Event α)} {charge : Nat}
    (program : CommonForest.Program (initial.map State.source) word finalSources charge)
    (joins : ∀ event ∈ word, CommonForest.Domains.JoinFits capacity event) :
    ∃ final : List (State capacity α), ∃ cost : Nat,
      final.map State.source = finalSources ∧
      PhysicalTrace (initial.map State.actual) word (final.map State.actual) cost ∧
      cost ≤ 4608 * Forest.potential State.size initial + 48492 * charge := by
  obtain ⟨final, cost, same, run, bound⟩ :=
    ForestCompiler.trace (primitives capacity) program joins initial rfl
  have initialBound := Forest.potential_le_size (fun state : State capacity α => 18 * state.potential)
    State.size 4608 (fun state => by have h := state.potential_le_size; omega) initial
  exact ⟨final, cost, same, run, by omega⟩

end MultiSplay.SparseRib
