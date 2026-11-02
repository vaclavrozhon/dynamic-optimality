import MultiSplay.DenseForestBound
import MultiSplay.LayeredBoundedForest

/-!
# Portable splay comparison for raw common-forest programs

The comparison program may rotate at arbitrary depths and may use arbitrary
initial shapes. The proof constructs its bounded heavy/rib normalization and
then the coupled splay execution. `capacity` bounds component key counts; the
factor `targetFactor capacity` is the stabilized iterated-log factor of the
original interface bound. No Cha-Cha competitive upper bound is used.
-/

namespace MultiSplay.Layered

theorem State.bounded_geometry {α : Type*} {capacity : Nat} (state : State capacity α) :
    BoundedMacros.Geometry (Bounded.height capacity) 20 state.actual := by
  refine ⟨_, _, state.component.actual, state.alphabet, rfl, ?_, ?_⟩
  · have ribs := state.component.ribRep.height_le state.component.heavyFits
    have heavy := state.component.heavyRep.height_le_capacity state.component.fits
    have comparison : state.component.heavy.height ≤
        Splay.Accounting.OfflineConnectedSupport.heavyHeight capacity := by
      dsimp [Splay.Accounting.OfflineConnectedSupport.heavyHeight]
      omega
    have multiplied := Nat.mul_le_mul_right (5 * Nat.clog 2 (capacity+1)) comparison
    dsimp [Bounded.height, Rib.simulationHeight]
    omega
  · exact BoundedMacros.ribs_mono _ state.component.ribRep.geometry.1 (by omega)

end MultiSplay.Layered

namespace MultiSplay.CommonForest

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder size)

variable {α : Type*}

/-- An actual splay run of the prescribed common word, from arbitrary initial
splay shapes, with a uniform cost comparison against any raw comparator.
The result is existential in the splay run; deterministic-run transfer is a
separate statement and is not assumed in this construction. -/
theorem exists_splay_comparison :
    ∃ constant : Nat, 0 < constant ∧ ∀ (α : Type*) [Inhabited α] (capacity : Nat)
      {sources targets actual : List (RawTree α)} {word : List (Event α)} {budget : Nat},
      Program sources word targets budget → Capacity capacity sources →
      (∀ event ∈ word, Domains.JoinFits capacity event) →
      actual.map inorder = sources.map inorder →
      ∃ final cost, SplayTrace actual word final cost ∧
        final.map inorder = targets.map inorder ∧
        cost ≤ constant * ((actual.map size).sum + actual.length + budget) *
          Splay.Analysis.targetFactor capacity := by
  obtain ⟨constant, positive, bound⟩ := DenseForest.forest_splay_bound
  refine ⟨constant*2880036864, Nat.mul_pos positive (by omega), ?_⟩
  intro α _ capacity sources targets actual word budget program fits joins same
  obtain ⟨initial, last, work, sourceEq, targetEq, run, paid⟩ :=
    Layered.Bounded.program_exists program fits joins
  have initialDomains : (initial.map Layered.State.actual).map inorder = sources.map inorder := by
    rw [← sourceEq]
    simp only [List.map_map, Function.comp_def, Layered.State.inorder_eq]
  have finalDomains : (last.map Layered.State.actual).map inorder = targets.map inorder := by
    rw [← targetEq]
    simp only [List.map_map, Function.comp_def, Layered.State.inorder_eq]
  have geometry : ∀ tree ∈ initial.map Layered.State.actual,
      BoundedMacros.Geometry (Layered.Bounded.height capacity) 20 tree := by
    intro tree member
    obtain ⟨state, _, rfl⟩ := List.mem_map.mp member
    exact state.bounded_geometry
  obtain ⟨final, cost, execution, domains, result⟩ :=
    bound α capacity run geometry (same.trans initialDomains.symm)
  have sizesEq : (actual.map size).sum = Forest.potential size sources := by
    have lengths := congrArg (fun domains : List (List α) => (domains.map List.length).sum) same
    simpa only [Forest.potential, List.map_map, Function.comp_def, ChaCha.MTR.Tree.length_inorder] using lengths
  have volume : 2 * (actual.map size).sum + actual.length + work ≤
      2880036864 * ((actual.map size).sum + actual.length + budget) := by
    rw [← sizesEq] at paid
    omega
  refine ⟨final, cost, execution, domains.trans finalDomains, result.trans ?_⟩
  calc
    constant * (2 * (actual.map size).sum + actual.length + work) * Splay.Analysis.targetFactor capacity ≤
        constant * (2880036864 * ((actual.map size).sum + actual.length + budget)) *
          Splay.Analysis.targetFactor capacity := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ volume)
    _ = _ := by ring

end MultiSplay.CommonForest
