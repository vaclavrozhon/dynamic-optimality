import MultiSplay.ForestProgramCoefficientBound
import MultiSplay.CommonForestSplayBound
import Splay.Accounting.IteratedLogEGBound

/-!
# Raw common-forest comparison with arbitrary valid Splay coefficients

The same bounded normalizer, ordinal coupling, placements and initialized
history are constructed as in the existing raw comparison. The conclusion
bounds the supplied actual splay trace by the supplied comparator's budget,
with the explicit normalizer cap. No inexpensive MultiSplay comparator is
assumed or constructed here. Constants precede coefficients and capacity.
-/

namespace MultiSplay.Unlocated

theorem normalizedValueCap_le_interfaceGapCap (capacity : Nat) :
    normalizedValueCap capacity ≤
      Splay.Accounting.ConstructedPolylogNormalForm.interfaceGapCap capacity := by
  apply Splay.Analysis.contractedGap_mono
  change 2 * Layered.Bounded.height capacity + 1 ≤
    2 * (54000 * Splay.Analysis.stabilizedLog capacity ^ 3) + 1
  have bounded := PackedSplay.normalized_height capacity
  omega

theorem normalizedFactor_le_egTargetFactor (capacity : Nat) :
    normalizedValueCap capacity * (Nat.clog 2 (normalizedValueCap capacity) + 1) *
      Splay.Analysis.LayerEnvelope.E (normalizedValueCap capacity) ≤
        168 * Splay.Analysis.egTargetFactor capacity := by
  have gap := normalizedValueCap_le_interfaceGapCap capacity
  have logarithm := Nat.add_le_add_right (Nat.clog_mono_right 2 gap) 1
  have envelope := Splay.Analysis.LayerEnvelope.E_mono gap
  exact (Nat.mul_le_mul (Nat.mul_le_mul gap logarithm) envelope).trans
    (Splay.Accounting.ConstructedPolylogNormalForm.gapFactor_le_egTargetFactor capacity)

end MultiSplay.Unlocated

namespace MultiSplay.DenseForest

open DynamicOptimality (RawTree)
open Splay.Interface (ActivityCoefficients CoefficientBound)
open Splay.Accounting (articleShape)
open ChaCha.MTR.Tree (inorder size)

variable {α : Type*}

theorem forest_splay_bound_of_coefficients :
    ∃ constant : Nat, 0 < constant ∧ ∀ coefficients : ActivityCoefficients,
      CoefficientBound articleShape coefficients → ∀ (α : Type*) [Inhabited α] (capacity : Nat)
      {before after actual : List (RawTree α)} {word : List (CommonForest.Event α)} {budget : Nat},
      Trace (Layered.Bounded.height capacity) 20 before word after budget →
      (∀ tree ∈ before, BoundedMacros.Geometry (Layered.Bounded.height capacity) 20 tree) →
      actual.map inorder = before.map inorder →
      ∃ final cost, CommonForest.SplayTrace actual word final cost ∧
        final.map inorder = after.map inorder ∧
        cost ≤ constant * (2 * (actual.map size).sum + actual.length + budget) *
          Splay.Analysis.coefficientFactor coefficients (Unlocated.normalizedValueCap capacity) := by
  obtain ⟨constant, positive, bound⟩ := Unlocated.forest_splay_bound_of_coefficients
  refine ⟨2*constant, by omega, ?_⟩
  intro coefficients valid α _ capacity before after actual word budget trace geometry same
  obtain ⟨initial, sourceEq, actualEq⟩ := exists_components before actual same
  obtain ⟨last, finalEq, ⟨execution⟩⟩ := compile trace (normalized_cap capacity) initial sourceEq
  have heights : ∀ trees ∈ initial.map Component.trees,
      trees.comparison.height ≤ Layered.Bounded.height capacity := by
    intro trees member
    obtain ⟨component, present, rfl⟩ := List.mem_map.mp member
    exact (component.geometry (geometry component.source (sourceEq ▸ List.mem_map.mpr ⟨component, present, rfl⟩))).1
  have paid := execution.paid.trans (bound coefficients valid capacity execution.program heights)
  have sizes := forest_sizes initial
  rw [actualEq] at sizes
  have lengths : (initial.map Component.trees).length = actual.length := by
    rw [← actualEq]
    simp
  have comparison := execution.comparison
  have volume : 2 * ((initial.map Component.trees).map Unlocated.Trees.size).sum +
      (initial.map Component.trees).length + execution.program.comparisonCost ≤
      2 * (2 * (actual.map size).sum + actual.length + budget) := by
    rw [sizes, lengths]
    omega
  refine ⟨last.map Component.actual, execution.cost, ?_, ?_, ?_⟩
  · simpa only [actualEq] using execution.actual
  · simpa only [finalEq] using forest_domains last
  · calc
      execution.cost ≤ constant * (2 * ((initial.map Component.trees).map Unlocated.Trees.size).sum +
          (initial.map Component.trees).length + execution.program.comparisonCost) *
          Splay.Analysis.coefficientFactor coefficients (Unlocated.normalizedValueCap capacity) := paid
      _ ≤ constant * (2 * (2 * (actual.map size).sum + actual.length + budget)) *
          Splay.Analysis.coefficientFactor coefficients (Unlocated.normalizedValueCap capacity) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ volume)
      _ = _ := by ring

end MultiSplay.DenseForest

namespace MultiSplay.CommonForest

open DynamicOptimality (RawTree)
open Splay.Interface (ActivityCoefficients CoefficientBound)
open Splay.Accounting (articleShape)
open ChaCha.MTR.Tree (inorder size)

variable {α : Type*}

/-- An actual splay run of the prescribed common word, from arbitrary initial
splay shapes, with a uniform cost comparison against any raw comparator.
The result is existential in the splay run; deterministic-run transfer is a
separate statement and is not assumed in this construction. -/
theorem exists_splay_comparison_of_coefficients :
    ∃ constant : Nat, 0 < constant ∧ ∀ coefficients : ActivityCoefficients,
      CoefficientBound articleShape coefficients → ∀ (α : Type*) [Inhabited α] (capacity : Nat)
      {sources targets actual : List (RawTree α)} {word : List (Event α)} {budget : Nat},
      Program sources word targets budget → Capacity capacity sources →
      (∀ event ∈ word, Domains.JoinFits capacity event) →
      actual.map inorder = sources.map inorder →
      ∃ final cost, SplayTrace actual word final cost ∧
        final.map inorder = targets.map inorder ∧
        cost ≤ constant * ((actual.map size).sum + actual.length + budget) *
          Splay.Analysis.coefficientFactor coefficients (Unlocated.normalizedValueCap capacity) := by
  obtain ⟨constant, positive, bound⟩ := DenseForest.forest_splay_bound_of_coefficients
  refine ⟨constant*2880036864, Nat.mul_pos positive (by omega), ?_⟩
  intro coefficients valid α _ capacity sources targets actual word budget program fits joins same
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
    bound coefficients valid α capacity run geometry (same.trans initialDomains.symm)
  have sizesEq : (actual.map size).sum = Forest.potential size sources := by
    have lengths := congrArg (fun domains : List (List α) => (domains.map List.length).sum) same
    simpa only [Forest.potential, List.map_map, Function.comp_def, ChaCha.MTR.Tree.length_inorder] using lengths
  have volume : 2 * (actual.map size).sum + actual.length + work ≤
      2880036864 * ((actual.map size).sum + actual.length + budget) := by
    rw [← sizesEq] at paid
    omega
  refine ⟨final, cost, execution, domains.trans finalDomains, result.trans ?_⟩
  calc
    constant * (2 * (actual.map size).sum + actual.length + work) * Splay.Analysis.coefficientFactor coefficients (Unlocated.normalizedValueCap capacity) ≤
        constant * (2880036864 * ((actual.map size).sum + actual.length + budget)) *
          Splay.Analysis.coefficientFactor coefficients (Unlocated.normalizedValueCap capacity) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ volume)
    _ = _ := by ring

/-- The portable raw-forest splay theorem. The supplied actual run, rather than
an existentially chosen replacement, receives the cost bound. -/
theorem forest_splay_bound_of_coefficients :
    ∃ constant : Nat, 0 < constant ∧ ∀ coefficients : ActivityCoefficients,
      CoefficientBound articleShape coefficients → ∀ (α : Type*) [Inhabited α] (capacity : Nat)
      {sources targets before after : List (RawTree α)} {word : List (Event α)} {budget cost : Nat},
      Program sources word targets budget → Capacity capacity sources →
      (∀ event ∈ word, Domains.JoinFits capacity event) →
      DistinctSplayTrace before word after cost →
      before.map inorder = sources.map inorder →
      cost ≤ constant * ((before.map size).sum + before.length + budget) *
        Splay.Analysis.coefficientFactor coefficients (Unlocated.normalizedValueCap capacity) := by
  obtain ⟨constant, positive, bound⟩ := exists_splay_comparison_of_coefficients
  refine ⟨constant, positive, ?_⟩
  intro coefficients valid α _ capacity sources targets before after word budget cost comparator fits joins actual domains
  obtain ⟨final, work, constructed, _, paid⟩ := bound coefficients valid α capacity comparator fits joins domains
  have exactCost := (actual.deterministic constructed (List.Perm.refl _)).2
  exact exactCost ▸ paid

/-- The improved envelope for the supplied actual forest execution. The cap
is that of the constructed normalizer; the comparator budget remains explicit. -/
theorem forest_splay_bound_layerEnvelope :
    ∃ constant : Nat, 0 < constant ∧ ∀ (α : Type*) [Inhabited α] (capacity : Nat)
      {sources targets before after : List (RawTree α)} {word : List (Event α)} {budget cost : Nat},
      Program sources word targets budget → Capacity capacity sources →
      (∀ event ∈ word, Domains.JoinFits capacity event) →
      DistinctSplayTrace before word after cost →
      before.map inorder = sources.map inorder →
      cost ≤ constant * ((before.map size).sum + before.length + budget) *
        Unlocated.normalizedValueCap capacity *
        (Nat.clog 2 (Unlocated.normalizedValueCap capacity) + 1) *
        Splay.Analysis.LayerEnvelope.E (Unlocated.normalizedValueCap capacity) := by
  obtain ⟨constant, positive, bound⟩ := forest_splay_bound_of_coefficients
  refine ⟨16 * constant, by positivity, ?_⟩
  intro α _ capacity sources targets before after word budget cost comparator fits joins actual domains
  let coefficients := Splay.Interface.LayerCoefficients.coefficients articleShape
  have valid : CoefficientBound articleShape coefficients :=
    Splay.Interface.LayerCoefficients.valid articleShape rfl rfl rfl
  have paid := bound coefficients valid α capacity comparator fits joins actual domains
  let gap := Unlocated.normalizedValueCap capacity
  have gapPositive : 0 < gap := lt_of_lt_of_le (by decide : 0 < 2)
    (Splay.Accounting.articleParameters (Layered.Bounded.height capacity)).valueBound_ge_two
  have estimates := Splay.Analysis.LayerEnvelope.coefficients_le articleShape (by decide) gap
  have factor := Splay.Analysis.coefficientFactor_le_envelope coefficients gap
    (Splay.Analysis.LayerEnvelope.envelope (Splay.Analysis.LayerEnvelope.depth gap))
    gapPositive (Splay.Analysis.LayerEnvelope.envelope_pos _) estimates.1 estimates.2
  calc
    _ ≤ constant * ((before.map size).sum + before.length + budget) *
        Splay.Analysis.coefficientFactor coefficients gap := paid
    _ ≤ constant * ((before.map size).sum + before.length + budget) *
        (16 * gap * Splay.Analysis.LayerEnvelope.envelope (Splay.Analysis.LayerEnvelope.depth gap) ^ 2 *
          (Nat.clog 2 gap + 1)) := Nat.mul_le_mul_left _ factor
    _ = _ := by unfold Splay.Analysis.LayerEnvelope.E; dsimp [gap]; ring

/-- The same strongest exported Splay factor, evaluated at component capacity,
for the supplied raw forest execution and comparator of its exact event word.
This theorem still charges the comparator's budget explicitly. -/
theorem forest_splay_bound_eg :
    ∃ constant : Nat, 0 < constant ∧ ∀ (α : Type*) [Inhabited α] (capacity : Nat)
      {sources targets before after : List (RawTree α)} {word : List (Event α)} {budget cost : Nat},
      Program sources word targets budget → Capacity capacity sources →
      (∀ event ∈ word, Domains.JoinFits capacity event) →
      DistinctSplayTrace before word after cost →
      before.map inorder = sources.map inorder →
      cost ≤ constant * ((before.map size).sum + before.length + budget) *
        Splay.Analysis.egTargetFactor capacity := by
  obtain ⟨constant, positive, bound⟩ := forest_splay_bound_layerEnvelope
  refine ⟨168 * constant, by positivity, ?_⟩
  intro α _ capacity sources targets before after word budget cost comparator fits joins actual domains
  have paid := bound α capacity comparator fits joins actual domains
  have factor := Unlocated.normalizedFactor_le_egTargetFactor capacity
  calc
    _ ≤ constant * ((before.map size).sum + before.length + budget) *
        (Unlocated.normalizedValueCap capacity *
          (Nat.clog 2 (Unlocated.normalizedValueCap capacity) + 1) *
          Splay.Analysis.LayerEnvelope.E (Unlocated.normalizedValueCap capacity)) := by
      simpa only [Nat.mul_assoc] using paid
    _ ≤ constant * ((before.map size).sum + before.length + budget) *
        (168 * Splay.Analysis.egTargetFactor capacity) := Nat.mul_le_mul_left _ factor
    _ = _ := by ring

end MultiSplay.CommonForest
