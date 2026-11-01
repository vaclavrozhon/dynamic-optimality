import MultiSplay.ForestSplayNormalForm
import MultiSplay.InitializedForestCoefficientBound

/-!
# Arbitrary interface coefficients for constructed forest programs

The existing packing and realization construct the same persistent history,
including its once-only initialization. Only the numerical interface bound
changes. Constants are uniform in the coefficient function and value cap.
-/

noncomputable section

namespace MultiSplay.PackedSplay

open Splay.Interface (Parameters Shape ActivityCoefficients CoefficientBound)
open Splay.Rank (Snapshot)
open SharedSplay

theorem splay_bound_of_coefficients (shape : Shape) (slack depth : Nat) :
    ∃ constant : Nat, 0 < constant ∧ ∀ coefficients : ActivityCoefficients,
      CoefficientBound shape coefficients →
      ∀ params : Parameters, params.toShape = shape →
      2 ≤ params.growingLimit → params.exemptPasses = 2 →
      params.matchingNumerator = 1 → params.matchingDenominator = 8 →
      ∀ {m : Nat} {before after : List (Trees m)} (program : Program params slack depth before after),
        before.Pairwise Trees.Disjoint →
        (∀ trees ∈ before, Splay.Analysis.contractedGap
          (Snapshot.ofTree trees.comparison).withTruePriority.maxRank ≤ params.valueBound) →
        program.splayCost + program.boundaries ≤ constant * program.volume *
          Splay.Analysis.coefficientFactor coefficients params.valueBound := by
  obtain ⟨base, positive, bound⟩ := Initialized.forest_splay_bound_of_coefficients shape slack depth
  refine ⟨8*base+1, by omega, ?_⟩
  intro coefficients valid params same growing exempt numerator denominator m before after program separate cap
  obtain ⟨initial, first, setup, initialized, excess, mass, ⟨packing⟩⟩ := canonical_start before separate growing cap
  have initialShapes : (before.map Trees.canonical).map Sigma.fst = before := by
    simp [Trees.canonical, List.map_map, Function.comp_def]
  obtain ⟨result, final, _, _, history, evolution, cost, requests, rotations, maintenance⟩ :=
    program.realize (before.map Trees.canonical) first packing initialShapes
  have paid := bound coefficients valid params same exempt numerator denominator setup history
    (geometry (before.map Trees.canonical)) (geometry result) (Trees.mass before) initialized excess evolution
  have keys := canonical_keys_le_mass before
  have volume : Initialized.structuralVolume setup history (geometry (before.map Trees.canonical)) (Trees.mass before) ≤
      8 * program.volume := by
    unfold Initialized.structuralVolume Program.volume
    rw [mass, requests, rotations]
    omega
  let factor := Splay.Analysis.coefficientFactor coefficients params.valueBound
  have factorPositive : 0 < factor := Splay.Analysis.coefficientFactor_pos _ _
  have paid' : program.splayCost ≤ base * (8 * program.volume) * factor := by
    calc
      _ ≤ history.splayCost + history.maintenanceCost := by omega
      _ ≤ base * Initialized.structuralVolume setup history (geometry (before.map Trees.canonical)) (Trees.mass before) * factor := paid
      _ ≤ _ := Nat.mul_le_mul_right factor (Nat.mul_le_mul_left base volume)
  have boundary : program.boundaries ≤ program.volume * factor := by
    calc
      _ ≤ program.volume := by unfold Program.volume; omega
      _ ≤ _ := by simpa using Nat.mul_le_mul_left program.volume factorPositive
  calc
    _ ≤ base * (8 * program.volume) * factor + program.volume * factor := Nat.add_le_add paid' boundary
    _ = _ := by dsimp [factor]; ring

end MultiSplay.PackedSplay

namespace MultiSplay.Unlocated

open Splay.Interface (Parameters Shape ActivityCoefficients CoefficientBound)
open Splay.Rank (Snapshot)
open Splay.Accounting (articleParameters articleShape)

/-- Global placements and the shared initialized history are constructed,
not supplied as additional hypotheses of this program bound. -/
theorem splay_bound_of_coefficients (shape : Shape) (slack depth : Nat) :
    ∃ constant : Nat, 0 < constant ∧ ∀ coefficients : ActivityCoefficients,
      CoefficientBound shape coefficients →
      ∀ params : Parameters, params.toShape = shape →
      2 ≤ params.growingLimit → params.exemptPasses = 2 →
      params.matchingNumerator = 1 → params.matchingDenominator = 8 →
      ∀ {before after : List Trees} (program : Program params slack depth before after),
        (∀ trees ∈ before, Splay.Analysis.contractedGap
          (Snapshot.ofTree trees.comparison).withTruePriority.maxRank ≤ params.valueBound) →
        program.splayCost + program.boundaries ≤ constant * program.volume *
          Splay.Analysis.coefficientFactor coefficients params.valueBound := by
  obtain ⟨constant, positive, bound⟩ := PackedSplay.splay_bound_of_coefficients shape slack depth
  refine ⟨constant, positive, ?_⟩
  intro coefficients valid params same growing exempt numerator denominator before after program cap
  obtain ⟨m, initial, final, compiled, cost, requests, rotations, boundaries⟩ := program.exists_packed
  have cap' : ∀ trees ∈ initial.locations.map Location.packed,
      Splay.Analysis.contractedGap (Snapshot.ofTree trees.comparison).withTruePriority.maxRank ≤ params.valueBound := by
    intro trees member
    obtain ⟨location, present, rfl⟩ := List.mem_map.mp member
    exact cap location.1 (initial.shapes ▸ List.mem_map.mpr ⟨location, present, rfl⟩)
  have paid := bound coefficients valid params same growing exempt numerator denominator compiled
    (packed_separate initial.locations initial.separate) cap'
  have volume : compiled.volume = program.volume := by
    unfold PackedSplay.Program.volume Program.volume
    rw [packed_mass, initial.shapes, requests, rotations, boundaries]
  rwa [cost, boundaries, volume] at paid

theorem height_splay_bound_of_coefficients (slack depth : Nat) :
    ∃ constant : Nat, 0 < constant ∧ ∀ coefficients : ActivityCoefficients,
      CoefficientBound articleShape coefficients →
      ∀ (height : Nat) {before after : List Trees}
        (program : Program (articleParameters height) slack depth before after),
        (∀ trees ∈ before, trees.comparison.height ≤ height) →
        program.splayCost + program.boundaries ≤ constant * program.volume *
          Splay.Analysis.coefficientFactor coefficients (articleParameters height).valueBound := by
  obtain ⟨constant, positive, bound⟩ := splay_bound_of_coefficients articleShape slack depth
  refine ⟨constant, positive, ?_⟩
  intro coefficients valid height before after program bounded
  apply bound coefficients valid (articleParameters height) rfl (Nat.le_refl 2) rfl rfl rfl program
  intro trees member
  apply Splay.Analysis.contractedGap_mono
  change 2 * trees.comparison.height ≤ 2 * height + 1
  have h := bounded trees member
  omega

/-- Explicit cap used by the actual bounded forest normalizer. No
iterated-log asymptotic estimate is needed for coefficient transport. -/
def normalizedValueCap (capacity : Nat) : Nat :=
  (articleParameters (Layered.Bounded.height capacity)).valueBound

theorem forest_splay_bound_of_coefficients :
    ∃ constant : Nat, 0 < constant ∧ ∀ coefficients : ActivityCoefficients,
      CoefficientBound articleShape coefficients →
      ∀ (capacity : Nat) {before after : List Trees}
        (program : Program (articleParameters (Layered.Bounded.height capacity)) 20 1 before after),
        (∀ trees ∈ before, trees.comparison.height ≤ Layered.Bounded.height capacity) →
        program.splayCost + program.boundaries ≤
          constant * (2*(before.map Trees.size).sum + before.length + program.comparisonCost) *
            Splay.Analysis.coefficientFactor coefficients (normalizedValueCap capacity) := by
  obtain ⟨constant, positive, bound⟩ := height_splay_bound_of_coefficients 20 1
  refine ⟨constant, positive, ?_⟩
  intro coefficients valid capacity before after program bounded
  have volume : program.volume ≤ mass before + program.comparisonCost := by
    have paid := program.volume_le_comparisonCost
    unfold Program.volume
    omega
  rw [mass_eq] at volume
  exact (bound coefficients valid (Layered.Bounded.height capacity) program bounded).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left constant volume))

end MultiSplay.Unlocated
