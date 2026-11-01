import MultiSplay.PackedProgramRealization
import MultiSplay.PackedStart
import MultiSplay.InitializedForestSplayBound

/-!
# Portable splay comparison for a changing forest

The input is a physical `Program`: actual complete splays, comparison rotations,
and common-root splits and joins. The shared lazy history and its one-time
initialization are constructed in the proof. The constant is uniform in the
value cap, the reserved universe, all component sizes, and the entire program.
-/

noncomputable section

namespace MultiSplay.PackedSplay

open Splay.Interface (Parameters Shape)
open Splay.Rank (Snapshot)
open SharedSplay

variable {m : Nat}

theorem canonical_keys_le_mass (forest : List (Trees m)) :
    (geometry (forest.map Trees.canonical)).keys ≤ Trees.mass forest := by
  induction forest with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
      simp only [geometry, Forest.keys, components, Trees.mass, Trees.canonical,
        List.map_cons, List.sum_cons] at ih ⊢
      omega

def Program.volume {params : Parameters} {slack depth : Nat} {before after : List (Trees m)}
    (program : Program params slack depth before after) : Nat :=
  Trees.mass before + program.requests + program.rotations + program.boundaries

/-- No cost inequality, interface run, rich-state history, or per-request
endpoint certificate is assumed. Only physical moves and their geometry enter. -/
theorem splay_bound (shape : Shape) (slack depth : Nat) :
    ∃ constant : Nat, 0 < constant ∧ ∀ params : Parameters, params.toShape = shape →
      2 ≤ params.growingLimit → params.exemptPasses = 2 →
      params.matchingNumerator = 1 → params.matchingDenominator = 8 →
      ∀ {m : Nat} {before after : List (Trees m)} (program : Program params slack depth before after),
        before.Pairwise Trees.Disjoint →
        (∀ trees ∈ before, Splay.Analysis.contractedGap
          (Snapshot.ofTree trees.comparison).withTruePriority.maxRank ≤ params.valueBound) →
        program.splayCost + program.boundaries ≤ constant * program.volume *
          params.valueBound * (Nat.clog 2 params.valueBound + 1)^2 := by
  obtain ⟨base, positive, bound⟩ := Initialized.forest_splay_bound shape slack depth
  refine ⟨8*base+1, by omega, ?_⟩
  intro params same growing exempt numerator denominator m before after program separate cap
  obtain ⟨initial, first, setup, initialized, excess, mass, ⟨packing⟩⟩ := canonical_start before separate growing cap
  have initialShapes : (before.map Trees.canonical).map Sigma.fst = before := by
    simp [Trees.canonical, List.map_map, Function.comp_def]
  obtain ⟨result, final, _, _, history, evolution, cost, requests, rotations, maintenance⟩ :=
    program.realize (before.map Trees.canonical) first packing initialShapes
  have paid := bound params same exempt numerator denominator setup history
    (geometry (before.map Trees.canonical)) (geometry result) (Trees.mass before) initialized excess evolution
  have keys := canonical_keys_le_mass before
  have volume : Initialized.structuralVolume setup history (geometry (before.map Trees.canonical)) (Trees.mass before) ≤
      8 * program.volume := by
    unfold Initialized.structuralVolume Program.volume
    rw [mass, requests, rotations]
    omega
  let factor := params.valueBound * (Nat.clog 2 params.valueBound + 1)^2
  have factorPositive : 0 < factor := by
    have gapPositive : 0 < params.valueBound := lt_of_lt_of_le (by decide : 0 < 2) params.valueBound_ge_two
    dsimp [factor]
    positivity
  have paid' : program.splayCost ≤ base * (8 * program.volume) * factor := by
    calc
      _ ≤ history.splayCost + history.maintenanceCost := by omega
      _ ≤ base * Initialized.structuralVolume setup history (geometry (before.map Trees.canonical)) (Trees.mass before) * factor := by
        simpa only [factor, Nat.mul_assoc] using paid
      _ ≤ _ := Nat.mul_le_mul_right factor (Nat.mul_le_mul_left base volume)
  have boundary : program.boundaries ≤ program.volume * factor := by
    calc
      _ ≤ program.volume := by unfold Program.volume; omega
      _ ≤ _ := by simpa using Nat.mul_le_mul_left program.volume factorPositive
  calc
    _ ≤ base * (8 * program.volume) * factor + program.volume * factor := Nat.add_le_add paid' boundary
    _ = _ := by dsimp [factor]; ring

end MultiSplay.PackedSplay
