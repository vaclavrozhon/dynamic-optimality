import MultiSplay.PortableSplayBound
import MultiSplay.LayeredGeometry
import Splay.Accounting.ConcreteTargetBound
import Splay.Analysis.PolylogHeightFactor

/-! # The iterated-log factor for the portable forest splay theorem -/

namespace MultiSplay.PackedSplay

open Splay.Accounting
open Splay.Rank (Snapshot)

theorem initial_cap_of_height {m height : Nat} (forest : List (Trees m))
    (bounded : ∀ trees ∈ forest, trees.comparison.height ≤ height) :
    ∀ trees ∈ forest, Splay.Analysis.contractedGap
      (Snapshot.ofTree trees.comparison).withTruePriority.maxRank ≤ (articleParameters height).valueBound := by
  intro trees member
  apply Splay.Analysis.contractedGap_mono
  change 2 * trees.comparison.height ≤ 2 * height + 1
  have h := bounded trees member
  omega

theorem height_splay_bound (slack depth : Nat) :
    ∃ constant : Nat, 0 < constant ∧ ∀ (height : Nat) {m : Nat} {before after : List (Trees m)}
      (program : Program (articleParameters height) slack depth before after),
      before.Pairwise Trees.Disjoint → (∀ trees ∈ before, trees.comparison.height ≤ height) →
      program.splayCost + program.boundaries ≤ constant * program.volume * Splay.Analysis.heightFactor height := by
  obtain ⟨base, positive, bound⟩ := splay_bound articleShape slack depth
  refine ⟨18*base, by positivity, ?_⟩
  intro height m before after program separate bounded
  have paid := bound (articleParameters height) rfl (Nat.le_refl 2) rfl rfl rfl program separate
    (initial_cap_of_height before bounded)
  have factor := articleParameters_factor_le height
  calc
    _ ≤ base * program.volume * ((articleParameters height).valueBound *
        (Nat.clog 2 (articleParameters height).valueBound + 1)^2) := by simpa only [Nat.mul_assoc] using paid
    _ ≤ base * program.volume * (18 * Splay.Analysis.heightFactor height) := Nat.mul_le_mul_left _ factor
    _ = _ := by ring

theorem normalized_height (capacity : Nat) :
    Layered.Bounded.height capacity ≤ 54000 * (Splay.Analysis.stabilizedLog capacity)^3 := by
  let logarithm := Splay.Analysis.stabilizedLog capacity
  have positive : 0 < logarithm := Splay.Analysis.stabilizedLog_pos capacity
  have power : capacity ≤ 2^logarithm := (le_max_right 2 capacity).trans (Nat.le_pow_clog (by decide : 1 < 2) _)
  have doubled : capacity+1 ≤ 2^(logarithm+1) := by
    rw [pow_succ]
    have one : 1 ≤ 2^logarithm := Nat.one_le_pow _ _ (by decide)
    omega
  have upper := Nat.clog_le_of_le_pow doubled
  have cube := Nat.pow_le_pow_left (show Nat.clog 2 (capacity+1)+1 ≤ 3*logarithm by omega) 3
  have height := Layered.Bounded.height_le_logCubed capacity
  nlinarith

/-- The same stabilized `log log K * (log log log K)^2` factor applies to
components of capacity K after the existing bounded forest normalizer. The
normalizer's physical rotations are counted in `program.volume`. -/
theorem normalized_splay_bound (slack depth : Nat) :
    ∃ constant : Nat, 0 < constant ∧ ∀ (capacity : Nat) {m : Nat} {before after : List (Trees m)}
      (program : Program (articleParameters (Layered.Bounded.height capacity)) slack depth before after),
      before.Pairwise Trees.Disjoint →
      (∀ trees ∈ before, trees.comparison.height ≤ Layered.Bounded.height capacity) →
      program.splayCost + program.boundaries ≤ constant * program.volume * Splay.Analysis.targetFactor capacity := by
  obtain ⟨base, positive, bound⟩ := height_splay_bound slack depth
  let scale := Splay.Analysis.polylogHeightFactorConstant 54000 3
  refine ⟨base * (scale+1), by positivity, ?_⟩
  intro capacity m before after program separate bounded
  have paid := bound (Layered.Bounded.height capacity) program separate bounded
  have factor := Splay.Analysis.heightFactor_le_targetFactor_of_polylog 54000 3 capacity
    (Layered.Bounded.height capacity) (normalized_height capacity)
  calc
    _ ≤ base * program.volume * Splay.Analysis.heightFactor (Layered.Bounded.height capacity) := paid
    _ ≤ base * program.volume * (scale * Splay.Analysis.targetFactor capacity) := Nat.mul_le_mul_left _ factor
    _ ≤ base * program.volume * ((scale+1) * Splay.Analysis.targetFactor capacity) := by gcongr; omega
    _ = _ := by ring

end MultiSplay.PackedSplay
