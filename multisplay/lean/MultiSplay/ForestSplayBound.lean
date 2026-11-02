import MultiSplay.ForestSplayGeometry

/-!
# Portable splay comparison for a changing forest

The structural volume is the initial key count, the initial excess allowance,
the number of requests and comparison rotations, and actual maintenance work.
The theorem charges this volume once, multiplied by the original splay factor.
Every local geometric and amortized bound comes from the actual executions.
-/

noncomputable section

namespace MultiSplay.SharedSplay

open Splay.Interface
open Splay.Accounting

namespace History

variable {m : Nat} {params : Parameters} {first last : State m}

def structuralVolume (history : History params first last) (forest : Forest) (seed : Nat) : Nat :=
  seed + forest.keys + history.requests + history.rotations + history.maintenanceCost

end History

def normalCoefficient (slack depth : Nat) : Nat :=
  2 + articleRequestBirthBudget slack + articleFullComparisonBirthBudget depth

theorem Evolution.volume_bound {m slack depth seed : Nat} {params : Parameters} {first last : State m}
    {history : History params first last} {before after : Forest}
    (evolution : Evolution slack depth history before after) :
    history.volume seed ≤ normalCoefficient slack depth * history.structuralVolume before seed := by
  have born := evolution.births
  dsimp [History.volume, History.structuralVolume, normalCoefficient]
  nlinarith

/-- The splay-side comparison theorem, independent of any ChaCha upper bound.
`Evolution` contains only actual component geometry and local normal-form
bounds; it contains no cost estimates or competitive-ratio premise. -/
theorem forest_splay_bound (shape : Shape) (slack depth : Nat) :
    ∃ constant : Nat, 0 < constant ∧
      ∀ (params : Parameters), params.toShape = shape →
      params.exemptPasses = 2 → params.matchingNumerator = 1 → params.matchingDenominator = 8 →
      ∀ {m : Nat} {first last : State m} (history : History params first last) (before after : Forest) (seed : Nat),
        first.Initial params → InterfaceForest.excess first ≤ params.valueBound * seed →
        Evolution slack depth history before after →
        history.splayCost + history.maintenanceCost ≤ constant * history.structuralVolume before seed *
          params.valueBound * (Nat.clog 2 params.valueBound + 1)^2 := by
  obtain ⟨pairConstant, pairPositive, pairingBound⟩ := activity_add_boundary shape
  let linear := 20 + 12 * (slack+1)
  let constant := 4 * pairConstant * normalCoefficient slack depth + linear
  refine ⟨constant, by dsimp [constant, linear]; omega, ?_⟩
  intro params same exempt numerator denominator m first last history before after seed initialized excessBound evolution
  let gap := params.valueBound
  let factor := gap * (Nat.clog 2 gap + 1)^2
  let volume := history.structuralVolume before seed
  have factorPositive : 0 < factor := by
    have gapPositive : 0 < gap := lt_of_lt_of_le (by decide : 0 < 2) params.valueBound_ge_two
    dsimp [factor]
    positivity
  have pairings := pairingBound params same exempt numerator denominator history seed initialized excessBound
  have volumeBound := evolution.volume_bound (seed := seed)
  have boundedPairings : totalActivity history.operations + history.boundary ≤
      pairConstant * normalCoefficient slack depth * volume * factor := by
    calc
      _ ≤ pairConstant * history.volume seed * gap * (Nat.clog 2 gap + 1)^2 := pairings
      _ ≤ pairConstant * (normalCoefficient slack depth * volume) * gap * (Nat.clog 2 gap + 1)^2 := by gcongr
      _ = _ := by dsimp [factor]; ring
  have paid := evolution.cost_le_pairings
  have linearBound : 2 * before.keys + (6+12*(slack+1)) * history.requests +
      8 * history.rotations + 3 * history.maintenanceCost ≤ linear * volume := by
    dsimp [linear, volume, History.structuralVolume]
    nlinarith
  have linearScaled : linear * volume ≤ linear * volume * factor := by
    simpa using Nat.mul_le_mul_left (linear * volume) factorPositive
  change history.splayCost + history.maintenanceCost ≤ constant * volume * gap * (Nat.clog 2 gap + 1)^2
  calc
    _ ≤ 4 * (totalActivity history.operations + history.boundary) + linear * volume := by omega
    _ ≤ 4 * (pairConstant * normalCoefficient slack depth * volume * factor) + linear * volume * factor :=
      Nat.add_le_add (Nat.mul_le_mul_left 4 boundedPairings) linearScaled
    _ = _ := by dsimp [constant, factor]; ring

end MultiSplay.SharedSplay
