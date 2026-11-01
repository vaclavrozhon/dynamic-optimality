import MultiSplay.SharedSplayHistory
import Splay.Accounting.BoundaryCreditUniformBound

/-!
# A uniform pairing bound for one changing-forest history

`volume seed` counts the one-time initial excess allowance, comparison
rotations, the article's proved block-birth budgets, and twice the literal
maintenance cost. In particular, reserving inactive universe elements adds no
cost. The constant is chosen before the value cap or the component sizes.

This uses the original interface activity theorem. No E(G) improvement is
assumed, and no Tango2 upper-bound theorem is imported.
-/

namespace MultiSplay.SharedSplay

open Splay.Interface

namespace History

variable {m : Nat} {params : Parameters} {first last : State m}

noncomputable def volume (history : History params first last) (seed : Nat) : Nat :=
  seed + history.rotations + history.births + 2 * history.maintenanceCost

theorem value_charge (history : History params first last) (valid : first.Valid params) :
    2 * totalIncreases history.operations + InterfaceForest.excess first ≤
      3 * InterfaceForest.excess first + 32 * params.valueBound * history.boundary +
        12 * params.valueBound * history.rotations + 4 * history.maintenanceCost := by
  have good := history.good_charge valid
  have increases := history.increases
  nlinarith

theorem boundary_estimate (history : History params first last) (initialized : first.Initial params)
    (seed cutoff : Nat) (exempt : params.exemptPasses = 2)
    (numerator : params.matchingNumerator = 1) (denominator : params.matchingDenominator = 8) :
    cutoff * (2 * history.boundary) ≤
      4 * cutoff * boundaryCreditCapacity cutoff * history.volume seed + 16 * totalActivity history.operations := by
  have paid := history.boundary_credit cutoff exempt numerator denominator
  have noCredit : boundaryCredit cutoff first = 0 := by simp [boundaryCredit, initialized.2]
  rw [noCredit] at paid
  have reserve : history.births + 2 * history.maintenanceCost ≤ history.volume seed := by unfold volume; omega
  have weighted := Nat.mul_le_mul_left (4 * cutoff * boundaryCreditCapacity cutoff) reserve
  nlinarith

end History

/-- The main portable pairing estimate. Its inputs are an actual chronological
history and a bound on the initial excess; local accounting estimates are
proved from the macro realizations, rather than supplied as hypotheses. -/
theorem activity_add_boundary (shape : Shape) :
    ∃ constant : Nat, 0 < constant ∧
      ∀ (params : Parameters), params.toShape = shape →
      params.exemptPasses = 2 → params.matchingNumerator = 1 → params.matchingDenominator = 8 →
      ∀ {m : Nat} {first last : State m} (history : History params first last) (seed : Nat),
        first.Initial params → InterfaceForest.excess first ≤ params.valueBound * seed →
        totalActivity history.operations + history.boundary ≤
          constant * history.volume seed * params.valueBound * (Nat.clog 2 params.valueBound + 1)^2 := by
  obtain ⟨a, b, aPositive, bPositive, blackbox⟩ := InterfaceForest.activity_le_excess shape
  let coefficient := 64 * (a+b+1)
  have positive : 0 < coefficient := by dsimp [coefficient]; omega
  obtain ⟨constant, constantPositive, absorb⟩ := Splay.Accounting.boundary_credit_uniform_bound coefficient 1 positive
  refine ⟨constant, constantPositive, ?_⟩
  intro params same exempt numerator denominator m first last history seed initialized excessBound
  let gap := params.valueBound
  let volume := history.volume seed
  have gapPositive : 0 < gap := lt_of_lt_of_le (by decide : 0 < 2) params.valueBound_ge_two
  apply absorb gap volume (totalActivity history.operations) history.boundary gapPositive
  · have raw := blackbox params same initialized (history.trace initialized.1)
    have inserts := history.inserts
    have values := history.value_charge initialized.1
    have volumeBound : seed + history.rotations + history.maintenanceCost ≤ volume := by
      dsimp [volume, History.volume]
      omega
    have insertsBound : totalInserts history.operations ≤ 2 * (volume + history.boundary) := by omega
    have valuesBound : 2 * totalIncreases history.operations + InterfaceForest.excess first ≤
        32 * gap * (volume + history.boundary) := by
      have scaledVolume := Nat.mul_le_mul_left (32 * gap) volumeBound
      have maintenanceScaled := Nat.mul_le_mul_left (4 * history.maintenanceCost) gapPositive
      change InterfaceForest.excess first ≤ gap * seed at excessBound
      change 2 * totalIncreases history.operations + InterfaceForest.excess first ≤
        3 * InterfaceForest.excess first + 32 * gap * history.boundary +
          12 * gap * history.rotations + 4 * history.maintenanceCost at values
      nlinarith
    have enlarged : totalActivity history.operations ≤ a * gap * (2 * (volume + history.boundary)) +
        b * Nat.clog 2 gap * (32 * gap * (volume + history.boundary)) :=
      raw.trans (Nat.add_le_add (Nat.mul_le_mul_left _ insertsBound) (Nat.mul_le_mul_left _ valuesBound))
    have firstTerm : a * gap * (2 * (volume + history.boundary)) ≤
        2 * a * gap * (Nat.clog 2 gap + 1) * (volume + history.boundary) := by
      calc
        _ = 2 * a * gap * 1 * (volume + history.boundary) := by ring
        _ ≤ _ := by gcongr; omega
    have secondTerm : b * Nat.clog 2 gap * (32 * gap * (volume + history.boundary)) ≤
        32 * b * gap * (Nat.clog 2 gap + 1) * (volume + history.boundary) := by
      calc
        _ = 32 * b * gap * Nat.clog 2 gap * (volume + history.boundary) := by ring
        _ ≤ _ := by gcongr; omega
    have coefficientBound : 2*a + 32*b ≤ coefficient := by dsimp [coefficient]; omega
    have weighted := Nat.mul_le_mul_right (gap * (Nat.clog 2 gap + 1) * (volume + history.boundary)) coefficientBound
    nlinarith
  · intro cutoff
    simpa only [Nat.mul_one] using history.boundary_estimate initialized seed cutoff exempt numerator denominator

end MultiSplay.SharedSplay
