import Splay.Accounting.BoundaryCreditAbsorption
import Mathlib.Tactic

namespace Splay.Accounting

/-- Boundary absorption for an arbitrary positive activity rate. This is the
only logarithmic loss introduced after an interface coefficient bound. -/
theorem boundary_credit_rate_bound (coefficient blockCoefficient : ℕ)
    (coefficientPositive : 0 < coefficient) :
    ∃ constant : ℕ, 0 < constant ∧ ∀ rate volume activity boundary : ℕ, 0 < rate →
      activity ≤ coefficient * rate * (volume + boundary) →
      (∀ cutoff : ℕ, cutoff * (2 * boundary) ≤
        4 * cutoff * Interface.boundaryCreditCapacity cutoff * blockCoefficient * volume +
          16 * activity) →
      activity + boundary ≤ constant * volume * rate * (Nat.clog 2 rate + 1) := by
  let capacityCoefficient := 16 * Nat.clog 2 (16 * coefficient) + 30
  let constant := 18 * coefficient + 36 * coefficient * blockCoefficient * capacityCoefficient +
    2 * blockCoefficient * capacityCoefficient
  refine ⟨constant, by dsimp [constant]; positivity, ?_⟩
  intro rate volume activity boundary ratePositive activityBound boundaryBound
  let logarithm := Nat.clog 2 rate + 1
  let cutoff := 16 * coefficient * rate
  let reserve := Interface.boundaryCreditCapacity cutoff * blockCoefficient * volume
  have cutoffPositive : 0 < cutoff := by dsimp [cutoff]; positivity
  have cutoffLarge : 16 * (coefficient * rate) ≤ cutoff := by
    dsimp [cutoff]
    rw [Nat.mul_assoc]
  have cutoffPow : cutoff ≤ 2 ^ (Nat.clog 2 (16 * coefficient) + Nat.clog 2 rate) := by
    rw [pow_add]
    exact Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _)
  have cutoffLog := Nat.clog_le_of_le_pow cutoffPow
  have capacity := Interface.boundaryCreditCapacity_bound cutoff
  have capacityBound : Interface.boundaryCreditCapacity cutoff ≤ capacityCoefficient * logarithm := by
    dsimp [capacityCoefficient, logarithm]
    nlinarith
  have boundaryAtCutoff : cutoff * (2 * boundary) ≤ 4 * cutoff * reserve + 16 * activity := by
    simpa only [reserve, Nat.mul_assoc] using boundaryBound cutoff
  obtain ⟨activityPaid, boundaryPaid⟩ :=
    boundary_credit_absorb cutoffPositive cutoffLarge activityBound boundaryAtCutoff
  have reserveBound : reserve ≤ capacityCoefficient * logarithm * blockCoefficient * volume :=
    Nat.mul_le_mul_right volume (Nat.mul_le_mul_right blockCoefficient capacityBound)
  have firstTerm := Nat.mul_le_mul_left (18 * coefficient * rate * volume)
    (show 1 ≤ logarithm by dsimp [logarithm]; omega)
  have lastTerm := Nat.mul_le_mul_left (2 * blockCoefficient * capacityCoefficient * logarithm * volume)
    ratePositive
  calc
    activity + boundary ≤ 9 * activity + 2 * reserve := by omega
    _ ≤ 18 * coefficient * rate * (volume + 2 * reserve) + 2 * reserve := by nlinarith
    _ ≤ 18 * coefficient * rate *
          (volume + 2 * (capacityCoefficient * logarithm * blockCoefficient * volume)) +
        2 * (capacityCoefficient * logarithm * blockCoefficient * volume) := by gcongr
    _ ≤ constant * volume * rate * (Nat.clog 2 rate + 1) := by
      change _ ≤ constant * volume * rate * logarithm
      dsimp only [constant]
      nlinarith

end Splay.Accounting
