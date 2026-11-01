import Splay.Accounting.BoundaryCreditAbsorption
import Mathlib.Tactic

namespace Splay.Accounting

/-- One fixed coefficient controls both kinds of pairing after the cutoff
is chosen. All constants precede the arbitrary gap bound and run size. -/
theorem boundary_credit_uniform_bound (coefficient blockCoefficient : ℕ)
    (coefficientPositive : 0 < coefficient) :
    ∃ constant : ℕ, 0 < constant ∧ ∀ gap volume activity boundary : ℕ, 0 < gap →
      activity ≤ coefficient * (gap * (Nat.clog 2 gap + 1)) * (volume + boundary) →
      (∀ cutoff : ℕ, cutoff * (2 * boundary) ≤
        4 * cutoff * Interface.boundaryCreditCapacity cutoff * blockCoefficient * volume + 16 * activity) →
      activity + boundary ≤ constant * volume * gap * (Nat.clog 2 gap + 1) ^ 2 := by
  let capacityCoefficient := 16 * Nat.clog 2 (32 * coefficient) + 46
  let constant := 18 * coefficient + 36 * coefficient * blockCoefficient * capacityCoefficient +
    2 * blockCoefficient * capacityCoefficient
  refine ⟨constant, by dsimp [constant]; positivity, ?_⟩
  intro gap volume activity boundary gapPositive activityBound boundaryBound
  let logarithm := Nat.clog 2 gap + 1
  let rate := coefficient * (gap * logarithm)
  let cutoff := 32 * coefficient * gap ^ 2
  let reserve := Interface.boundaryCreditCapacity cutoff * blockCoefficient * volume
  obtain ⟨cutoffPositive, cutoffLarge, capacityBound⟩ := polynomial_boundary_cutoff coefficientPositive gapPositive
  have boundaryAtCutoff : cutoff * (2 * boundary) ≤ 4 * cutoff * reserve + 16 * activity := by
    simpa only [reserve, Nat.mul_assoc] using boundaryBound cutoff
  obtain ⟨activityPaid, boundaryPaid⟩ := boundary_credit_absorb cutoffPositive cutoffLarge activityBound boundaryAtCutoff
  have reserveBound : reserve ≤ capacityCoefficient * logarithm * blockCoefficient * volume :=
    Nat.mul_le_mul_right volume (Nat.mul_le_mul_right blockCoefficient capacityBound)
  have firstTerm := Nat.mul_le_mul_left (18 * coefficient * gap * volume)
    (show logarithm ≤ logarithm ^ 2 by dsimp [logarithm]; nlinarith)
  have lastTerm := Nat.mul_le_mul_left (2 * blockCoefficient * capacityCoefficient * volume)
    (show logarithm ≤ gap * logarithm ^ 2 by
      have logPositive : 0 < logarithm := by dsimp [logarithm]; omega
      nlinarith [Nat.mul_le_mul_right (logarithm ^ 2) gapPositive])
  calc
    activity + boundary ≤ 9 * activity + 2 * reserve := by omega
    _ ≤ 18 * rate * (volume + 2 * reserve) + 2 * reserve := by
      change activity ≤ 2 * rate * (volume + 2 * reserve) at activityPaid
      nlinarith
    _ ≤ 18 * rate * (volume + 2 * (capacityCoefficient * logarithm * blockCoefficient * volume)) +
        2 * (capacityCoefficient * logarithm * blockCoefficient * volume) := by gcongr
    _ ≤ constant * volume * gap * (Nat.clog 2 gap + 1) ^ 2 := by
      dsimp only [constant, rate]
      change _ ≤ (18 * coefficient + 36 * coefficient * blockCoefficient * capacityCoefficient +
        2 * blockCoefficient * capacityCoefficient) * volume * gap * logarithm ^ 2
      nlinarith

end Splay.Accounting
