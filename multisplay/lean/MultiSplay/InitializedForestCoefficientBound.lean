import MultiSplay.InitializedForestSplayBound
import Splay.Analysis.CoefficientEnvelope
import Splay.Analysis.LayerEnvelope
import Splay.Accounting.BoundaryCreditRateBound

/-!
# Strong interface coefficients for a persistent Splay forest

This transports arbitrary valid interface coefficients through the existing
initialized forest execution. It retains the actual setup, history, and
boundary credits. In particular the improved Splay coefficients need not be
replaced by the older `G * (log G + 1)^2` estimate when components split or
join. The theorem still charges the supplied comparison execution: it does
not construct a cheaper comparator for classical MultiSplay.
-/

noncomputable section

namespace MultiSplay.SharedSplay.Initialized

open Splay.Interface

/-- The constant is uniform in the chosen coefficient function and cap. -/
theorem activity_add_boundary_of_coefficients (shape : Shape) :
    ∃ constant : Nat, 0 < constant ∧ ∀ coefficients : ActivityCoefficients,
      CoefficientBound shape coefficients →
      ∀ (params : Parameters), params.toShape = shape →
      params.exemptPasses = 2 → params.matchingNumerator = 1 → params.matchingDenominator = 8 →
      ∀ {m : Nat} {initial first last : State m} (setup : Initialization params initial first)
        (history : History params first last) (seed : Nat),
        initial.Initial params → InterfaceForest.excess initial ≤ params.valueBound * seed →
        totalActivity history.operations + history.boundary ≤
          constant * volume setup history seed *
            Splay.Analysis.coefficientFactor coefficients params.valueBound := by
  obtain ⟨constant, positive, absorb⟩ :=
    Splay.Accounting.boundary_credit_rate_bound 32 1 (by decide)
  refine ⟨constant, positive, ?_⟩
  intro coefficients valid params same exempt numerator denominator m initial first last
    setup history seed initialized excessBound
  let gap := params.valueBound
  let size := volume setup history seed
  let a := (coefficients gap).1
  let b := (coefficients gap).2
  change totalActivity history.operations + history.boundary ≤
    constant * size * Splay.Analysis.coefficientFactor coefficients gap
  rw [Splay.Analysis.coefficientFactor, ← Nat.mul_assoc]
  apply absorb _ size _ _ (Splay.Analysis.coefficientRate_pos coefficients gap)
  · have execution := trace setup history initialized.1
    have raw := valid params same initialized execution
    rw [activity] at raw
    have changes := InterfaceForest.valueChanges_le_excess initialized.1 execution
    have ins := inserts setup history
    have values := value_charge setup history initialized.1
    have gapPositive : 0 < gap := lt_of_lt_of_le (by decide : 0 < 2) params.valueBound_ge_two
    have volumeBound : seed + setup.mass + history.rotations + history.maintenanceCost ≤ size := by
      dsimp [size, volume]
      omega
    have insertsBound : totalInserts (operations setup history) ≤ 2 * (size + history.boundary) := by
      omega
    have valuesBound : totalValueChanges (operations setup history) ≤
        32 * gap * (size + history.boundary) := by
      have scaledVolume := Nat.mul_le_mul_left (32 * gap) volumeBound
      have maintenanceScaled := Nat.mul_le_mul_left (4 * history.maintenanceCost) gapPositive
      change InterfaceForest.excess initial ≤ gap * seed at excessBound
      change 2 * totalIncreases (operations setup history) + InterfaceForest.excess initial ≤
        3 * InterfaceForest.excess initial + 12 * gap * setup.mass +
          32 * gap * history.boundary + 12 * gap * history.rotations +
          4 * history.maintenanceCost at values
      nlinarith
    change totalActivity history.operations ≤
      a * totalInserts (operations setup history) +
        b * totalValueChanges (operations setup history) at raw
    have enlarged := raw.trans (Nat.add_le_add
      (Nat.mul_le_mul_left a insertsBound) (Nat.mul_le_mul_left b valuesBound))
    change totalActivity history.operations ≤ 32 * (a + gap * b + 1) * (size + history.boundary)
    apply enlarged.trans
    ring_nf
    omega
  · intro cutoff
    simpa only [Nat.mul_one] using
      boundary_estimate setup history initialized seed cutoff exempt numerator denominator

/-- The same physical forest evolution accepts the stronger coefficient
bound. No local geometry, common word, or component initialization changes. -/
theorem forest_splay_bound_of_coefficients (shape : Shape) (slack depth : Nat) :
    ∃ constant : Nat, 0 < constant ∧ ∀ coefficients : ActivityCoefficients,
      CoefficientBound shape coefficients →
      ∀ (params : Parameters), params.toShape = shape →
      params.exemptPasses = 2 → params.matchingNumerator = 1 → params.matchingDenominator = 8 →
      ∀ {m : Nat} {initial first last : State m} (setup : Initialization params initial first)
        (history : History params first last) (before after : Forest) (seed : Nat),
        initial.Initial params → InterfaceForest.excess initial ≤ params.valueBound * seed →
        Evolution slack depth history before after →
        history.splayCost + history.maintenanceCost ≤
          constant * structuralVolume setup history before seed *
            Splay.Analysis.coefficientFactor coefficients params.valueBound := by
  obtain ⟨pairConstant, pairPositive, pairingBound⟩ := activity_add_boundary_of_coefficients shape
  let linear := 20 + 12 * (slack+1)
  let constant := 4 * pairConstant * normalCoefficient slack depth + linear
  refine ⟨constant, by dsimp [constant, linear]; omega, ?_⟩
  intro coefficients valid params same exempt numerator denominator m initial first last setup
    history before after seed initialized excessBound evolution
  let factor := Splay.Analysis.coefficientFactor coefficients params.valueBound
  let size := structuralVolume setup history before seed
  have factorPositive : 0 < factor := Splay.Analysis.coefficientFactor_pos _ _
  have pairings := pairingBound coefficients valid params same exempt numerator denominator
    setup history seed initialized excessBound
  have volumeBound := volume_bound setup evolution (seed := seed)
  have boundedPairings : totalActivity history.operations + history.boundary ≤
      pairConstant * normalCoefficient slack depth * size * factor := by
    calc
      _ ≤ pairConstant * volume setup history seed * factor := pairings
      _ ≤ pairConstant * (normalCoefficient slack depth * size) * factor := by gcongr
      _ = _ := by ring
  have paid := evolution.cost_le_pairings
  have linearBound : 2 * before.keys + (6+12*(slack+1)) * history.requests +
      8 * history.rotations + 3 * history.maintenanceCost ≤ linear * size := by
    dsimp [linear, size, structuralVolume]
    nlinarith
  have linearScaled : linear * size ≤ linear * size * factor := by
    simpa using Nat.mul_le_mul_left (linear * size) factorPositive
  change history.splayCost + history.maintenanceCost ≤ constant * size * factor
  calc
    _ ≤ 4 * (totalActivity history.operations + history.boundary) + linear * size := by omega
    _ ≤ 4 * (pairConstant * normalCoefficient slack depth * size * factor) + linear * size * factor :=
      Nat.add_le_add (Nat.mul_le_mul_left 4 boundedPairings) linearScaled
    _ = _ := by dsimp [constant]; ring

/-- The strongest current Splay envelope also holds for the persistent
forest. The comparison volume remains explicit in the conclusion. -/
theorem forest_splay_bound_layerEnvelope (shape : Shape) (slack depth : Nat)
    (smallShape : Splay.Interface.LayerCompression.shapeConstant shape ≤ 31)
    (exempt : shape.exemptPasses = 2) (numerator : shape.matchingNumerator = 1)
    (denominator : shape.matchingDenominator = 8) :
    ∃ constant : Nat, 0 < constant ∧ ∀ (params : Parameters), params.toShape = shape →
      ∀ {m : Nat} {initial first last : State m} (setup : Initialization params initial first)
        (history : History params first last) (before after : Forest) (seed : Nat),
        initial.Initial params → InterfaceForest.excess initial ≤ params.valueBound * seed →
        Evolution slack depth history before after →
        history.splayCost + history.maintenanceCost ≤
          constant * structuralVolume setup history before seed * params.valueBound *
            (Nat.clog 2 params.valueBound + 1) * Splay.Analysis.LayerEnvelope.E params.valueBound := by
  obtain ⟨constant, positive, bound⟩ := forest_splay_bound_of_coefficients shape slack depth
  refine ⟨16 * constant, by positivity, ?_⟩
  intro params same m initial first last setup history before after seed initialized excessBound evolution
  let coefficients := Splay.Interface.LayerCoefficients.coefficients shape
  have valid : CoefficientBound shape coefficients :=
    Splay.Interface.LayerCoefficients.valid shape exempt numerator denominator
  have actual := bound coefficients valid params same
    ((congrArg Shape.exemptPasses same).trans exempt)
    ((congrArg Shape.matchingNumerator same).trans numerator)
    ((congrArg Shape.matchingDenominator same).trans denominator)
    setup history before after seed initialized excessBound evolution
  have estimates := Splay.Analysis.LayerEnvelope.coefficients_le shape smallShape params.valueBound
  have factor := Splay.Analysis.coefficientFactor_le_envelope coefficients params.valueBound
    (Splay.Analysis.LayerEnvelope.envelope (Splay.Analysis.LayerEnvelope.depth params.valueBound))
    (lt_of_lt_of_le (by decide : 0 < 2) params.valueBound_ge_two)
    (Splay.Analysis.LayerEnvelope.envelope_pos _) estimates.1 estimates.2
  calc
    _ ≤ constant * structuralVolume setup history before seed *
        Splay.Analysis.coefficientFactor coefficients params.valueBound := actual
    _ ≤ constant * structuralVolume setup history before seed *
        (16 * params.valueBound *
          Splay.Analysis.LayerEnvelope.envelope (Splay.Analysis.LayerEnvelope.depth params.valueBound) ^ 2 *
          (Nat.clog 2 params.valueBound + 1)) := Nat.mul_le_mul_left _ factor
    _ = _ := by unfold Splay.Analysis.LayerEnvelope.E; ring

end MultiSplay.SharedSplay.Initialized
