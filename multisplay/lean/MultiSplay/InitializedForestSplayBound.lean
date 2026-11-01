import MultiSplay.ForestSplayBound
import MultiSplay.SharedInitialization

/-!
# Linear initialization in the forest splay comparison

The initializer is executed once in the same shared history. Its mass counts
external component slots, rather than its G-dependent unit value changes.
Thus the initial term has the same splay factor as the later structural work.
-/

noncomputable section

namespace MultiSplay.SharedSplay.Initialized

open Splay.Interface

variable {m : Nat} {params : Parameters} {initial first last : State m}

def operations (setup : Initialization params initial first) (history : History params first last) :=
  setup.operations ++ history.operations

def volume (setup : Initialization params initial first) (history : History params first last) (seed : Nat) :=
  seed + 2 * setup.mass + history.rotations + history.births + 2 * history.maintenanceCost

def structuralVolume (setup : Initialization params initial first) (history : History params first last) (forest : Forest) (seed : Nat) :=
  seed + 2 * setup.mass + forest.keys + history.requests + history.rotations + history.maintenanceCost

theorem trace (setup : Initialization params initial first) (history : History params first last) (valid : initial.Valid params) :
    Trace params initial (operations setup history) last := by
  have start := setup.trace valid
  exact InterfaceForest.trace_append start (history.trace (InterfaceForest.trace_final_valid start))

@[simp] theorem activity (setup : Initialization params initial first) (history : History params first last) :
    totalActivity (operations setup history) = totalActivity history.operations := by
  simp [operations, totalActivity_append, setup.activity]

theorem inserts (setup : Initialization params initial first) (history : History params first last) :
    totalInserts (operations setup history) ≤ setup.mass + history.rotations + 2 * history.boundary + history.maintenanceCost := by
  have a := setup.inserts
  have b := history.inserts
  simp only [operations, totalInserts_append]
  omega

theorem value_charge (setup : Initialization params initial first) (history : History params first last)
    (valid : initial.Valid params) :
    2 * totalIncreases (operations setup history) + InterfaceForest.excess initial ≤
      3 * InterfaceForest.excess initial + 12 * params.valueBound * setup.mass +
        32 * params.valueBound * history.boundary + 12 * params.valueBound * history.rotations + 4 * history.maintenanceCost := by
  have start := setup.trace valid
  have balance := InterfaceForest.excess_balance valid start
  have increase := setup.increases
  have good := history.good_charge (InterfaceForest.trace_final_valid start)
  have later := history.increases
  simp only [operations, totalIncreases_append]
  nlinarith

theorem boundary_estimate (setup : Initialization params initial first) (history : History params first last)
    (initialized : initial.Initial params) (seed cutoff : Nat) (exempt : params.exemptPasses = 2)
    (numerator : params.matchingNumerator = 1) (denominator : params.matchingDenominator = 8) :
    cutoff * (2 * history.boundary) ≤ 4 * cutoff * boundaryCreditCapacity cutoff * volume setup history seed +
      16 * totalActivity history.operations := by
  have initialCredit := setup.boundary_credit initialized cutoff
  have paid := history.boundary_credit cutoff exempt numerator denominator
  have weighted := Nat.mul_le_mul_left (4 * cutoff) initialCredit
  have reserve : 2 * setup.mass + history.births + 2 * history.maintenanceCost ≤ volume setup history seed := by
    unfold volume
    omega
  have enlarged := Nat.mul_le_mul_left (4 * cutoff * boundaryCreditCapacity cutoff) reserve
  nlinarith

/-- Uniform pairing bound including the actual once-only initialization. -/
theorem activity_add_boundary (shape : Shape) :
    ∃ constant : Nat, 0 < constant ∧ ∀ (params : Parameters), params.toShape = shape →
      params.exemptPasses = 2 → params.matchingNumerator = 1 → params.matchingDenominator = 8 →
      ∀ {m : Nat} {initial first last : State m} (setup : Initialization params initial first)
        (history : History params first last) (seed : Nat),
        initial.Initial params → InterfaceForest.excess initial ≤ params.valueBound * seed →
        totalActivity history.operations + history.boundary ≤
          constant * volume setup history seed * params.valueBound * (Nat.clog 2 params.valueBound + 1)^2 := by
  obtain ⟨a, b, aPositive, bPositive, blackbox⟩ := InterfaceForest.activity_le_excess shape
  let coefficient := 64 * (a+b+1)
  have positive : 0 < coefficient := by dsimp [coefficient]; omega
  obtain ⟨constant, constantPositive, absorb⟩ := Splay.Accounting.boundary_credit_uniform_bound coefficient 1 positive
  refine ⟨constant, constantPositive, ?_⟩
  intro params same exempt numerator denominator m initial first last setup history seed initialized excessBound
  let gap := params.valueBound
  let size := volume setup history seed
  have gapPositive : 0 < gap := lt_of_lt_of_le (by decide : 0 < 2) params.valueBound_ge_two
  apply absorb gap size (totalActivity history.operations) history.boundary gapPositive
  · have raw := blackbox params same initialized (trace setup history initialized.1)
    rw [activity] at raw
    have ins := inserts setup history
    have values := value_charge setup history initialized.1
    have volumeBound : seed + setup.mass + history.rotations + history.maintenanceCost ≤ size := by
      dsimp [size, volume]
      omega
    have insertsBound : totalInserts (operations setup history) ≤ 2 * (size + history.boundary) := by omega
    have valuesBound : 2 * totalIncreases (operations setup history) + InterfaceForest.excess initial ≤
        32 * gap * (size + history.boundary) := by
      have scaledVolume := Nat.mul_le_mul_left (32 * gap) volumeBound
      have maintenanceScaled := Nat.mul_le_mul_left (4 * history.maintenanceCost) gapPositive
      change InterfaceForest.excess initial ≤ gap * seed at excessBound
      change 2 * totalIncreases (operations setup history) + InterfaceForest.excess initial ≤
        3 * InterfaceForest.excess initial + 12 * gap * setup.mass + 32 * gap * history.boundary +
          12 * gap * history.rotations + 4 * history.maintenanceCost at values
      nlinarith
    have enlarged : totalActivity history.operations ≤ a * gap * (2 * (size + history.boundary)) +
        b * Nat.clog 2 gap * (32 * gap * (size + history.boundary)) :=
      raw.trans (Nat.add_le_add (Nat.mul_le_mul_left _ insertsBound) (Nat.mul_le_mul_left _ valuesBound))
    have firstTerm : a * gap * (2 * (size + history.boundary)) ≤
        2 * a * gap * (Nat.clog 2 gap + 1) * (size + history.boundary) := by
      calc
        _ = 2 * a * gap * 1 * (size + history.boundary) := by ring
        _ ≤ _ := by gcongr; omega
    have secondTerm : b * Nat.clog 2 gap * (32 * gap * (size + history.boundary)) ≤
        32 * b * gap * (Nat.clog 2 gap + 1) * (size + history.boundary) := by
      calc
        _ = 32 * b * gap * Nat.clog 2 gap * (size + history.boundary) := by ring
        _ ≤ _ := by gcongr; omega
    have coefficientBound : 2*a + 32*b ≤ coefficient := by dsimp [coefficient]; omega
    have weighted := Nat.mul_le_mul_right (gap * (Nat.clog 2 gap + 1) * (size + history.boundary)) coefficientBound
    nlinarith
  · intro cutoff
    simpa only [Nat.mul_one] using boundary_estimate setup history initialized seed cutoff exempt numerator denominator

theorem volume_bound (setup : Initialization params initial first) {history : History params first last}
    {before after : Forest} {slack depth seed : Nat} (evolution : Evolution slack depth history before after) :
    volume setup history seed ≤ normalCoefficient slack depth * structuralVolume setup history before seed := by
  have born := evolution.births
  dsimp [volume, structuralVolume, normalCoefficient]
  nlinarith

/-- Full splay-side theorem with a linear one-time initialization term. All
constants precede the value cap, universe size, forest and access history. -/
theorem forest_splay_bound (shape : Shape) (slack depth : Nat) :
    ∃ constant : Nat, 0 < constant ∧ ∀ (params : Parameters), params.toShape = shape →
      params.exemptPasses = 2 → params.matchingNumerator = 1 → params.matchingDenominator = 8 →
      ∀ {m : Nat} {initial first last : State m} (setup : Initialization params initial first)
        (history : History params first last) (before after : Forest) (seed : Nat),
        initial.Initial params → InterfaceForest.excess initial ≤ params.valueBound * seed →
        Evolution slack depth history before after →
        history.splayCost + history.maintenanceCost ≤ constant * structuralVolume setup history before seed *
          params.valueBound * (Nat.clog 2 params.valueBound + 1)^2 := by
  obtain ⟨pairConstant, pairPositive, pairingBound⟩ := activity_add_boundary shape
  let linear := 20 + 12 * (slack+1)
  let constant := 4 * pairConstant * normalCoefficient slack depth + linear
  refine ⟨constant, by dsimp [constant, linear]; omega, ?_⟩
  intro params same exempt numerator denominator m initial first last setup history before after seed initialized excessBound evolution
  let gap := params.valueBound
  let factor := gap * (Nat.clog 2 gap + 1)^2
  let size := structuralVolume setup history before seed
  have factorPositive : 0 < factor := by
    have gapPositive : 0 < gap := lt_of_lt_of_le (by decide : 0 < 2) params.valueBound_ge_two
    dsimp [factor]
    positivity
  have pairings := pairingBound params same exempt numerator denominator setup history seed initialized excessBound
  have volumeBound := volume_bound setup evolution (seed := seed)
  have boundedPairings : totalActivity history.operations + history.boundary ≤
      pairConstant * normalCoefficient slack depth * size * factor := by
    calc
      _ ≤ pairConstant * volume setup history seed * gap * (Nat.clog 2 gap + 1)^2 := pairings
      _ ≤ pairConstant * (normalCoefficient slack depth * size) * gap * (Nat.clog 2 gap + 1)^2 := by gcongr
      _ = _ := by dsimp [factor]; ring
  have paid := evolution.cost_le_pairings
  have linearBound : 2 * before.keys + (6+12*(slack+1)) * history.requests +
      8 * history.rotations + 3 * history.maintenanceCost ≤ linear * size := by
    dsimp [linear, size, structuralVolume]
    nlinarith
  have linearScaled : linear * size ≤ linear * size * factor := by
    simpa using Nat.mul_le_mul_left (linear * size) factorPositive
  change history.splayCost + history.maintenanceCost ≤ constant * size * gap * (Nat.clog 2 gap + 1)^2
  calc
    _ ≤ 4 * (totalActivity history.operations + history.boundary) + linear * size := by omega
    _ ≤ 4 * (pairConstant * normalCoefficient slack depth * size * factor) + linear * size * factor :=
      Nat.add_le_add (Nat.mul_le_mul_left 4 boundedPairings) linearScaled
    _ = _ := by dsimp [constant, factor]; ring

end MultiSplay.SharedSplay.Initialized
