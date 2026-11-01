import Splay.Analysis.IteratedLog
import Mathlib.Tactic

namespace Splay.Accounting

/-- Maximum contracted point gap exported by a comparison-tree height bound. -/
def gapBound (height : ℕ) : ℕ :=
  Analysis.contractedGap (height + 1)

/-- Logarithmic factor used by the abstract pairing interface. -/
def gapLog (height : ℕ) : ℕ :=
  Analysis.stabilizedLog (gapBound height)

@[simp]
theorem gapBound_pos (height : ℕ) : 0 < gapBound height := by
  unfold gapBound Analysis.contractedGap
  omega

@[simp]
theorem gapLog_pos (height : ℕ) : 0 < gapLog height :=
  Analysis.stabilizedLog_pos _

/-- Universal constants hidden by the local `O(·)` bounds in the manuscript. -/
structure Constants where
  blocks : ℕ
  important : ℕ
  interface : ℕ
  paid : ℕ
  unimportantThreshold : ℕ
  bends : ℕ
  /--
  A factor `64`, instead of the manuscript's `32`, absorbs both copies of the
  unimportant-pairing term without assuming the unstated inequality `u ≤ p`.
  -/
  threshold_large :
    64 * interface ≤ unimportantThreshold

namespace Constants

/-- Coefficient after absorbing unimportant pairings into internal pairings. -/
def internalCoefficient (constants : Constants) : ℕ :=
  2 * constants.interface * (constants.paid + 1)

/-- Coefficient bounding twice the number of zig-zigs. -/
def pairingCoefficient (constants : Constants) : ℕ :=
  constants.important * constants.blocks +
    2 * constants.internalCoefficient

/-- Uniform coefficient for the complete local splay accounting. -/
def coreConstant (constants : Constants) : ℕ :=
  2 + 2 * constants.pairingCoefficient + 2 * constants.bends

theorem coreConstant_pos (constants : Constants) :
    0 < constants.coreConstant := by
  unfold coreConstant
  omega

end Constants

/--
Exact natural-number certificate corresponding to the global accounting
lemmas in `putting-everything-together.tex`.

The internal-pairing bound deliberately retains the `unimportant` term. This
avoids the first missing inequality in the manuscript (`unimportant ≤ paid`);
the stronger threshold condition in `Constants` absorbs it later.
-/
structure Certificate (constants : Constants)
    (n nearCost height splayCost : ℕ) where
  blocks : ℕ
  paid : ℕ
  important : ℕ
  unimportant : ℕ
  internal : ℕ
  accesses : ℕ
  zig : ℕ
  zigZig : ℕ
  zigZag : ℕ

  blocks_le :
    blocks ≤ constants.blocks * (n + nearCost)
  important_le :
    important ≤ constants.important * blocks * gapLog height
  paid_le :
    paid ≤
      unimportant + constants.paid * (n + nearCost) * gapLog height
  internal_preabsorb :
    internal ≤
      constants.interface *
        (paid * gapBound height * gapLog height +
          unimportant * gapBound height * gapLog height +
          (n + nearCost) * gapBound height * gapLog height ^ 2)
  local_charge :
    constants.unimportantThreshold * gapBound height * gapLog height *
        unimportant ≤
      16 * internal
  unimportant_le_internal :
    unimportant ≤ internal
  zigZig_pairings :
    2 * zigZig ≤ important + unimportant + internal
  zigZag_bends :
    zigZag ≤ zigZig + constants.bends * (n + nearCost)
  accesses_le :
    accesses ≤ nearCost
  zig_le :
    zig ≤ accesses
  cost_le :
    splayCost ≤ accesses + zig + 2 * zigZig + 2 * zigZag

namespace Certificate

variable {constants : Constants}
  {n nearCost height splayCost : ℕ}

/--
Self-charge absorption with the unimportant term retained explicitly.
-/
theorem internal_le
    (certificate : Certificate constants n nearCost height splayCost) :
    certificate.internal ≤
      constants.internalCoefficient *
        (n + nearCost) * gapBound height * gapLog height ^ 2 := by
  let base := n + nearCost
  let gap := gapBound height
  let log := gapLog height
  let selfTerm :=
    2 * constants.interface * certificate.unimportant * gap * log
  let remainder :=
    constants.interface * (constants.paid + 1) * base * gap * log ^ 2

  have hPaidScaled :
      certificate.paid * gap * log ≤
        (certificate.unimportant +
          constants.paid * base * log) * gap * log :=
    Nat.mul_le_mul_right log
      (Nat.mul_le_mul_right gap certificate.paid_le)
  have hBeforeAbsorption :
      certificate.internal ≤ selfTerm + remainder := by
    calc
      certificate.internal ≤
          constants.interface *
            (certificate.paid * gap * log +
              certificate.unimportant * gap * log +
              base * gap * log ^ 2) := certificate.internal_preabsorb
      _ ≤ constants.interface *
            (((certificate.unimportant +
                constants.paid * base * log) * gap * log) +
              certificate.unimportant * gap * log +
              base * gap * log ^ 2) := by
        exact Nat.mul_le_mul_left _
          (Nat.add_le_add_right
            (Nat.add_le_add_right hPaidScaled _) _)
      _ = selfTerm + remainder := by
        simp only [selfTerm, remainder]
        ring

  have hThresholdScaled :
      64 * constants.interface * (gap * log * certificate.unimportant) ≤
        constants.unimportantThreshold *
          (gap * log * certificate.unimportant) :=
    Nat.mul_le_mul_right _ constants.threshold_large
  have hSelfCharge :
      2 * selfTerm ≤ certificate.internal := by
    have hToSixteen :
        64 * constants.interface *
            (gap * log * certificate.unimportant) ≤
          16 * certificate.internal := by
      exact hThresholdScaled.trans (by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          certificate.local_charge)
    apply Nat.le_of_mul_le_mul_left (c := 16) _ (by omega)
    calc
      16 * (2 * selfTerm) =
          64 * constants.interface *
            (gap * log * certificate.unimportant) := by
        simp only [selfTerm]
        ring
      _ ≤ 16 * certificate.internal := hToSixteen

  have hAbsorbed :
      certificate.internal ≤ 2 * remainder := by
    omega
  calc
    certificate.internal ≤ 2 * remainder := hAbsorbed
    _ = constants.internalCoefficient * base * gap * log ^ 2 := by
      simp only [remainder, Constants.internalCoefficient]
      ring

/-- The height-scaled factor is at least the unscaled base count. -/
theorem base_le_scaled (height n nearCost : ℕ) :
    n + nearCost ≤
      (n + nearCost) * gapBound height * gapLog height ^ 2 := by
  have hGap := gapBound_pos height
  have hLog := gapLog_pos height
  have hLogSquared : 1 ≤ gapLog height ^ 2 :=
    Nat.one_le_pow 2 (gapLog height) hLog
  calc
    n + nearCost = (n + nearCost) * 1 * 1 := by simp
    _ ≤ (n + nearCost) * gapBound height * gapLog height ^ 2 :=
      Nat.mul_le_mul
        (Nat.mul_le_mul_left (n + nearCost) hGap) hLogSquared

/-- Important boundary pairings are bounded by the common height scale. -/
theorem important_le_scaled
    (certificate : Certificate constants n nearCost height splayCost) :
    certificate.important ≤
      (constants.important * constants.blocks) *
        (n + nearCost) * gapBound height * gapLog height ^ 2 := by
  calc
    certificate.important ≤
        constants.important * certificate.blocks * gapLog height :=
      certificate.important_le
    _ ≤ constants.important *
          (constants.blocks * (n + nearCost)) * gapLog height :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ certificate.blocks_le)
    _ ≤ (constants.important * constants.blocks) *
          (n + nearCost) * gapBound height * gapLog height ^ 2 := by
      have hGap := gapBound_pos height
      have hLog := gapLog_pos height
      have hGapOne : 1 ≤ gapBound height := hGap
      have hLogOne : 1 ≤ gapLog height := hLog
      have hLogLeSquared :
          gapLog height ≤ gapLog height ^ 2 := by
        simpa only [pow_two, mul_one] using
          Nat.mul_le_mul_left (gapLog height) hLogOne
      have hLogScaled :
          gapLog height ≤ gapBound height * gapLog height ^ 2 :=
        hLogLeSquared.trans (by
          simpa only [one_mul] using
            Nat.mul_le_mul_right (gapLog height ^ 2) hGapOne)
      simpa only [mul_assoc] using
        Nat.mul_le_mul_left
          (constants.important * (constants.blocks * (n + nearCost)))
          hLogScaled

/-- Twice the zig-zig count is bounded by the common height scale. -/
theorem two_zigZig_le_scaled
    (certificate : Certificate constants n nearCost height splayCost) :
    2 * certificate.zigZig ≤
      constants.pairingCoefficient *
        (n + nearCost) * gapBound height * gapLog height ^ 2 := by
  let scale := (n + nearCost) * gapBound height * gapLog height ^ 2
  have hImportant := certificate.important_le_scaled
  have hInternal := certificate.internal_le
  have hUnimportant := certificate.unimportant_le_internal
  have hImportantScaled :
      certificate.important ≤
        (constants.important * constants.blocks) * scale := by
    simpa only [scale, mul_assoc] using hImportant
  have hInternalScaled :
      certificate.internal ≤
        constants.internalCoefficient * scale := by
    simpa only [scale, mul_assoc] using hInternal
  have hScaled :
      2 * certificate.zigZig ≤
        constants.pairingCoefficient * scale := by
    calc
      2 * certificate.zigZig ≤
          certificate.important + certificate.unimportant +
            certificate.internal :=
        certificate.zigZig_pairings
      _ ≤ certificate.important + 2 * certificate.internal := by omega
      _ ≤ (constants.important * constants.blocks) * scale +
            2 * (constants.internalCoefficient * scale) :=
        Nat.add_le_add hImportantScaled
          (Nat.mul_le_mul_left 2 hInternalScaled)
      _ = constants.pairingCoefficient * scale := by
        simp only [Constants.pairingCoefficient, scale]
        ring
  simpa only [scale, mul_assoc] using hScaled

/--
The entire splay cost is bounded by the height-scaled factor with one uniform
constant determined solely by the manuscript's local constants.
-/
theorem cost_bound
    (certificate : Certificate constants n nearCost height splayCost) :
    splayCost ≤
      constants.coreConstant *
        (n + nearCost) * gapBound height * gapLog height ^ 2 := by
  let scale := (n + nearCost) * gapBound height * gapLog height ^ 2
  have hBase : n + nearCost ≤ scale :=
    base_le_scaled height n nearCost
  have hAccesses : certificate.accesses ≤ scale :=
    certificate.accesses_le.trans (Nat.le_add_left _ _ |>.trans hBase)
  have hZig : certificate.zig ≤ scale :=
    certificate.zig_le.trans hAccesses
  have hZigZig :
      2 * certificate.zigZig ≤
        constants.pairingCoefficient * scale := by
    simpa only [scale, mul_assoc] using
      certificate.two_zigZig_le_scaled
  have hZigZag :
      2 * certificate.zigZag ≤
        constants.pairingCoefficient * scale +
          2 * constants.bends * scale := by
    calc
      2 * certificate.zigZag ≤
          2 * certificate.zigZig +
            2 * (constants.bends * (n + nearCost)) :=
        (Nat.mul_le_mul_left 2 certificate.zigZag_bends).trans_eq (by
          rw [Nat.mul_add])
      _ ≤ constants.pairingCoefficient * scale +
            2 * constants.bends * scale := by
        exact Nat.add_le_add hZigZig
          (by
            simpa only [mul_assoc] using
              Nat.mul_le_mul_left (2 * constants.bends) hBase)
  have hCost : splayCost ≤ constants.coreConstant * scale := by
    calc
      splayCost ≤
          certificate.accesses + certificate.zig +
            2 * certificate.zigZig + 2 * certificate.zigZag :=
        certificate.cost_le
      _ ≤ scale + scale +
            constants.pairingCoefficient * scale +
            (constants.pairingCoefficient * scale +
              2 * constants.bends * scale) :=
        Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add hAccesses hZig) hZigZig)
          hZigZag
      _ = constants.coreConstant * scale := by
        simp only [Constants.coreConstant]
        ring
  simpa only [scale, mul_assoc] using hCost

end Certificate

end Splay.Accounting
