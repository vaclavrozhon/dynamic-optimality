import Splay.Interface.JoinHistory
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring

namespace Splay.Interface

/--
One source batch in a fixed `(lineage root, inherited pass count)` fiber.

For an actual pass, `beforeMass`, `afterMass`, and `activity` are respectively
the source size before the pass, its size afterward, and the matching size.
A terminal batch (elements whose branch never performs this pass count) has
zero `afterMass` and zero `activity`.  Deletions may make `balance` strict.
-/
structure DescendantBatch (params : Parameters) where
  beforeMass : ℕ
  afterMass : ℕ
  activity : ℕ
  balance : afterMass + activity ≤ beforeMass
  weightedDecay :
    params.matchingDenominator * afterMass +
        params.matchingNumerator * beforeMass ≤
      params.matchingDenominator * beforeMass

namespace DescendantBatch

/--
The size data exported by one genuine nonexempt pass is a descendant batch.
This constructor is the direct bridge from `MatchingValid.weighted_decay`.
-/
def ofMatching {n : ℕ} {params : Parameters} {state : State n}
    {sourceId : BlockId} {source : Block n}
    {matching : List (Pairing n)}
    (valid : MatchingValid params state sourceId source matching)
    (nonexempt : params.exemptPasses ≤ source.passCount) :
    DescendantBatch params :=
  { beforeMass := source.elements.length
    afterMass := (removeLosers source.elements matching).length
    activity := matching.length
    balance := by
      rw [valid.removeLosers_length_add]
    weightedDecay := valid.weighted_decay nonexempt }

/--
A branch which never reaches the next pass-count fiber can be closed by a
terminal batch.  Its whole payload disappears from the next fiber without
contributing activity.
-/
def terminal (params : Parameters) (mass : ℕ) :
    DescendantBatch params :=
  { beforeMass := mass
    afterMass := 0
    activity := 0
    balance := by simp
    weightedDecay := by
      have numerator_le :
          params.matchingNumerator ≤ params.matchingDenominator := by
        have half := params.matchingFraction_le_half
        omega
      simpa using Nat.mul_le_mul_right mass numerator_le }

end DescendantBatch

namespace DescendantBatches

def beforeMass {params : Parameters}
    (batches : List (DescendantBatch params)) : ℕ :=
  (batches.map DescendantBatch.beforeMass).sum

def afterMass {params : Parameters}
    (batches : List (DescendantBatch params)) : ℕ :=
  (batches.map DescendantBatch.afterMass).sum

def activity {params : Parameters}
    (batches : List (DescendantBatch params)) : ℕ :=
  (batches.map DescendantBatch.activity).sum

/-- Local source balances add across all split descendants. -/
theorem after_add_activity_le_before {params : Parameters}
    (batches : List (DescendantBatch params)) :
    afterMass batches + activity batches ≤ beforeMass batches := by
  induction batches with
  | nil =>
      simp [beforeMass, afterMass, activity]
  | cons head tail ih =>
      simp only [beforeMass, afterMass, activity, List.map_cons,
        List.sum_cons] at ih ⊢
      calc
        head.afterMass +
              (tail.map DescendantBatch.afterMass).sum +
            (head.activity +
              (tail.map DescendantBatch.activity).sum) =
            (head.afterMass + head.activity) +
              ((tail.map DescendantBatch.afterMass).sum +
                (tail.map DescendantBatch.activity).sum) := by
          omega
        _ ≤
            head.beforeMass +
              (tail.map DescendantBatch.beforeMass).sum :=
          Nat.add_le_add head.balance ih

/-- Division-free local decay likewise adds over all descendant sources. -/
theorem weighted_decay {params : Parameters}
    (batches : List (DescendantBatch params)) :
    params.matchingDenominator * afterMass batches +
        params.matchingNumerator * beforeMass batches ≤
      params.matchingDenominator * beforeMass batches := by
  induction batches with
  | nil =>
      simp [beforeMass, afterMass]
  | cons head tail ih =>
      simp only [beforeMass, afterMass, List.map_cons, List.sum_cons]
      calc
        params.matchingDenominator *
              (head.afterMass +
                (tail.map DescendantBatch.afterMass).sum) +
            params.matchingNumerator *
              (head.beforeMass +
                (tail.map DescendantBatch.beforeMass).sum) =
            (params.matchingDenominator * head.afterMass +
                params.matchingNumerator * head.beforeMass) +
              (params.matchingDenominator *
                  (tail.map DescendantBatch.afterMass).sum +
                params.matchingNumerator *
                  (tail.map DescendantBatch.beforeMass).sum) := by
              simp only [Nat.mul_add]
              omega
        _ ≤
            params.matchingDenominator * head.beforeMass +
              params.matchingDenominator *
                (tail.map DescendantBatch.beforeMass).sum :=
          Nat.add_le_add head.weightedDecay ih
        _ =
            params.matchingDenominator *
              (head.beforeMass +
                (tail.map DescendantBatch.beforeMass).sum) := by
          rw [Nat.mul_add]

end DescendantBatches

/--
The exact aggregate certificate for one inherited pass-count fiber.

`current_eq` is the essential coverage premise: the batches partition the
whole current fiber, including terminal branches.  `next_le` says every
element that reaches pass count `i + 1` is among the survivors of a batch at
pass count `i`.  Both premises concern lineage history across arbitrary
splits; neither follows from a collection of unrelated fixed-source
`PassRun`s alone.
-/
structure FiberLayer (params : Parameters)
    (currentMass nextMass layerActivity : ℕ) where
  batches : List (DescendantBatch params)
  current_eq :
    currentMass = DescendantBatches.beforeMass batches
  next_le :
    nextMass ≤ DescendantBatches.afterMass batches
  activity_eq :
    layerActivity = DescendantBatches.activity batches

namespace FiberLayer

/-- Aggregate activity and the successor fiber telescope against this fiber. -/
theorem retention {params : Parameters}
    {currentMass nextMass layerActivity : ℕ}
    (layer : FiberLayer params currentMass nextMass layerActivity) :
    nextMass + layerActivity ≤ currentMass := by
  obtain ⟨batches, current_eq, next_le, activity_eq⟩ := layer
  have localBound :=
    DescendantBatches.after_add_activity_le_before batches
  rw [current_eq, activity_eq]
  exact (Nat.add_le_add_right next_le _).trans localBound

/-- Aggregate geometric decay across every split descendant at this level. -/
theorem weighted_decay {params : Parameters}
    {currentMass nextMass layerActivity : ℕ}
    (layer : FiberLayer params currentMass nextMass layerActivity) :
    params.matchingDenominator * nextMass +
        params.matchingNumerator * currentMass ≤
      params.matchingDenominator * currentMass := by
  obtain ⟨batches, current_eq, next_le, activity_eq⟩ := layer
  have localBound := DescendantBatches.weighted_decay batches
  calc
    params.matchingDenominator * nextMass +
          params.matchingNumerator * currentMass ≤
        params.matchingDenominator *
              DescendantBatches.afterMass batches +
            params.matchingNumerator * currentMass :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_left _ next_le) _
    _ =
        params.matchingDenominator *
              DescendantBatches.afterMass batches +
            params.matchingNumerator *
              DescendantBatches.beforeMass batches := by
      rw [current_eq]
    _ ≤
        params.matchingDenominator *
          DescendantBatches.beforeMass batches :=
      localBound
    _ =
        params.matchingDenominator * currentMass := by
      rw [current_eq]

end FiberLayer

/--
A finite global decay profile for one root lineage over consecutive inherited
pass counts.  The functions are intentionally indexed by naturals: values
outside `0 .. steps` are irrelevant.
-/
structure FiberProfile (params : Parameters) (steps : ℕ) where
  mass : ℕ → ℕ
  activity : ℕ → ℕ
  layer :
    ∀ index < steps,
      FiberLayer params (mass index) (mass (index + 1)) (activity index)

namespace FiberProfile

/-- Number of denominator-sized halving blocks used by the global threshold. -/
def decayBlocks (params : Parameters) : ℕ :=
  Nat.clog 2 params.valueBound + 2

/-- Number of nonexempt inherited pass-count levels before the tail. -/
def decaySteps (params : Parameters) : ℕ :=
  params.matchingDenominator * decayBlocks params

/-- The manuscript's explicit insignificant-pass threshold. -/
def insignificantThreshold (params : Parameters) : ℕ :=
  params.exemptPasses + decaySteps params

/-- The chosen number of halving blocks dominates the required `4G` factor. -/
theorem four_mul_valueBound_le_pow_decayBlocks (params : Parameters) :
    4 * params.valueBound ≤ 2 ^ decayBlocks params := by
  have valueBound_le :
      params.valueBound ≤
        2 ^ Nat.clog 2 params.valueBound :=
    Nat.le_pow_clog (by omega) params.valueBound
  calc
    4 * params.valueBound ≤
        4 * 2 ^ Nat.clog 2 params.valueBound :=
      Nat.mul_le_mul_left 4 valueBound_le
    _ = 2 ^ decayBlocks params := by
      simp [decayBlocks, pow_add]
      ring

/--
The explicit threshold is logarithmic with a coefficient depending only on
the structural shape.
-/
theorem insignificantThreshold_le_shape_mul_clog
    (params : Parameters) :
    insignificantThreshold params ≤
      (params.exemptPasses +
          3 * params.matchingDenominator) *
        Nat.clog 2 params.valueBound := by
  let logarithm := Nat.clog 2 params.valueBound
  have logarithm_pos : 0 < logarithm := by
    dsimp [logarithm]
    exact Nat.clog_pos (by omega) (by
      exact lt_of_lt_of_le (by omega) params.valueBound_ge_two)
  have logarithm_one : 1 ≤ logarithm := logarithm_pos
  have exempt_scaled :
      params.exemptPasses ≤ params.exemptPasses * logarithm := by
    simpa using Nat.mul_le_mul_left params.exemptPasses logarithm_one
  have two_denominator_scaled :
      2 * params.matchingDenominator ≤
        2 * params.matchingDenominator * logarithm := by
    simpa using
      Nat.mul_le_mul_left (2 * params.matchingDenominator) logarithm_one
  change
    params.exemptPasses +
        params.matchingDenominator * (logarithm + 2) ≤
      (params.exemptPasses +
          3 * params.matchingDenominator) * logarithm
  calc
    params.exemptPasses +
          params.matchingDenominator * (logarithm + 2) =
        params.exemptPasses +
          params.matchingDenominator * logarithm +
          2 * params.matchingDenominator := by
      ring
    _ ≤
        params.exemptPasses * logarithm +
          params.matchingDenominator * logarithm +
          2 * params.matchingDenominator * logarithm :=
      Nat.add_le_add
        (Nat.add_le_add_right exempt_scaled _)
        two_denominator_scaled
    _ =
        (params.exemptPasses +
            3 * params.matchingDenominator) * logarithm := by
      ring

/-- Total activity in the profiled consecutive pass-count fibers. -/
def totalActivity {params : Parameters} {steps : ℕ}
    (profile : FiberProfile params steps) : ℕ :=
  (List.range steps |>.map profile.activity).sum

private theorem telescope
    {steps : ℕ} {mass activity : ℕ → ℕ}
    (retention :
      ∀ index < steps,
        mass (index + 1) + activity index ≤ mass index) :
    mass steps +
        (List.range steps |>.map activity).sum ≤
      mass 0 := by
  induction steps with
  | zero =>
      simp
  | succ steps ih =>
      have prefixRetention :
          ∀ index < steps,
            mass (index + 1) + activity index ≤ mass index := by
        intro index index_lt
        exact retention index (by omega)
      have prefixBound := ih prefixRetention
      have last := retention steps (by omega)
      rw [List.sum_range_succ]
      omega

/-- All activity after a fixed fiber level is paid by its initial population. -/
theorem mass_add_totalActivity_le {params : Parameters} {steps : ℕ}
    (profile : FiberProfile params steps) :
    profile.mass steps + profile.totalActivity ≤ profile.mass 0 := by
  apply telescope
  intro index index_lt
  exact (profile.layer index index_lt).retention

theorem totalActivity_le_initialMass {params : Parameters} {steps : ℕ}
    (profile : FiberProfile params steps) :
    profile.totalActivity ≤ profile.mass 0 := by
  have bound := profile.mass_add_totalActivity_le
  omega

/-- The aggregate profile satisfies the same weighted power decay as one run. -/
theorem weighted_decay {params : Parameters} {steps : ℕ}
    (profile : FiberProfile params steps) :
    params.matchingDenominator ^ steps * profile.mass steps ≤
      (params.matchingDenominator - params.matchingNumerator) ^ steps *
        profile.mass 0 := by
  apply weighted_decay_iterate
  · have half := params.matchingFraction_le_half
    omega
  · intro index index_lt
    exact (profile.layer index index_lt).weighted_decay

/--
After `matchingDenominator * blocks` nonexempt fiber levels, the remaining
mass has fallen by a factor of at least `2 ^ blocks`.
-/
theorem pow_two_mul_finalMass_le {params : Parameters} {steps blocks : ℕ}
    (profile : FiberProfile params steps)
    (steps_eq : steps = params.matchingDenominator * blocks) :
    2 ^ blocks * profile.mass steps ≤ profile.mass 0 := by
  let denominator := params.matchingDenominator
  let remaining :=
    params.matchingDenominator - params.matchingNumerator
  have denominator_pos : 0 < denominator := by
    have numerator_pos := params.matchingNumerator_pos
    have half := params.matchingFraction_le_half
    omega
  have weighted := profile.weighted_decay
  have powerComparison :=
    params.pow_two_mul_remaining_pow_blocks_le blocks
  have scaled :
      denominator ^ steps *
          (2 ^ blocks * profile.mass steps) ≤
        denominator ^ steps * profile.mass 0 := by
    calc
      denominator ^ steps *
            (2 ^ blocks * profile.mass steps) =
          2 ^ blocks *
            (denominator ^ steps * profile.mass steps) := by
        ac_rfl
      _ ≤
          2 ^ blocks *
            (remaining ^ steps * profile.mass 0) :=
        Nat.mul_le_mul_left _ weighted
      _ =
          (2 ^ blocks * remaining ^ steps) *
            profile.mass 0 := by
        ac_rfl
      _ ≤
          denominator ^ steps * profile.mass 0 := by
        apply Nat.mul_le_mul_right
        simpa [denominator, remaining, steps_eq] using powerComparison
  exact Nat.le_of_mul_le_mul_left scaled
    (Nat.pow_pos denominator_pos)

/--
Compose a decaying prefix with an arbitrary later tail.  This is the exact
form used for insignificant activity: once the prefix population is small,
all future matching activity telescopes against that remaining population.
-/
theorem scaled_tailActivity_le_initialMass
    {params : Parameters} {prefixSteps blocks tailSteps scale : ℕ}
    (prefixProfile : FiberProfile params prefixSteps)
    (tail : FiberProfile params tailSteps)
    (continuous :
      tail.mass 0 ≤ prefixProfile.mass prefixSteps)
    (prefixSteps_eq :
      prefixSteps = params.matchingDenominator * blocks)
    (scale_le : scale ≤ 2 ^ blocks) :
    scale * tail.totalActivity ≤ prefixProfile.mass 0 := by
  have tailBound := tail.totalActivity_le_initialMass
  have prefixBound :=
    prefixProfile.pow_two_mul_finalMass_le prefixSteps_eq
  calc
    scale * tail.totalActivity ≤
        2 ^ blocks * tail.totalActivity :=
      Nat.mul_le_mul_right _ scale_le
    _ ≤ 2 ^ blocks * tail.mass 0 :=
      Nat.mul_le_mul_left _ tailBound
    _ ≤ 2 ^ blocks * prefixProfile.mass prefixSteps :=
      Nat.mul_le_mul_left _ continuous
    _ ≤ prefixProfile.mass 0 :=
      prefixBound

/--
Concrete insignificant-tail estimate at the logarithmic threshold chosen
above.
-/
theorem insignificant_tail_scaled_le_initialMass
    {params : Parameters} {tailSteps : ℕ}
    (prefixProfile :
      FiberProfile params (decaySteps params))
    (tail : FiberProfile params tailSteps)
    (continuous :
      tail.mass 0 ≤ prefixProfile.mass (decaySteps params)) :
    4 * params.valueBound * tail.totalActivity ≤
      prefixProfile.mass 0 := by
  exact
    prefixProfile.scaled_tailActivity_le_initialMass tail continuous
      (blocks := decayBlocks params)
      (scale := 4 * params.valueBound)
      rfl (four_mul_valueBound_le_pow_decayBlocks params)

end FiberProfile

/-- One root-lineage charge after choosing a global insignificant threshold. -/
structure RootDecayCharge (scale : ℕ) where
  convertedMass : ℕ
  tailActivity : ℕ
  scaled_tail_le : scale * tailActivity ≤ convertedMass

namespace RootDecayCharge

/-- Root-lineage insignificant charges add without loss. -/
theorem sum_scaled_tail_le_converted
    {scale : ℕ} (charges : List (RootDecayCharge scale)) :
    scale * (charges.map RootDecayCharge.tailActivity).sum ≤
      (charges.map RootDecayCharge.convertedMass).sum := by
  induction charges with
  | nil =>
      simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, Nat.mul_add]
      exact Nat.add_le_add head.scaled_tail_le ih

/--
If converted root populations are charged to all lineage entries, the exact
global insignificant-activity inequality follows.
-/
theorem sum_scaled_tail_le_entryBudget
    {scale entryBudget : ℕ} (charges : List (RootDecayCharge scale))
    (converted_le :
      (charges.map RootDecayCharge.convertedMass).sum ≤ entryBudget) :
    scale * (charges.map RootDecayCharge.tailActivity).sum ≤ entryBudget :=
  (sum_scaled_tail_le_converted charges).trans converted_le

/--
The manuscript's global insignificant-activity target, once each converted
root lineage supplies its decay charge and converted populations are charged
to the exact entry budget.
-/
theorem global_insignificant_activity_bound
    {params : Parameters} {n : ℕ}
    {operations : List (Operation n)}
    (charges :
      List (RootDecayCharge (4 * params.valueBound)))
    (converted_le_entries :
      (charges.map RootDecayCharge.convertedMass).sum ≤
        totalActivity operations + totalInserts operations) :
    4 * params.valueBound *
        (charges.map RootDecayCharge.tailActivity).sum ≤
      totalActivity operations + totalInserts operations :=
  sum_scaled_tail_le_entryBudget charges converted_le_entries

end RootDecayCharge

/--
The remaining shift argument, separated from global decay.

The first inequality is exactly the output supplied by the root decay
profiles when `scale = 4 * valueBound`.  The second is the manuscript's
v/u/w-shift charging estimate.  Keeping both explicit prevents the missing
history-continuity proof from being smuggled into the arithmetic endpoint.
-/
def ShiftChargingHypothesis
    (shape : Shape) (insertShiftConstant valueShiftConstant : ℕ) : Prop :=
  ∀ (params : Parameters), params.toShape = shape →
    ∀ {n : ℕ} {initial final : State n}
      {operations : List (Operation n)},
      initial.Initial params →
      Trace params initial operations final →
      ∃ insignificantActivity : ℕ,
        4 * params.valueBound * insignificantActivity ≤
            totalActivity operations + totalInserts operations ∧
          totalActivity operations ≤
            2 * params.valueBound * insignificantActivity +
              insertShiftConstant * params.valueBound *
                totalInserts operations +
              valueShiftConstant * Nat.clog 2 params.valueBound *
                totalValueChanges operations

/--
Once the two explicit global charging estimates are available, the
`A / 2` absorption in the manuscript yields `ActivityBound` with concrete
constants depending only on `Shape`.
-/
theorem activityBound_of_shiftCharging
    (shape : Shape) (insertShiftConstant valueShiftConstant : ℕ)
    (charging :
      ShiftChargingHypothesis shape
        insertShiftConstant valueShiftConstant) :
    ActivityBound shape := by
  refine
    ⟨2 * insertShiftConstant + 1,
      2 * valueShiftConstant + 1, by omega, by omega, ?_⟩
  intro params params_shape n initial final operations initialState trace
  obtain ⟨insignificantActivity, decayCharge, shiftCharge⟩ :=
    charging params params_shape initialState trace
  let activity := totalActivity operations
  let inserts := totalInserts operations
  let changes := totalValueChanges operations
  let valueBound := params.valueBound
  let logarithm := Nat.clog 2 params.valueBound
  change
    4 * valueBound * insignificantActivity ≤ activity + inserts
      at decayCharge
  change
    activity ≤
      2 * valueBound * insignificantActivity +
        insertShiftConstant * valueBound * inserts +
        valueShiftConstant * logarithm * changes
      at shiftCharge
  have doubled :
      2 * activity ≤
        activity + inserts +
          2 * insertShiftConstant * valueBound * inserts +
          2 * valueShiftConstant * logarithm * changes := by
    calc
      2 * activity ≤
          2 *
            (2 * valueBound * insignificantActivity +
              insertShiftConstant * valueBound * inserts +
              valueShiftConstant * logarithm * changes) :=
        Nat.mul_le_mul_left 2 shiftCharge
      _ =
          4 * valueBound * insignificantActivity +
            2 * insertShiftConstant * valueBound * inserts +
            2 * valueShiftConstant * logarithm * changes := by
        simp only [Nat.mul_add]
        ring
      _ ≤
          (activity + inserts) +
            2 * insertShiftConstant * valueBound * inserts +
            2 * valueShiftConstant * logarithm * changes := by
        let remainder :=
          2 * insertShiftConstant * valueBound * inserts +
            2 * valueShiftConstant * logarithm * changes
        have extended :=
          Nat.add_le_add_right decayCharge remainder
        simpa [remainder, Nat.add_assoc] using extended
      _ =
          activity + inserts +
            2 * insertShiftConstant * valueBound * inserts +
            2 * valueShiftConstant * logarithm * changes := by
        rfl
  have absorbed :
      activity ≤
        inserts +
          2 * insertShiftConstant * valueBound * inserts +
          2 * valueShiftConstant * logarithm * changes := by
    apply Nat.le_of_add_le_add_left
      (a := activity)
    simpa [two_mul, Nat.add_assoc] using doubled
  have one_le_valueBound : 1 ≤ valueBound := by
    have ge_two := params.valueBound_ge_two
    dsimp [valueBound]
    omega
  change
    activity ≤
      (2 * insertShiftConstant + 1) * valueBound * inserts +
        (2 * valueShiftConstant + 1) * logarithm * changes
  calc
    activity ≤
        inserts +
          2 * insertShiftConstant * valueBound * inserts +
          2 * valueShiftConstant * logarithm * changes :=
      absorbed
    _ ≤
        (2 * insertShiftConstant + 1) * valueBound * inserts +
          (2 * valueShiftConstant + 1) * logarithm * changes := by
      have insert_unit : inserts ≤ valueBound * inserts := by
        simpa using Nat.mul_le_mul_right inserts one_le_valueBound
      calc
        inserts +
              2 * insertShiftConstant * valueBound * inserts +
              2 * valueShiftConstant * logarithm * changes ≤
            valueBound * inserts +
              2 * insertShiftConstant * valueBound * inserts +
              2 * valueShiftConstant * logarithm * changes := by
          let remainder :=
            2 * insertShiftConstant * valueBound * inserts +
              2 * valueShiftConstant * logarithm * changes
          have extended :=
            Nat.add_le_add_right insert_unit remainder
          simpa [remainder, Nat.add_assoc] using extended
        _ ≤
            (2 * insertShiftConstant + 1) * valueBound * inserts +
              (2 * valueShiftConstant + 1) * logarithm * changes := by
          have insert_expand :
              (2 * insertShiftConstant + 1) * valueBound * inserts =
                2 * insertShiftConstant * valueBound * inserts +
                  valueBound * inserts := by
            ring
          have value_expand :
              (2 * valueShiftConstant + 1) * logarithm * changes =
                2 * valueShiftConstant * logarithm * changes +
                  logarithm * changes := by
            ring
          rw [insert_expand, value_expand]
          omega

end Splay.Interface
