import Splay.Interface.PassCountHistory
import Splay.Interface.Potential
import FirstWinBinary
import Mathlib.Tactic

namespace Splay.Research.BinaryMemorylessPotential
open Splay.Interface

/-- Native binary-cap potential.  `price` ranges from 5 to 9; insertion costs
`9-price`.  Low-valued residents have credit 9,8,7 in the first three
pre-pass states and zero thereafter. -/
def weight (price passes value : ℕ) : ℕ :=
  if value = 1 then (if passes ≤ 2 then 9 - passes else 0)
  else 9 - price + (if passes ≤ 2 then 0 else 1)

def blockWeight {n : ℕ} (price : ℕ) (value : Element n → ℕ)
    (block : Block n) : ℕ :=
  (block.elements.map fun x => weight price block.passCount (value x)).sum

def blocksWeight {n : ℕ} (price : ℕ) (value : Element n → ℕ)
    (blocks : List (Block n)) : ℕ :=
  (blocks.map (blockWeight price value)).sum

def potential {n : ℕ} (price : ℕ) (state : State n) : ℕ :=
  blocksWeight price state.value state.blocks

def lowCount {n : ℕ} (value : Element n → ℕ)
    (elements : List (Element n)) : ℕ :=
  (elements.map fun x => if value x = 1 then 1 else 0).sum

private theorem sum_erase_add {α : Type*} [DecidableEq α]
    (f : α → ℕ) (xs : List α) (x : α) (member : x ∈ xs) :
    ((xs.erase x).map f).sum + f x = (xs.map f).sum := by
  have balance := ((List.perm_cons_erase member).map f).sum_eq
  simp only [List.map_cons, List.sum_cons] at balance
  omega

private theorem sum_eraseMany_add {α : Type*} [DecidableEq α]
    (f : α → ℕ) (xs removals : List α)
    (distinct : removals.Nodup)
    (present : ∀ x ∈ removals, x ∈ xs) :
    ((removals.foldl (fun current x => current.erase x) xs).map f).sum +
        (removals.map f).sum = (xs.map f).sum := by
  induction removals generalizing xs with
  | nil => simp
  | cons x removals ih =>
    obtain ⟨fresh, distinct⟩ := List.nodup_cons.mp distinct
    have member := present x (by simp)
    have rest : ∀ y ∈ removals, y ∈ xs.erase x := by
      intro y hy
      have different : y ≠ x := by
        intro same
        subst y
        exact fresh hy
      exact (List.mem_erase_of_ne different).2 (present y (by simp [hy]))
    have tailBalance := ih (xs.erase x) distinct rest
    have headBalance := sum_erase_add f xs x member
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    omega

private theorem lowCount_le_length {n : ℕ} (value : Element n → ℕ)
    (xs : List (Element n)) : lowCount value xs ≤ xs.length := by
  induction xs with
  | nil => simp [lowCount]
  | cons x xs ih =>
    simp only [lowCount, List.map_cons, List.sum_cons] at *
    simp only [List.length_cons]
    split_ifs <;> omega

private theorem lowCount_cons {n : ℕ} (value : Element n → ℕ)
    (x : Element n) (xs : List (Element n)) :
    lowCount value (x :: xs) = (if value x = 1 then 1 else 0) + lowCount value xs := by
  simp [lowCount]

private theorem weighted_count {n : ℕ} (price passes : ℕ)
    (value : Element n → ℕ) (xs : List (Element n)) :
    (xs.map fun x => weight price passes (value x)).sum =
      weight price passes 1 * lowCount value xs +
        weight price passes 2 * (xs.length - lowCount value xs) := by
  induction xs with
  | nil => simp [lowCount]
  | cons x xs ih =>
    have bound := lowCount_le_length value xs
    simp only [List.map_cons, List.sum_cons, List.length_cons, lowCount_cons]
    by_cases low : value x = 1
    · simp only [low, if_true]
      have sub : xs.length + 1 - (1 + lowCount value xs) =
          xs.length - lowCount value xs := by omega
      rw [sub, ih]
      ring
    · have same : weight price passes (value x) = weight price passes 2 := by
        simp [weight, low]
      simp only [low, if_false, zero_add]
      have sub : xs.length + 1 - lowCount value xs =
          xs.length - lowCount value xs + 1 := by omega
      rw [same, sub, ih]
      ring

private theorem winners_sublist {n : ℕ} (matching : List (Pairing n)) :
    (matching.map Pairing.winner).Sublist
      (matching.flatMap fun pairing => [pairing.winner, pairing.loser]) := by
  induction matching with
  | nil => exact .slnil
  | cons p ps ih => exact (ih.cons p.loser).cons_cons p.winner

private theorem binary_endpoints {n : ℕ} {params : Parameters}
    {state : State n} {sourceId : BlockId} {source : Block n}
    {matching : List (Pairing n)}
    (validState : state.Valid params) (binary : params.valueBound = 2)
    (valid : MatchingValid params state sourceId source matching)
    {pairing : Pairing n} (member : pairing ∈ matching) :
    state.value pairing.winner = 1 ∧ state.value pairing.loser = 2 := by
  have order := (valid.2.2.2.1 pairing member).2.1
  have winnerBounds := validState.2.1 pairing.winner
  have loserBounds := validState.2.1 pairing.loser
  omega

private theorem source_counts {n : ℕ} {params : Parameters}
    {state : State n} {sourceId : BlockId} {source : Block n}
    {matching : List (Pairing n)}
    (validState : state.Valid params) (binary : params.valueBound = 2)
    (valid : MatchingValid params state sourceId source matching) :
    (removeLosers source.elements matching).length + matching.length =
        source.elements.length ∧
    lowCount state.value (removeLosers source.elements matching) =
        lowCount state.value source.elements ∧
    matching.length ≤ lowCount state.value source.elements := by
  have losersDistinct := pairingLosers_nodup valid.2.1
  have losersPresent : ∀ x ∈ pairingLosers matching, x ∈ source.elements := by
    intro x hx
    obtain ⟨pairing, member, rfl⟩ := List.mem_map.mp hx
    exact valid.loser_mem member
  have lengths := length_foldl_erase_add source.elements
    (pairingLosers matching) losersDistinct losersPresent
  rw [← removeLosers_eq_foldl] at lengths
  have lowBalance := sum_eraseMany_add
    (fun x => if state.value x = 1 then 1 else 0) source.elements
    (pairingLosers matching) losersDistinct losersPresent
  rw [← removeLosers_eq_foldl] at lowBalance
  have lowLosers : ((pairingLosers matching).map
      fun x => if state.value x = 1 then 1 else 0).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨loser, loserMember, rfl⟩ := List.mem_map.mp hx
    obtain ⟨pairing, pairingMember, rfl⟩ := List.mem_map.mp loserMember
    simp [(binary_endpoints validState binary valid pairingMember).2]
  have winnersDistinct := (winners_sublist matching).nodup valid.2.1
  have winnersPresent : ∀ x ∈ matching.map Pairing.winner,
      x ∈ source.elements := by
    intro x hx
    obtain ⟨pairing, member, rfl⟩ := List.mem_map.mp hx
    exact (valid.2.2.2.1 pairing member).1.first_mem
  have winnerBalance := sum_eraseMany_add
    (fun x => if state.value x = 1 then 1 else 0) source.elements
    (matching.map Pairing.winner) winnersDistinct winnersPresent
  have lowWinners : ((matching.map Pairing.winner).map
      fun x => if state.value x = 1 then 1 else 0).sum = matching.length := by
    rw [List.map_map]
    have mapped : matching.map (fun p =>
        if state.value p.winner = 1 then 1 else 0) = matching.map (fun _ => 1) := by
      apply List.map_congr_left
      intro p hp
      simp [(binary_endpoints validState binary valid hp).1]
    change (matching.map (fun p => if state.value p.winner = 1 then 1 else 0)).sum = _
    rw [mapped]
    simp
  rw [lowLosers] at lowBalance
  rw [lowWinners] at winnerBalance
  refine ⟨?_, ?_, ?_⟩
  · simpa [pairingLosers] using lengths
  · simpa [lowCount] using lowBalance
  · unfold lowCount
    omega

/-- The complete source calculation, including the transition at pass 2. -/
theorem source_pass_bound {n : ℕ} {params : Parameters}
    {state : State n} {sourceId : BlockId} {source : Block n}
    {matching : List (Pairing n)} {price : ℕ}
    (_priceLower : 5 ≤ price) (_priceUpper : price ≤ 9)
    (validState : state.Valid params) (binary : params.valueBound = 2)
    (exempt : params.exemptPasses = 2)
    (numerator : params.matchingNumerator = 1)
    (denominator : params.matchingDenominator = 8)
    (valid : MatchingValid params state sourceId source matching) :
    matching.length + (9-price) * matching.length +
      blockWeight price state.value
        { source with
          passCount := source.passCount + 1
          elements := removeLosers source.elements matching } ≤
      blockWeight price state.value source := by
  obtain ⟨lengths, lows, winners⟩ := source_counts validState binary valid
  have countBound := lowCount_le_length state.value source.elements
  have afterCount := lowCount_le_length state.value
    (removeLosers source.elements matching)
  rw [lows] at afterCount
  unfold blockWeight
  rw [weighted_count, weighted_count, lows]
  by_cases early : source.passCount < 2
  · have beforeEarly : source.passCount ≤ 2 := by omega
    have afterEarly : source.passCount + 1 ≤ 2 := by omega
    simp only [weight, beforeEarly, afterEarly, if_true, Nat.reduceEqDiff,
      if_false, Nat.add_zero]
    have subBefore : 9 - source.passCount = 9 - (source.passCount + 1) + 1 := by omega
    rw [subBefore]
    have populations : source.elements.length - lowCount state.value source.elements =
        (removeLosers source.elements matching).length -
          lowCount state.value source.elements + matching.length := by omega
    rw [populations]
    nlinarith
  · by_cases transition : source.passCount = 2
    · have dense : source.elements.length ≤ 8 * matching.length := by
        rcases valid.2.2.2.2 with exempted | dense
        · omega
        · simpa [numerator, denominator] using dense
      simp only [transition, weight]
      norm_num
      have populations : source.elements.length - lowCount state.value source.elements =
          (removeLosers source.elements matching).length -
            lowCount state.value source.elements + matching.length := by omega
      have residualBound : matching.length +
          ((removeLosers source.elements matching).length -
            lowCount state.value source.elements) ≤
          7 * lowCount state.value source.elements := by omega
      rw [populations]
      nlinarith only [residualBound]
    · have beforeLate : ¬source.passCount ≤ 2 := by omega
      have afterLate : ¬source.passCount + 1 ≤ 2 := by omega
      simp only [weight, beforeLate, afterLate, if_false, Nat.reduceEqDiff,
        if_true, Nat.zero_mul, Nat.zero_add]
      have populations : source.elements.length - lowCount state.value source.elements =
          (removeLosers source.elements matching).length -
            lowCount state.value source.elements + matching.length := by omega
      rw [populations]
      nlinarith



private theorem weight_change_bound {price : ℕ}
    (lower : 5 ≤ price) (upper : price ≤ 9)
    (passes oldValue newValue : ℕ) :
    weight price passes newValue ≤ weight price passes oldValue + price := by
  unfold weight
  split_ifs <;> omega

private theorem sum_change_bound {α : Type*} [DecidableEq α]
    (oldWeight newWeight : α → ℕ) (xs : List α) (target : α) (price : ℕ)
    (same : ∀ x, x ≠ target → newWeight x = oldWeight x)
    (changed : newWeight target ≤ oldWeight target + price) :
    (xs.map newWeight).sum ≤ (xs.map oldWeight).sum + price * xs.count target := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases equal : x = target
    · subst x
      simp only [List.map_cons, List.sum_cons, List.count_cons, beq_self_eq_true,
        if_true]
      nlinarith
    · simp only [List.map_cons, List.sum_cons]
      rw [same x equal]
      simp only [List.count_cons, beq_iff_eq, equal, if_false, Nat.add_zero]
      omega

private theorem weight_decrease_bound {price : ℕ}
    (lower : 5 ≤ price) (upper : price ≤ 9) (passes : ℕ) :
    weight price passes 1 ≤ weight price passes 2 + price := by
  unfold weight
  split_ifs <;> omega

private theorem weight_increase_bound {price : ℕ}
    (lower : 5 ≤ price) (upper : price ≤ 9) (passes : ℕ) :
    weight price passes 2 ≤ weight price passes 1 + (10-price) := by
  unfold weight
  split_ifs <;> omega

private theorem blocks_change_bound {n : ℕ} (price cost : ℕ)
    (oldValue : Element n → ℕ) (target : Element n) (newValue : ℕ)
    (change : ∀ passes, weight price passes newValue ≤
      weight price passes (oldValue target) + cost)
    (blocks : List (Block n)) :
    blocksWeight price (Function.update oldValue target newValue) blocks ≤
      blocksWeight price oldValue blocks +
        cost * (blocks.flatMap Block.elements).count target := by
  induction blocks with
  | nil => simp [blocksWeight]
  | cons block blocks ih =>
    have first := sum_change_bound
      (fun x => weight price block.passCount (oldValue x))
      (fun x => weight price block.passCount
        (Function.update oldValue target newValue x))
      block.elements target cost
      (by intro x different; simp [Function.update_of_ne different])
      (by simpa using change block.passCount)
    change blockWeight price (Function.update oldValue target newValue) block ≤
      blockWeight price oldValue block + cost * block.elements.count target at first
    simp only [blocksWeight, List.map_cons, List.sum_cons] at ih ⊢
    simp only [List.flatMap_cons, List.count_append]
    nlinarith

private theorem state_change_bound {n : ℕ} {params : Parameters}
    (price cost : ℕ) (state : State n) (valid : state.Valid params)
    (target : Element n) (newValue : ℕ)
    (change : ∀ passes, weight price passes newValue ≤
      weight price passes (state.value target) + cost) :
    blocksWeight price (Function.update state.value target newValue) state.blocks ≤
      potential price state + cost := by
  have bound := blocks_change_bound price cost state.value target newValue change state.blocks
  have countBound := List.nodup_iff_count_le_one.mp valid.1 target
  change (state.blocks.flatMap Block.elements).count target ≤ 1 at countBound
  unfold potential
  nlinarith

private def destinationZero {n : ℕ} (blocks : List (Block n))
    (pairing : Pairing n) : Prop :=
  ∃ block, blocks[pairing.destination]? = some block ∧ block.passCount = 0

private theorem destinationZero_prepend {n : ℕ}
    {blocks : List (Block n)} {pairing : Pairing n}
    (zero : destinationZero blocks pairing) (index : ℕ) (x : Element n) :
    destinationZero (blocks.modify index fun b => {b with elements := x :: b.elements})
      pairing := by
  obtain ⟨block, found, count⟩ := zero
  unfold destinationZero
  by_cases equal : index = pairing.destination
  · refine ⟨{block with elements := x :: block.elements}, ?_, count⟩
    simp [equal, found]
  · refine ⟨block, ?_, count⟩
    simp [equal, found]

private theorem destinations_weight {n : ℕ} (price : ℕ)
    (value : Element n → ℕ) (blocks : List (Block n))
    (matching : List (Pairing n))
    (zeros : ∀ pairing ∈ matching, destinationZero blocks pairing)
    (losersHigh : ∀ pairing ∈ matching, value pairing.loser = 2) :
    blocksWeight price value (insertAtDestinations blocks matching) =
      blocksWeight price value blocks + (9-price) * matching.length := by
  induction matching generalizing blocks with
  | nil => simp [insertAtDestinations]
  | cons pairing matching ih =>
    obtain ⟨block, found, count⟩ := zeros pairing (by simp)
    let updated := blocks.modify pairing.destination
      fun b => {b with elements := pairing.loser :: b.elements}
    have balance := list_sum_map_modify_add (blockWeight price value) blocks
      pairing.destination block found
      (fun b => {b with elements := pairing.loser :: b.elements})
    have one : blocksWeight price value updated =
        blocksWeight price value blocks + (9-price) := by
      simp only [blockWeight, List.map_cons, List.sum_cons] at balance
      have high := losersHigh pairing (by simp)
      simp only [count, high, weight, Nat.reduceEqDiff, if_false,
        Nat.zero_le, if_true, Nat.add_zero] at balance
      change _ = _ at balance
      unfold blocksWeight updated
      omega
    have restZeros : ∀ p ∈ matching, destinationZero updated p := by
      intro p hp
      exact destinationZero_prepend (zeros p (by simp [hp]))
        pairing.destination pairing.loser
    have restHigh : ∀ p ∈ matching, value p.loser = 2 := by
      intro p hp
      exact losersHigh p (by simp [hp])
    have tailBalance := ih updated restZeros restHigh
    change blocksWeight price value (insertAtDestinations updated matching) = _
    rw [tailBalance, one]
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

private theorem growingZero_step {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    (zero : GrowingPassCountZero before) (step : Step params before operation after) :
    GrowingPassCountZero after := by
  have single : Trace params before [operation] after := .cons step (.nil step.2.2)
  obtain ⟨labels, history⟩ := HistoryTrace.lift single []
  exact history.preserveGrowingPassCountZero zero



/-- Every native operation obeys the potential inequality. -/
theorem step_bound {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n} {price : ℕ}
    (priceLower : 5 ≤ price) (priceUpper : price ≤ 9)
    (binary : params.valueBound = 2) (exempt : params.exemptPasses = 2)
    (numerator : params.matchingNumerator = 1)
    (denominator : params.matchingDenominator = 8)
    (zero : GrowingPassCountZero before)
    (step : Step params before operation after) :
    operation.activity + potential price after ≤
      potential price before + (9-price) * operation.insertCount +
        price * operation.decreaseCount + (10-price) * operation.increaseCount := by
  have validBefore := step.1
  cases step.2.1 with
  | convert found growing blocks_eq values_eq =>
    rename_i blockId block
    have balance := list_sum_map_modify_add (blockWeight price before.value)
      before.blocks blockId block found (fun b => {b with mode := .shrinking})
    have unchanged : blockWeight price before.value {block with mode := .shrinking} =
        blockWeight price before.value block := rfl
    rw [unchanged] at balance
    simp only [Operation.activity, Operation.insertCount, Operation.decreaseCount, Operation.increaseCount,
      Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    unfold potential blocksWeight
    rw [blocks_eq, values_eq]
    omega
  | create room blocks_eq values_eq =>
    simp [Operation.activity, Operation.insertCount, Operation.decreaseCount, Operation.increaseCount,
      potential, blocksWeight, blockWeight, blocks_eq, values_eq]
  | insert found growing unassigned order blocks_eq values_eq =>
    rename_i blockId block element
    have count := zero blockId block found growing
    have entrant : before.value element = 2 := by
      have creatorBounds := validBefore.2.1 block.creator
      have elementBounds := validBefore.2.1 element
      omega
    have balance := list_sum_map_modify_add (blockWeight price before.value)
      before.blocks blockId block found
      (fun b => {b with elements := element :: b.elements})
    simp only [blockWeight, List.map_cons, List.sum_cons] at balance
    simp only [count, entrant, weight, Nat.reduceEqDiff, if_false,
      Nat.zero_le, if_true, Nat.add_zero] at balance
    simp only [Operation.activity, Operation.insertCount, Operation.decreaseCount, Operation.increaseCount,
      Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add]
    unfold potential blocksWeight
    rw [blocks_eq, values_eq]
    omega
  | delete found shrinking present blocks_eq values_eq =>
    rename_i blockId block element
    have balance := list_sum_map_modify_add (blockWeight price before.value)
      before.blocks blockId block found
      (fun b => {b with elements := b.elements.erase element})
    have removed := sum_erase_add
      (fun x => weight price block.passCount (before.value x))
      block.elements element present
    change blockWeight price before.value {block with elements := block.elements.erase element} +
        weight price block.passCount (before.value element) =
      blockWeight price before.value block at removed
    simp only [Operation.activity, Operation.insertCount, Operation.decreaseCount, Operation.increaseCount,
      Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    unfold potential blocksWeight
    rw [blocks_eq, values_eq]
    omega
  | pass found matchingValid blocks_eq values_eq =>
    rename_i sourceId source matching
    let sourceUpdated := before.blocks.modify sourceId fun _ =>
      { source with
        passCount := source.passCount + 1
        elements := removeLosers source.elements matching }
    have balance := list_sum_map_modify_add (blockWeight price before.value)
      before.blocks sourceId source found
      (fun _ => { source with
        passCount := source.passCount + 1
        elements := removeLosers source.elements matching })
    have sourceBound := source_pass_bound priceLower priceUpper validBefore binary
      exempt numerator denominator matchingValid
    have destinations : ∀ pairing ∈ matching, destinationZero sourceUpdated pairing := by
      intro pairing member
      have pairValid := matchingValid.2.2.2.1 pairing member
      obtain ⟨destination, destinationFound, growing, _⟩ := pairValid.2.2.2
      refine ⟨destination, ?_, zero pairing.destination destination destinationFound growing⟩
      have different : sourceId ≠ pairing.destination := Ne.symm pairValid.2.2.1
      change before.blocks[pairing.destination]? = some destination at destinationFound
      simp [sourceUpdated, different, destinationFound]
    have highs : ∀ pairing ∈ matching, before.value pairing.loser = 2 := by
      intro pairing member
      exact (binary_endpoints validBefore binary matchingValid member).2
    have destinationBalance := destinations_weight price before.value sourceUpdated
      matching destinations highs
    change blocksWeight price before.value sourceUpdated +
        blockWeight price before.value source =
      blocksWeight price before.value before.blocks +
        blockWeight price before.value { source with
          passCount := source.passCount + 1
          elements := removeLosers source.elements matching } at balance
    simp only [Operation.activity, Operation.insertCount, Operation.decreaseCount, Operation.increaseCount,
      Nat.mul_zero, Nat.add_zero]
    unfold potential
    rw [blocks_eq, values_eq]
    change matching.length + blocksWeight price before.value
      (insertAtDestinations sourceUpdated matching) ≤ _
    rw [destinationBalance]
    omega
  | split found shrinking prefix_le blocks_eq values_eq =>
    rename_i sourceId source prefixLength
    have balance := list_sum_map_modify_add (blockWeight price before.value)
      before.blocks sourceId source found (fun b => {b with elements := []})
    have pieces :
        blockWeight price before.value {source with elements := source.elements.take prefixLength} +
        blockWeight price before.value {source with elements := source.elements.drop prefixLength} =
        blockWeight price before.value source := by
      unfold blockWeight
      rw [← List.sum_append, ← List.map_append, List.take_append_drop]
    have empty : blockWeight price before.value {source with elements := []} = 0 := rfl
    rw [empty] at balance
    simp only [Operation.activity, Operation.insertCount, Operation.decreaseCount, Operation.increaseCount,
      Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    unfold potential blocksWeight
    rw [blocks_eq, values_eq]
    simp only [splitBlocks, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    change _ + (blockWeight price before.value _ + blockWeight price before.value _) ≤ _
    rw [pieces]
    omega
  | decrease can_decrease blocks_eq values_eq =>
    rename_i element
    have old : before.value element = 2 := by
      have bounds := validBefore.2.1 element
      omega
    have bound := state_change_bound price price before validBefore
      element (before.value element - 1) (by
        intro passes
        simpa [old] using weight_decrease_bound priceLower priceUpper passes)
    simpa [Operation.activity, Operation.insertCount, Operation.decreaseCount, Operation.increaseCount,
      potential, blocks_eq, values_eq] using bound
  | increase can_increase blocks_eq values_eq =>
    rename_i element
    have old : before.value element = 1 := by
      have bounds := validBefore.2.1 element
      omega
    have bound := state_change_bound price (10-price) before validBefore
      element (before.value element + 1) (by
        intro passes
        simpa [old] using weight_increase_bound priceLower priceUpper passes)
    simpa [Operation.activity, Operation.insertCount, Operation.decreaseCount, Operation.increaseCount,
      potential, blocks_eq, values_eq] using bound

/-- Potential telescoping over the native trace relation. -/
theorem trace_bound {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)} {price : ℕ}
    (priceLower : 5 ≤ price) (priceUpper : price ≤ 9)
    (binary : params.valueBound = 2) (exempt : params.exemptPasses = 2)
    (numerator : params.matchingNumerator = 1)
    (denominator : params.matchingDenominator = 8)
    (zero : GrowingPassCountZero initial)
    (trace : Trace params initial operations final) :
    totalActivity operations + potential price final ≤
      potential price initial + (9-price) * totalInserts operations +
        price * totalDecreases operations + (10-price) * totalIncreases operations := by
  induction trace with
  | nil valid => simp [totalActivity, totalInserts, totalDecreases, totalIncreases]
  | @cons before middle final operation operations head tail ih =>
    have first := step_bound priceLower priceUpper binary exempt numerator denominator zero head
    have rest := ih (growingZero_step zero head)
    simp only [totalActivity, totalInserts, totalDecreases, totalIncreases,
      List.map_cons, List.sum_cons] at rest ⊢
    nlinarith

/-- Sharp binary-cap upper bound, with no auxiliary history or certificate
hypothesis: the only execution premises are native `Initial` and `Trace`. -/
theorem from_initial_trace_directional {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)} {price : ℕ}
    (priceLower : 5 ≤ price) (priceUpper : price ≤ 9)
    (binary : params.valueBound = 2) (exempt : params.exemptPasses = 2)
    (numerator : params.matchingNumerator = 1)
    (denominator : params.matchingDenominator = 8)
    (initialState : initial.Initial params)
    (trace : Trace params initial operations final) :
    totalActivity operations ≤ (9-price) * totalInserts operations +
      price * totalDecreases operations + (10-price) * totalIncreases operations := by
  have zero : GrowingPassCountZero initial := by
    intro blockId block found
    simp [State.block?, initialState.2] at found
  have bound := trace_bound priceLower priceUpper binary exempt numerator denominator zero trace
  have initialPotential : potential price initial = 0 := by
    simp [potential, blocksWeight, initialState.2]
  rw [initialPotential] at bound
  omega



/-- The two sharp endpoint coefficients, and every integral point between. -/
theorem from_initial_trace {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)} {price : ℕ}
    (priceLower : 5 ≤ price) (priceUpper : price ≤ 9)
    (binary : params.valueBound = 2) (exempt : params.exemptPasses = 2)
    (numerator : params.matchingNumerator = 1)
    (denominator : params.matchingDenominator = 8)
    (initialState : initial.Initial params)
    (trace : Trace params initial operations final) :
    totalActivity operations ≤ (9-price) * totalInserts operations +
      price * totalValueChanges operations := by
  have bound := from_initial_trace_directional priceLower priceUpper binary exempt
    numerator denominator initialState trace
  rw [totalValueChanges_eq]
  have larger : 10-price ≤ price := by omega
  nlinarith

/-- All real coefficients in the sharp binary region, now from native traces. -/
theorem coefficient_region_upper {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)} {a b : ℝ}
    (aNonnegative : 0 ≤ a) (bLower : 5 ≤ b) (sumLower : 9 ≤ a+b)
    (binary : params.valueBound = 2) (exempt : params.exemptPasses = 2)
    (numerator : params.matchingNumerator = 1)
    (denominator : params.matchingDenominator = 8)
    (initialState : initial.Initial params)
    (trace : Trace params initial operations final) :
    (totalActivity operations : ℝ) ≤ a * totalInserts operations +
      b * totalValueChanges operations := by
  have sharp := from_initial_trace (price := 5) (by omega) (by omega)
    binary exempt numerator denominator initialState trace
  have zero := from_initial_trace (price := 9) (by omega) (by omega)
    binary exempt numerator denominator initialState trace
  norm_num at sharp zero
  have sharpReal : (totalActivity operations : ℝ) ≤
      4 * totalInserts operations + 5 * totalValueChanges operations := by exact_mod_cast sharp
  have zeroReal : (totalActivity operations : ℝ) ≤
      9 * totalValueChanges operations := by exact_mod_cast zero
  exact FirstWinBinary.coefficient_region_upper (by positivity) (by positivity)
    zeroReal sharpReal aNonnegative bLower sumLower

/-- Compiler traces start with every global value one.  In that subclass
five times total variation pays all activity with zero insertion charge. -/
theorem all_ones_bound {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (binary : params.valueBound = 2) (exempt : params.exemptPasses = 2)
    (numerator : params.matchingNumerator = 1)
    (denominator : params.matchingDenominator = 8)
    (initialState : initial.Initial params)
    (allOnes : ∀ x, initial.value x = 1)
    (trace : Trace params initial operations final) :
    totalActivity operations ≤ 5 * totalValueChanges operations := by
  have bound := from_initial_trace_directional (price := 9) (by omega) (by omega)
    binary exempt numerator denominator initialState trace
  have finalValid : final.Valid params := by
    clear bound allOnes initialState
    induction trace with
    | nil valid => exact valid
    | cons head tail ih => exact ih
  have valueMonotone : initial.totalValue ≤ final.totalValue := by
    apply Finset.sum_le_sum
    intro x hx
    rw [allOnes]
    exact (finalValid.2.1 x).1
  have balance := trace.totalValue_balance
  rw [totalValueChanges_eq]
  norm_num at bound
  omega

#print axioms source_pass_bound
#print axioms step_bound
#print axioms from_initial_trace
#print axioms coefficient_region_upper
#print axioms all_ones_bound
end Splay.Research.BinaryMemorylessPotential
