import Splay.Interface.Decay
import Splay.Interface.JoinHistory
import Mathlib.Tactic

namespace Splay.Interface

/--
Changing one found list entry gives an exact additive balance for any natural
weight.  This avoids truncated subtraction in all block-potential updates.
-/
theorem list_sum_map_modify_add
    {α : Type*} (weight : α → ℕ) (items : List α)
    (index : ℕ) (item : α)
    (found : items[index]? = some item)
    (update : α → α) :
    ((items.modify index update).map weight).sum + weight item =
      (items.map weight).sum + weight (update item) := by
  induction items generalizing index with
  | nil =>
      simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst item
          simp [List.modify_eq_take_drop]
          omega
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          have tailBalance := ih index found
          have extended := congrArg (weight head + ·) tailBalance
          simpa [List.modify_eq_take_drop, Nat.add_assoc] using extended

namespace Block

/-- Number of elements contributing to the growing-block population. -/
def growingWeight {n : ℕ} (block : Block n) : ℕ :=
  if block.mode = .growing then block.elements.length else 0

end Block

/-- Total number of elements currently residing in growing blocks. -/
def growingMassBlocks {n : ℕ} (blocks : List (Block n)) : ℕ :=
  (blocks.map Block.growingWeight).sum

namespace State

def growingMass {n : ℕ} (state : State n) : ℕ :=
  growingMassBlocks state.blocks

end State

/-- Prepending an element changes no block-mode label. -/
theorem map_mode_modify_prepend {n : ℕ}
    (blocks : List (Block n)) (destination : BlockId)
    (element : Element n) :
    (blocks.modify destination fun block =>
        { block with elements := element :: block.elements }).map
          Block.mode =
      blocks.map Block.mode := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map, List.getElem?_modify]
  cases found : blocks[index]? with
  | none =>
      simp
  | some block =>
      by_cases same : destination = index
      · simp [same]
      · simp [same]

/-- Updating only pass metadata and contents likewise preserves all modes. -/
theorem map_mode_modify_passSource {n : ℕ}
    (blocks : List (Block n)) (sourceId : BlockId)
    (source : Block n) (matching : List (Pairing n))
    (sourceFound : blocks[sourceId]? = some source) :
    (blocks.modify sourceId fun _ =>
        { source with
          passCount := source.passCount + 1
          elements := removeLosers source.elements matching }).map
          Block.mode =
      blocks.map Block.mode := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map, List.getElem?_modify]
  by_cases same : sourceId = index
  · subst index
    simp [sourceFound]
  · cases found : blocks[index]? <;>
      simp [same]

/-- A total predicate saying that a destination lookup exists and is growing. -/
def destinationGrowing {n : ℕ}
    (blocks : List (Block n)) (pairing : Pairing n) : Prop :=
  ∃ destination,
    blocks[pairing.destination]? = some destination ∧
      destination.mode = .growing

/-- Prepending elsewhere preserves the growing status of every destination. -/
theorem destinationGrowing_modify_prepend {n : ℕ}
    {blocks : List (Block n)} {pairing : Pairing n}
    (growing : destinationGrowing blocks pairing)
    (modifiedDestination : BlockId) (element : Element n) :
    destinationGrowing
      (blocks.modify modifiedDestination fun block =>
        { block with elements := element :: block.elements })
      pairing := by
  obtain ⟨destination, found, destination_mode⟩ := growing
  let modified :=
    blocks.modify modifiedDestination fun block =>
      { block with elements := element :: block.elements }
  have mode_lookup :
      ((modified.map Block.mode)[pairing.destination]?) =
        some destination.mode := by
    rw [map_mode_modify_prepend]
    simpa using congrArg (Option.map Block.mode) found
  rw [List.getElem?_map] at mode_lookup
  cases modified_found : modified[pairing.destination]? with
  | none =>
      simp [modified_found] at mode_lookup
  | some modifiedBlock =>
      refine ⟨modifiedBlock, modified_found, ?_⟩
      simp [modified_found] at mode_lookup
      exact mode_lookup.trans destination_mode

/-- Prepending to one known growing block increases growing mass by one. -/
theorem growingMassBlocks_modify_prepend
    {n : ℕ} {blocks : List (Block n)}
    {destinationId : BlockId} {destination : Block n}
    (found : blocks[destinationId]? = some destination)
    (growing : destination.mode = .growing)
    (element : Element n) :
    growingMassBlocks
        (blocks.modify destinationId fun block =>
          { block with elements := element :: block.elements }) =
      growingMassBlocks blocks + 1 := by
  have balance :=
    list_sum_map_modify_add Block.growingWeight blocks destinationId
      destination found
      (fun block =>
        { block with elements := element :: block.elements })
  unfold growingMassBlocks at balance ⊢
  simp [Block.growingWeight, growing] at balance
  omega

/--
Each pass loser is prepended to a growing destination, so destination updates
increase growing mass exactly by matching length.
-/
theorem growingMassBlocks_insertAtDestinations
    {n : ℕ} (blocks : List (Block n))
    (matching : List (Pairing n))
    (destinationsGrowing :
      ∀ pairing ∈ matching, destinationGrowing blocks pairing) :
    growingMassBlocks (insertAtDestinations blocks matching) =
      growingMassBlocks blocks + matching.length := by
  induction matching generalizing blocks with
  | nil =>
      simp [insertAtDestinations]
  | cons pairing matching ih =>
      obtain ⟨destination, found, growing⟩ :=
        destinationsGrowing pairing (by simp)
      let modified :=
        blocks.modify pairing.destination fun block =>
          { block with elements := pairing.loser :: block.elements }
      have head_mass :
          growingMassBlocks modified =
            growingMassBlocks blocks + 1 :=
        growingMassBlocks_modify_prepend found growing pairing.loser
      have tail_destinations :
          ∀ later ∈ matching, destinationGrowing modified later := by
        intro later later_mem
        exact destinationGrowing_modify_prepend
          (destinationsGrowing later (by simp [later_mem]))
          pairing.destination pairing.loser
      have tail_mass := ih modified tail_destinations
      change
        growingMassBlocks
            (insertAtDestinations modified matching) =
          growingMassBlocks blocks + (matching.length + 1)
      rw [tail_mass, head_mass]
      omega

/-- Size removed from the growing population by one conversion operation. -/
def operationConversionMass {n : ℕ}
    (before : State n) : Operation n → ℕ
  | .convert blockId =>
      (before.block? blockId).map (fun block => block.elements.length)
        |>.getD 0
  | _ => 0

/--
Exact one-step potential balance:

* insert and pass activity add entries to growing blocks;
* convert cashes out the complete growing population of its block;
* every other operation preserves the potential.
-/
theorem Effect.growingMass_balance
    {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    (effect : Effect params before operation after) :
    after.growingMass + operationConversionMass before operation =
      before.growingMass + operation.insertCount + operation.activity := by
  cases effect with
  | convert found growing blocks_eq values_eq =>
      rename_i blockId block
      change before.blocks[blockId]? = some block at found
      have balance :=
        list_sum_map_modify_add Block.growingWeight before.blocks blockId
          block found
          (fun current => { current with mode := .shrinking })
      unfold State.growingMass growingMassBlocks at ⊢
      simp [blocks_eq, operationConversionMass, State.block?, found,
        Block.growingWeight, growing, Operation.insertCount,
        Operation.activity] at balance ⊢
      omega
  | create room blocks_eq values_eq =>
      simp [State.growingMass, growingMassBlocks, blocks_eq,
        operationConversionMass, Block.growingWeight,
        Operation.insertCount, Operation.activity]
  | insert found growing unassigned value_order blocks_eq values_eq =>
      rename_i blockId block element
      have mass_step :=
        growingMassBlocks_modify_prepend found growing element
      simpa [State.growingMass, blocks_eq, operationConversionMass,
        Operation.insertCount, Operation.activity] using mass_step
  | delete found shrinking present blocks_eq values_eq =>
      rename_i blockId block element
      have balance :=
        list_sum_map_modify_add Block.growingWeight before.blocks blockId
          block found
          (fun current =>
            { current with elements := current.elements.erase element })
      unfold State.growingMass growingMassBlocks at ⊢
      simp [blocks_eq, operationConversionMass, Block.growingWeight,
        shrinking, Operation.insertCount, Operation.activity] at balance ⊢
      exact balance
  | pass found valid_matching blocks_eq values_eq =>
      rename_i sourceId source matching
      let sourceUpdated :=
        before.blocks.modify sourceId fun _ =>
          { source with
            passCount := source.passCount + 1
            elements := removeLosers source.elements matching }
      have source_balance :=
        list_sum_map_modify_add Block.growingWeight before.blocks sourceId
          source found
          (fun _ =>
            { source with
              passCount := source.passCount + 1
              elements := removeLosers source.elements matching })
      have source_mass :
          growingMassBlocks sourceUpdated =
            growingMassBlocks before.blocks := by
        have source_weight :
            Block.growingWeight source = 0 := by
          simp [Block.growingWeight, valid_matching.1]
        have updated_weight :
            Block.growingWeight
              { source with
                passCount := source.passCount + 1
                elements := removeLosers source.elements matching } = 0 := by
          simp [Block.growingWeight, valid_matching.1]
        unfold sourceUpdated growingMassBlocks
        rw [source_weight, updated_weight] at source_balance
        omega
      have modes_eq :
          sourceUpdated.map Block.mode =
            before.blocks.map Block.mode :=
        map_mode_modify_passSource before.blocks sourceId source matching
          found
      have destinations :
          ∀ pairing ∈ matching,
            destinationGrowing sourceUpdated pairing := by
        intro pairing pairing_mem
        obtain ⟨destination, destination_found, destination_growing,
            _creator⟩ :=
          (valid_matching.2.2.2.1 pairing pairing_mem).2.2.2
        change
          before.blocks[pairing.destination]? = some destination
          at destination_found
        have mode_lookup :
            ((sourceUpdated.map Block.mode)[pairing.destination]?) =
              some destination.mode := by
          rw [modes_eq]
          simpa using congrArg (Option.map Block.mode) destination_found
        rw [List.getElem?_map] at mode_lookup
        cases updated_found : sourceUpdated[pairing.destination]? with
        | none =>
            simp [updated_found] at mode_lookup
        | some updatedDestination =>
            refine ⟨updatedDestination, updated_found, ?_⟩
            have mode_eq :
                updatedDestination.mode = destination.mode := by
              simp [updated_found] at mode_lookup
              exact mode_lookup
            exact mode_eq.trans destination_growing
      have destination_mass :=
        growingMassBlocks_insertAtDestinations
          sourceUpdated matching destinations
      have after_mass :
          after.growingMass =
            growingMassBlocks
              (insertAtDestinations sourceUpdated matching) := by
        unfold State.growingMass
        rw [blocks_eq]
        rfl
      rw [after_mass]
      simp only [operationConversionMass, Operation.insertCount,
        Operation.activity]
      rw [destination_mass, source_mass]
      simp [State.growingMass]
  | split found shrinking prefix_le blocks_eq values_eq =>
      rename_i sourceId source prefixLength
      have emptied_balance :=
        list_sum_map_modify_add Block.growingWeight before.blocks sourceId
          source found
          (fun current => { current with elements := [] })
      unfold State.growingMass growingMassBlocks at ⊢
      simp [blocks_eq, splitBlocks, operationConversionMass,
        Block.growingWeight, shrinking, Operation.insertCount,
        Operation.activity] at emptied_balance ⊢
      exact emptied_balance
  | decrease can_decrease blocks_eq values_eq =>
      simp [State.growingMass, blocks_eq, operationConversionMass,
        Operation.insertCount, Operation.activity]
  | increase can_increase blocks_eq values_eq =>
      simp [State.growingMass, blocks_eq, operationConversionMass,
        Operation.insertCount, Operation.activity]

/--
The total population cashed out by conversions along a concrete trace.
The relation retains the pre-state needed to compute each conversion mass.
-/
inductive ConversionHistory {n : ℕ} (params : Parameters) :
    State n → List (Operation n) → State n → ℕ → Prop
  | nil {state : State n} (valid : state.Valid params) :
      ConversionHistory params state [] state 0
  | cons {before middle final : State n}
      {operation : Operation n} {operations : List (Operation n)}
      {tailMass : ℕ}
      (head : Step params before operation middle)
      (tail :
        ConversionHistory params middle operations final tailMass) :
      ConversionHistory params before (operation :: operations) final
        (operationConversionMass before operation + tailMass)

namespace ConversionHistory

theorem erase
    {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    {convertedMass : ℕ}
    (history :
      ConversionHistory params initial operations final convertedMass) :
    Trace params initial operations final := by
  induction history with
  | nil valid =>
      exact .nil valid
  | cons head tail ih =>
      exact .cons head ih

/-- Every ordinary trace has its deterministic conversion accounting. -/
theorem lift
    {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (trace : Trace params initial operations final) :
    ∃ convertedMass,
      ConversionHistory params initial operations final convertedMass := by
  induction trace with
  | nil valid =>
      exact ⟨0, .nil valid⟩
  | @cons before middle final operation operations head tail ih =>
      obtain ⟨tailMass, tailHistory⟩ := ih
      exact
        ⟨operationConversionMass before operation + tailMass,
          .cons head tailHistory⟩

/-- The one-step growing-population balance telescopes exactly. -/
theorem growingMass_balance
    {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    {convertedMass : ℕ}
    (history :
      ConversionHistory params initial operations final convertedMass) :
    final.growingMass + convertedMass =
      initial.growingMass +
        totalInserts operations + totalActivity operations := by
  induction history with
  | nil valid =>
      simp [totalInserts, totalActivity]
  | @cons before middle final operation operations tailMass head tail ih =>
      have headBalance := head.2.1.growingMass_balance
      simp only [totalInserts, totalActivity, List.map_cons,
        List.sum_cons]
      calc
        final.growingMass +
              (operationConversionMass before operation + tailMass) =
            (final.growingMass + tailMass) +
              operationConversionMass before operation := by
          omega
        _ =
            (middle.growingMass +
                totalInserts operations + totalActivity operations) +
              operationConversionMass before operation := by
          rw [ih]
        _ =
            (middle.growingMass +
                operationConversionMass before operation) +
              totalInserts operations + totalActivity operations := by
          omega
        _ =
            (before.growingMass + operation.insertCount +
                operation.activity) +
              totalInserts operations + totalActivity operations := by
          rw [headBalance]
        _ =
            before.growingMass +
                (operation.insertCount + totalInserts operations) +
              (operation.activity + totalActivity operations) := by
          omega

end ConversionHistory

/--
For a trace starting with no blocks, the sum of all root populations at
conversion is bounded by the exact block-entry budget `inserts + activity`.
-/
theorem Trace.exists_conversionMass_le_entries
    {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (initialState : initial.Initial params)
    (trace : Trace params initial operations final) :
    ∃ convertedMass,
      ConversionHistory params initial operations final convertedMass ∧
        convertedMass ≤
          totalInserts operations + totalActivity operations := by
  obtain ⟨convertedMass, history⟩ := ConversionHistory.lift trace
  have balance := history.growingMass_balance
  have initial_zero : initial.growingMass = 0 := by
    simp [State.growingMass, growingMassBlocks, initialState.2]
  rw [initial_zero, zero_add] at balance
  exact ⟨convertedMass, history, by omega⟩

/-- One root block and its exact population at the moment of conversion. -/
structure ConversionOccurrence where
  root : RootId
  block : BlockId
  convertedMass : ℕ
  deriving DecidableEq, Repr

/-- Deterministic root-labelled conversion annotation of one operation. -/
def operationConversionOccurrences {n : ℕ}
    (before : State n) (labels : RootLabels) :
    Operation n → List ConversionOccurrence
  | .convert blockId =>
      [{ root := (RootLabels.root? labels blockId).getD blockId
         block := blockId
         convertedMass :=
           (before.block? blockId).map
             (fun block => block.elements.length) |>.getD 0 }]
  | _ => []

@[simp]
theorem sum_operationConversionOccurrences
    {n : ℕ} (before : State n) (labels : RootLabels)
    (operation : Operation n) :
    (operationConversionOccurrences before labels operation |>.map
      ConversionOccurrence.convertedMass).sum =
        operationConversionMass before operation := by
  cases operation <;>
    simp [operationConversionOccurrences, operationConversionMass]

/-- Every annotated conversion uses successful block/root lookups and exact mass. -/
theorem conversion_spec_of_mem_operationConversionOccurrences
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n} {occurrence : ConversionOccurrence}
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    (member :
      occurrence ∈
        operationConversionOccurrences before labels operation) :
    ∃ block : Block n,
      operation = .convert occurrence.block ∧
        before.block? occurrence.block = some block ∧
        RootLabels.root? labels occurrence.block =
          some occurrence.root ∧
        block.mode = .growing ∧
        occurrence.convertedMass = block.elements.length := by
  cases operation with
  | convert blockId =>
      rcases step with ⟨_beforeValid, effect, _afterValid⟩
      cases effect with
      | convert found growing blocks_eq values_eq =>
          rename_i block
          obtain ⟨root, root_found⟩ :=
            root_exists_of_aligned_block_found aligned found
          simp only [operationConversionOccurrences,
            List.mem_singleton] at member
          subst occurrence
          simp [found, root_found]
          exact growing
  | create creator =>
      simp [operationConversionOccurrences] at member
  | insert blockId element =>
      simp [operationConversionOccurrences] at member
  | delete blockId element =>
      simp [operationConversionOccurrences] at member
  | pass blockId matching =>
      simp [operationConversionOccurrences] at member
  | split blockId prefixLength =>
      simp [operationConversionOccurrences] at member
  | valueChange element delta =>
      simp [operationConversionOccurrences] at member

/--
The complete chronological list of root conversions, synchronized with the
already deterministic lineage labels.
-/
inductive RootConversionHistory {n : ℕ} (params : Parameters) :
    State n → RootLabels → List (Operation n) →
      List ConversionOccurrence → State n → RootLabels → Prop
  | nil {state : State n} {labels : RootLabels}
      (valid : state.Valid params) :
      RootConversionHistory params state labels [] [] state labels
  | cons {before middle final : State n}
      {beforeLabels finalLabels : RootLabels}
      {operation : Operation n} {operations : List (Operation n)}
      {tailOccurrences : List ConversionOccurrence}
      (head : Step params before operation middle)
      (tail :
        RootConversionHistory params middle
          (RootLabels.after beforeLabels operation)
          operations tailOccurrences final finalLabels) :
      RootConversionHistory params before beforeLabels
        (operation :: operations)
        (operationConversionOccurrences before beforeLabels operation ++
          tailOccurrences)
        final finalLabels

namespace RootConversionHistory

theorem erase
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List ConversionOccurrence}
    (history :
      RootConversionHistory params initial initialLabels operations
        occurrences final finalLabels) :
    HistoryTrace params initial initialLabels operations
      final finalLabels := by
  induction history with
  | nil valid =>
      exact .nil valid
  | cons head tail ih =>
      exact .cons head ih

theorem lift
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    (history :
      HistoryTrace params initial initialLabels operations
        final finalLabels) :
    ∃ occurrences,
      RootConversionHistory params initial initialLabels operations
        occurrences final finalLabels := by
  induction history with
  | nil valid =>
      exact ⟨[], .nil valid⟩
  | @cons before middle final beforeLabels finalLabels operation operations
      head tail ih =>
      obtain ⟨tailOccurrences, annotatedTail⟩ := ih
      exact
        ⟨operationConversionOccurrences before beforeLabels operation ++
            tailOccurrences,
          .cons head annotatedTail⟩

/-- Root-labelled conversion masses satisfy the exact growing-mass balance. -/
theorem growingMass_balance
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List ConversionOccurrence}
    (history :
      RootConversionHistory params initial initialLabels operations
        occurrences final finalLabels) :
    final.growingMass +
        (occurrences.map ConversionOccurrence.convertedMass).sum =
      initial.growingMass +
        totalInserts operations + totalActivity operations := by
  induction history with
  | nil valid =>
      simp [totalInserts, totalActivity]
  | @cons before middle final beforeLabels finalLabels operation operations
      tailOccurrences head tail ih =>
      have headBalance := head.2.1.growingMass_balance
      simp only [List.map_append, List.sum_append,
        sum_operationConversionOccurrences, totalInserts, totalActivity,
        List.map_cons, List.sum_cons]
      calc
        final.growingMass +
              (operationConversionMass before operation +
                (tailOccurrences.map
                  ConversionOccurrence.convertedMass).sum) =
            (final.growingMass +
                (tailOccurrences.map
                  ConversionOccurrence.convertedMass).sum) +
              operationConversionMass before operation := by
          omega
        _ =
            (middle.growingMass +
                totalInserts operations + totalActivity operations) +
              operationConversionMass before operation := by
          rw [ih]
        _ =
            (middle.growingMass +
                operationConversionMass before operation) +
              totalInserts operations + totalActivity operations := by
          omega
        _ =
            (before.growingMass + operation.insertCount +
                operation.activity) +
              totalInserts operations + totalActivity operations := by
          rw [headBalance]
        _ =
            before.growingMass +
                (operation.insertCount + totalInserts operations) +
              (operation.activity + totalActivity operations) := by
          omega

/-- Every global root-conversion occurrence exposes its exact aligned step. -/
theorem occurrence_snapshot
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List ConversionOccurrence}
    (history :
      RootConversionHistory params initial initialLabels operations
        occurrences final finalLabels)
    (aligned : initialLabels.length = initial.blocks.length)
    {occurrence : ConversionOccurrence}
    (member : occurrence ∈ occurrences) :
    ∃ (before after : State n) (labels : RootLabels)
        (block : Block n),
      Step params before (.convert occurrence.block) after ∧
        labels.length = before.blocks.length ∧
        before.block? occurrence.block = some block ∧
        RootLabels.root? labels occurrence.block =
          some occurrence.root ∧
        block.mode = .growing ∧
        occurrence.convertedMass = block.elements.length := by
  induction history with
  | nil valid =>
      simp at member
  | @cons before middle final beforeLabels finalLabels operation operations
      tailOccurrences head tail ih =>
      rcases List.mem_append.mp member with headMember | tailMember
      · obtain
          ⟨block, operation_eq, block_found, root_found, growing,
            mass_eq⟩ :=
          conversion_spec_of_mem_operationConversionOccurrences
            head aligned headMember
        subst operation
        exact
          ⟨before, middle, beforeLabels, block, head, aligned,
            block_found, root_found, growing, mass_eq⟩
      · have next_aligned :
            (RootLabels.after beforeLabels operation).length =
              middle.blocks.length :=
          (HistoryStep.mk head rfl).labels_length aligned
        exact ih next_aligned tailMember

end RootConversionHistory

/--
Canonical root-labelled conversion history and its exact global entry-budget
bound for every interface trace from an initial state.
-/
theorem Trace.exists_rootConversionHistory
    {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (initialState : initial.Initial params)
    (trace : Trace params initial operations final) :
    ∃ (finalLabels : RootLabels)
        (occurrences : List ConversionOccurrence),
      RootConversionHistory params initial [] operations occurrences
        final finalLabels ∧
      (occurrences.map ConversionOccurrence.convertedMass).sum ≤
        totalInserts operations + totalActivity operations := by
  obtain ⟨finalLabels, lineageHistory, _aligned⟩ :=
    HistoryTrace.lift_initial initialState trace
  obtain ⟨occurrences, conversionHistory⟩ :=
    RootConversionHistory.lift lineageHistory
  have balance := conversionHistory.growingMass_balance
  have initial_zero : initial.growingMass = 0 := by
    simp [State.growingMass, growingMassBlocks, initialState.2]
  rw [initial_zero, zero_add] at balance
  exact ⟨finalLabels, occurrences, conversionHistory, by omega⟩

end Splay.Interface
