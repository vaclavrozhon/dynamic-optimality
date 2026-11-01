import Splay.Interface.LineageElements

namespace Splay.Interface

/-- The operation-level origin of an element joining a growing block. -/
inductive JoinOrigin (n : ℕ)
  | insert
  | pass (source : BlockId) (winner : Element n)
  deriving DecidableEq, Repr

/--
One join event with the complete pre-state data needed by later charging
arguments.

`destinationCreator` and `destinationPassCount` are inherited from the actual
destination block immediately before the join.  `valueAtJoin` freezes the
element value at that same instant.
-/
structure JoinOccurrence (n : ℕ) where
  origin : JoinOrigin n
  element : Element n
  destination : BlockId
  destinationRoot : RootId
  valueAtJoin : ℕ
  destinationCreator : Element n
  destinationPassCount : ℕ
  deriving DecidableEq, Repr

/--
Total constructor for a join occurrence.

The fallbacks are irrelevant on legal aligned steps; lookup-success theorems
below prove that every field is read from an actual destination block/root.
-/
def makeJoinOccurrence {n : ℕ}
    (before : State n) (labels : RootLabels)
    (origin : JoinOrigin n) (element : Element n)
    (destination : BlockId) (fallbackCreator : Element n) :
    JoinOccurrence n :=
  let destinationBlock? := before.block? destination
  { origin := origin
    element := element
    destination := destination
    destinationRoot :=
      (RootLabels.root? labels destination).getD destination
    valueAtJoin := before.value element
    destinationCreator :=
      (destinationBlock?.map Block.creator).getD fallbackCreator
    destinationPassCount :=
      (destinationBlock?.map Block.passCount).getD 0 }

/--
Deterministic join annotation of one operation at its exact pre-state.

An explicit insert contributes one occurrence.  A pass contributes one
occurrence for every loser, at that pairing's actual destination identifier.
-/
def operationJoinOccurrences {n : ℕ}
    (before : State n) (labels : RootLabels) :
    Operation n → List (JoinOccurrence n)
  | .insert destination element =>
      [makeJoinOccurrence before labels .insert element destination element]
  | .pass source matching =>
      matching.map fun pairing =>
        makeJoinOccurrence before labels
          (.pass source pairing.winner) pairing.loser
          pairing.destination pairing.winner
  | _ => []

@[simp]
theorem operationJoinOccurrences_convert {n : ℕ}
    (before : State n) (labels : RootLabels) (blockId : BlockId) :
    operationJoinOccurrences before labels (.convert blockId) = [] :=
  rfl

@[simp]
theorem operationJoinOccurrences_create {n : ℕ}
    (before : State n) (labels : RootLabels) (creator : Element n) :
    operationJoinOccurrences before labels (.create creator) = [] :=
  rfl

@[simp]
theorem operationJoinOccurrences_insert {n : ℕ}
    (before : State n) (labels : RootLabels)
    (blockId : BlockId) (element : Element n) :
    operationJoinOccurrences before labels (.insert blockId element) =
      [makeJoinOccurrence before labels .insert element blockId element] :=
  rfl

@[simp]
theorem operationJoinOccurrences_delete {n : ℕ}
    (before : State n) (labels : RootLabels)
    (blockId : BlockId) (element : Element n) :
    operationJoinOccurrences before labels (.delete blockId element) = [] :=
  rfl

@[simp]
theorem operationJoinOccurrences_pass {n : ℕ}
    (before : State n) (labels : RootLabels) (source : BlockId)
    (matching : List (Pairing n)) :
    operationJoinOccurrences before labels (.pass source matching) =
      matching.map fun pairing =>
        makeJoinOccurrence before labels
          (.pass source pairing.winner) pairing.loser
          pairing.destination pairing.winner :=
  rfl

@[simp]
theorem operationJoinOccurrences_split {n : ℕ}
    (before : State n) (labels : RootLabels)
    (blockId prefixLength : BlockId) :
    operationJoinOccurrences before labels
      (.split blockId prefixLength) = [] :=
  rfl

@[simp]
theorem operationJoinOccurrences_valueChange {n : ℕ}
    (before : State n) (labels : RootLabels)
    (element : Element n) (delta : ValueDelta) :
    operationJoinOccurrences before labels
      (.valueChange element delta) = [] :=
  rfl

/-- One operation contributes exactly inserts plus pass activity joins. -/
@[simp]
theorem length_operationJoinOccurrences {n : ℕ}
    (before : State n) (labels : RootLabels)
    (operation : Operation n) :
    (operationJoinOccurrences before labels operation).length =
      operation.insertCount + operation.activity := by
  cases operation <;>
    simp [operationJoinOccurrences, Operation.insertCount,
      Operation.activity]

/-- The stored join value is definitionally the element's exact pre-state value. -/
theorem valueAtJoin_eq_of_mem_operationJoinOccurrences
    {n : ℕ} {before : State n} {labels : RootLabels}
    {operation : Operation n} {occurrence : JoinOccurrence n}
    (member :
      occurrence ∈ operationJoinOccurrences before labels operation) :
    occurrence.valueAtJoin = before.value occurrence.element := by
  cases operation with
  | convert blockId =>
      simp at member
  | create creator =>
      simp at member
  | insert blockId element =>
      simp only [operationJoinOccurrences_insert, List.mem_singleton] at member
      subst occurrence
      rfl
  | delete blockId element =>
      simp at member
  | pass source matching =>
      obtain ⟨pairing, pairing_mem, occurrence_eq⟩ :=
        List.mem_map.mp member
      subst occurrence
      rfl
  | split blockId prefixLength =>
      simp at member
  | valueChange element delta =>
      simp at member

/-- Alignment turns every successful block lookup into a successful root lookup. -/
theorem root_exists_of_aligned_block_found
    {n : ℕ} {state : State n} {labels : RootLabels}
    (aligned : labels.length = state.blocks.length)
    {blockId : BlockId} {block : Block n}
    (found : state.block? blockId = some block) :
    ∃ root, RootLabels.root? labels blockId = some root := by
  obtain ⟨block_lt, _block_eq⟩ :=
    List.getElem?_eq_some_iff.mp found
  have root_lt : blockId < labels.length := by
    simpa [aligned] using block_lt
  exact
    ⟨labels[blockId],
      List.getElem?_eq_getElem root_lt⟩

/-- Operation-shape specification for every deterministic join occurrence. -/
theorem origin_spec_of_mem_operationJoinOccurrences
    {n : ℕ} {before : State n} {labels : RootLabels}
    {operation : Operation n} {occurrence : JoinOccurrence n}
    (member :
      occurrence ∈ operationJoinOccurrences before labels operation) :
    (operation =
        .insert occurrence.destination occurrence.element ∧
      occurrence.origin = .insert) ∨
      ∃ source matching pairing,
        operation = .pass source matching ∧
          pairing ∈ matching ∧
          occurrence.origin = .pass source pairing.winner ∧
          occurrence.destination = pairing.destination ∧
          occurrence.element = pairing.loser := by
  cases operation with
  | convert blockId =>
      simp at member
  | create creator =>
      simp at member
  | insert blockId element =>
      simp only [operationJoinOccurrences_insert, List.mem_singleton] at member
      subst occurrence
      exact Or.inl ⟨rfl, rfl⟩
  | delete blockId element =>
      simp at member
  | pass source matching =>
      obtain ⟨pairing, pairing_mem, occurrence_eq⟩ :=
        List.mem_map.mp member
      subst occurrence
      exact
        Or.inr
          ⟨source, matching, pairing, rfl, pairing_mem, rfl, rfl, rfl⟩
  | split blockId prefixLength =>
      simp at member
  | valueChange element delta =>
      simp at member

namespace JoinOccurrence

/-- Successful destination lookup and exact inherited metadata at join time. -/
def LookupValidAt {n : ℕ} (before : State n) (labels : RootLabels)
    (occurrence : JoinOccurrence n) : Prop :=
  ∃ destinationBlock,
    before.block? occurrence.destination = some destinationBlock ∧
      RootLabels.root? labels occurrence.destination =
        some occurrence.destinationRoot ∧
      destinationBlock.mode = .growing ∧
      occurrence.destinationCreator = destinationBlock.creator ∧
      occurrence.destinationPassCount = destinationBlock.passCount ∧
      occurrence.valueAtJoin = before.value occurrence.element

end JoinOccurrence

/--
Every join encoded for an aligned legal step uses an actual growing
destination block and its actual root and inherited metadata.
-/
theorem lookupValidAt_of_mem_operationJoinOccurrences
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n} {occurrence : JoinOccurrence n}
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    (member :
      occurrence ∈ operationJoinOccurrences before labels operation) :
    occurrence.LookupValidAt before labels := by
  cases operation with
  | convert blockId =>
      simp at member
  | create creator =>
      simp at member
  | insert blockId element =>
      rcases step with ⟨_before_valid, effect, _after_valid⟩
      cases effect with
      | insert found growing unassigned value_order blocks_eq values_eq =>
          rename_i block
          obtain ⟨root, root_found⟩ :=
            root_exists_of_aligned_block_found aligned found
          simp only [operationJoinOccurrences_insert,
            List.mem_singleton] at member
          subst occurrence
          simp [JoinOccurrence.LookupValidAt, makeJoinOccurrence,
            found, root_found, growing]
  | delete blockId element =>
      simp at member
  | pass source matching =>
      rcases step with ⟨_before_valid, effect, _after_valid⟩
      cases effect with
      | pass source_found valid_matching blocks_eq values_eq =>
          obtain ⟨pairing, pairing_mem, occurrence_eq⟩ :=
            List.mem_map.mp member
          have pairing_valid :=
            valid_matching.2.2.2.1 pairing pairing_mem
          obtain ⟨destinationBlock, destination_found,
              destination_growing, _destination_creator⟩ :=
            pairing_valid.2.2.2
          obtain ⟨destinationRoot, root_found⟩ :=
            root_exists_of_aligned_block_found aligned destination_found
          subst occurrence
          simp [JoinOccurrence.LookupValidAt, makeJoinOccurrence,
            destination_found, root_found, destination_growing]
  | split blockId prefixLength =>
      simp at member
  | valueChange element delta =>
      simp at member

/-- Every legal join freezes a value inside the interface's global bounds. -/
theorem valueAtJoin_bounds_of_mem_operationJoinOccurrences
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n} {occurrence : JoinOccurrence n}
    (step : Step params before operation after)
    (member :
      occurrence ∈ operationJoinOccurrences before labels operation) :
    1 ≤ occurrence.valueAtJoin ∧
      occurrence.valueAtJoin ≤ params.valueBound := by
  rw [valueAtJoin_eq_of_mem_operationJoinOccurrences member]
  exact step.1.2.1 occurrence.element

/--
Every join occurrence is present in its destination lineage immediately after
the annotated step.
-/
theorem element_mem_lineageElements_after_of_mem_operationJoinOccurrences
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n} {occurrence : JoinOccurrence n}
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    (member :
      occurrence ∈ operationJoinOccurrences before labels operation) :
    occurrence.element ∈
      lineageElements after (RootLabels.after labels operation)
        occurrence.destinationRoot := by
  obtain ⟨destinationBlock, destination_found, root_found,
      _destination_growing, _creator_eq, _passCount_eq, _value_eq⟩ :=
    lookupValidAt_of_mem_operationJoinOccurrences step aligned member
  rcases origin_spec_of_mem_operationJoinOccurrences member with
      insert_spec | pass_spec
  · rcases insert_spec with ⟨operation_eq, _origin_eq⟩
    subst operation
    let historyStep :
        HistoryStep params before labels
          (.insert occurrence.destination occurrence.element)
          after
          (RootLabels.after labels
            (.insert occurrence.destination occurrence.element)) :=
      ⟨step, rfl⟩
    rw [historyStep.lineageElements_insert aligned
      occurrence.destinationRoot]
    apply Finset.mem_union_right
    simp [root_found]
  · obtain ⟨source, matching, pairing, operation_eq, pairing_mem,
        _origin_eq, destination_eq, element_eq⟩ :=
      pass_spec
    subst operation
    have delivered :
        occurrence.element ∈
          destinationLineageLosers labels matching
            occurrence.destinationRoot := by
      apply mem_destinationLineageLosers_iff.mpr
      refine
        ⟨pairing, pairing_mem, element_eq.symm, ?_⟩
      simpa [RootLabels.root?, ← destination_eq] using root_found
    let historyStep :
        HistoryStep params before labels (.pass source matching)
          after (RootLabels.after labels (.pass source matching)) :=
      ⟨step, rfl⟩
    exact
      (historyStep.mem_lineageElements_pass_iff aligned
        occurrence.destinationRoot).mpr (Or.inr delivered)

/--
A complete history with deterministic join annotations at every pre-state.
-/
inductive JoinHistory {n : ℕ} (params : Parameters) :
    State n → RootLabels → List (Operation n) →
      List (JoinOccurrence n) → State n → RootLabels → Prop
  | nil {state : State n} {labels : RootLabels}
      (valid : state.Valid params) :
      JoinHistory params state labels [] [] state labels
  | cons {before middle after : State n}
      {beforeLabels afterLabels : RootLabels}
      {operation : Operation n} {operations : List (Operation n)}
      {tailOccurrences : List (JoinOccurrence n)}
      (head : Step params before operation middle)
      (tail :
        JoinHistory params middle
          (RootLabels.after beforeLabels operation)
          operations tailOccurrences after afterLabels) :
      JoinHistory params before beforeLabels
        (operation :: operations)
        (operationJoinOccurrences before beforeLabels operation ++
          tailOccurrences)
        after afterLabels

namespace JoinHistory

/-- Forgetting join annotations recovers the ghost-lineage history. -/
theorem erase
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (JoinOccurrence n)}
    (history :
      JoinHistory params initial initialLabels operations occurrences
        final finalLabels) :
    HistoryTrace params initial initialLabels operations final finalLabels := by
  induction history with
  | nil valid =>
      exact .nil valid
  | cons head tail ih =>
      exact .cons head ih

/-- Every lineage history admits its deterministic join annotation. -/
theorem lift
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    (history :
      HistoryTrace params initial initialLabels operations
        final finalLabels) :
    ∃ occurrences,
      JoinHistory params initial initialLabels operations occurrences
        final finalLabels := by
  induction history with
  | nil valid =>
      exact ⟨[], .nil valid⟩
  | @cons before middle after beforeLabels afterLabels operation operations
      head tail ih =>
      obtain ⟨tailOccurrences, annotatedTail⟩ := ih
      exact
        ⟨operationJoinOccurrences before beforeLabels operation ++
            tailOccurrences,
          .cons head annotatedTail⟩

/-- Alignment is preserved at the endpoint of an annotated join history. -/
theorem labels_length
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (JoinOccurrence n)}
    (history :
      JoinHistory params initial initialLabels operations occurrences
        final finalLabels)
    (aligned : initialLabels.length = initial.blocks.length) :
    finalLabels.length = final.blocks.length :=
  history.erase.labels_length aligned

/-- Lift an aligned lineage history and retain endpoint alignment. -/
theorem lift_aligned
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    (history :
      HistoryTrace params initial initialLabels operations
        final finalLabels)
    (aligned : initialLabels.length = initial.blocks.length) :
    ∃ occurrences,
      JoinHistory params initial initialLabels operations occurrences
          final finalLabels ∧
        finalLabels.length = final.blocks.length := by
  obtain ⟨occurrences, annotated⟩ := lift history
  exact
    ⟨occurrences, annotated,
      annotated.labels_length aligned⟩

/--
The global occurrence count is exact: one per explicit insert and one per
pass pairing.
-/
theorem occurrences_length
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (JoinOccurrence n)}
    (history :
      JoinHistory params initial initialLabels operations occurrences
        final finalLabels) :
    occurrences.length =
      totalInserts operations + totalActivity operations := by
  induction history with
  | nil valid =>
      rfl
  | @cons before middle after beforeLabels afterLabels operation operations
      tailOccurrences head tail ih =>
      simp only [List.length_append, length_operationJoinOccurrences]
      rw [ih]
      simp only [totalInserts, totalActivity, List.map_cons, List.sum_cons]
      omega

/-- Every occurrence in a legal history stores a globally bounded join value. -/
theorem occurrence_value_bounds
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (JoinOccurrence n)}
    (history :
      JoinHistory params initial initialLabels operations occurrences
        final finalLabels)
    {occurrence : JoinOccurrence n} (member : occurrence ∈ occurrences) :
    1 ≤ occurrence.valueAtJoin ∧
      occurrence.valueAtJoin ≤ params.valueBound := by
  induction history with
  | nil valid =>
      simp at member
  | @cons before middle after beforeLabels afterLabels operation operations
      tailOccurrences head tail ih =>
      rcases List.mem_append.mp member with head_member | tail_member
      · exact
          valueAtJoin_bounds_of_mem_operationJoinOccurrences
            head head_member
      · exact ih tail_member

/--
Every global occurrence comes with a concrete aligned step snapshot at which
all destination lookups and inherited fields succeed.
-/
theorem occurrence_lookup_snapshot
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (JoinOccurrence n)}
    (history :
      JoinHistory params initial initialLabels operations occurrences
        final finalLabels)
    (aligned : initialLabels.length = initial.blocks.length)
    {occurrence : JoinOccurrence n} (member : occurrence ∈ occurrences) :
    ∃ (before : State n) (labels : RootLabels)
        (operation : Operation n) (after : State n),
      Step params before operation after ∧
        labels.length = before.blocks.length ∧
        occurrence ∈
          operationJoinOccurrences before labels operation ∧
        occurrence.LookupValidAt before labels := by
  induction history with
  | nil valid =>
      simp at member
  | @cons before middle after beforeLabels afterLabels operation operations
      tailOccurrences head tail ih =>
      rcases List.mem_append.mp member with head_member | tail_member
      · exact
          ⟨before, beforeLabels, operation, middle, head, aligned,
            head_member,
            lookupValidAt_of_mem_operationJoinOccurrences
              head aligned head_member⟩
      · have middle_aligned :
            (RootLabels.after beforeLabels operation).length =
              middle.blocks.length :=
          (HistoryStep.mk head rfl).labels_length aligned
        exact ih middle_aligned tail_member

/--
Every global occurrence also exposes the exact immediate post-step payload in
which its element appears.
-/
theorem occurrence_payload_snapshot
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (JoinOccurrence n)}
    (history :
      JoinHistory params initial initialLabels operations occurrences
        final finalLabels)
    (aligned : initialLabels.length = initial.blocks.length)
    {occurrence : JoinOccurrence n} (member : occurrence ∈ occurrences) :
    ∃ (before : State n) (labels : RootLabels)
        (operation : Operation n) (after : State n),
      Step params before operation after ∧
        labels.length = before.blocks.length ∧
        occurrence ∈
          operationJoinOccurrences before labels operation ∧
        occurrence.element ∈
          lineageElements after (RootLabels.after labels operation)
            occurrence.destinationRoot := by
  obtain ⟨before, labels, operation, after, step, step_aligned,
      operation_member, _lookup_valid⟩ :=
    history.occurrence_lookup_snapshot aligned member
  exact
    ⟨before, labels, operation, after, step, step_aligned,
      operation_member,
      element_mem_lineageElements_after_of_mem_operationJoinOccurrences
        step step_aligned operation_member⟩

/--
Every ordinary trace from an interface initial state has a canonical aligned
join history, with its exact occurrence count.
-/
theorem lift_initial
    {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (initialState : initial.Initial params)
    (trace : Trace params initial operations final) :
    ∃ finalLabels occurrences,
      JoinHistory params initial [] operations occurrences
          final finalLabels ∧
        finalLabels.length = final.blocks.length ∧
        occurrences.length =
          totalInserts operations + totalActivity operations := by
  obtain ⟨finalLabels, lineageHistory, final_aligned⟩ :=
    HistoryTrace.lift_initial initialState trace
  obtain ⟨occurrences, annotated⟩ := lift lineageHistory
  exact
    ⟨finalLabels, occurrences, annotated, final_aligned,
      annotated.occurrences_length⟩

end JoinHistory

end Splay.Interface
