import Splay.Interface.Model

namespace Splay.Interface

/--
Ghost label carried by every live or emptied block.

The label is the stable block identifier of the `create` operation at the root
of its lineage.  A split does not create a new lineage: both appended children
inherit the source label.
-/
abbrev RootId :=
  BlockId

/-- One root label for each entry of `State.blocks`, in the same order. -/
abbrev RootLabels :=
  List RootId

namespace RootLabels

/-- Lookup the lineage root of a block. -/
def root? (labels : RootLabels) (block : BlockId) : Option RootId :=
  labels[block]?

/--
Ghost update associated with an interface operation.

Only `create` and `split` change the number of blocks.  A newly created block
is its own lineage root.  The two children appended by a split inherit the
source root.  The fallback in the split case is irrelevant for valid, aligned
steps, where the source lookup is proved to succeed.
-/
def after {n : ℕ} (labels : RootLabels) : Operation n → RootLabels
  | .create _ =>
      labels ++ [labels.length]
  | .split source _ =>
      let root := (root? labels source).getD source
      labels ++ [root, root]
  | _ =>
      labels

@[simp]
theorem after_create {n : ℕ} (labels : RootLabels) (creator : Element n) :
    after labels (.create creator) = labels ++ [labels.length] :=
  rfl

@[simp]
theorem after_split {n : ℕ} (labels : RootLabels) (source prefixLength : ℕ) :
    after labels (.split source prefixLength : Operation n) =
      labels ++
        [(root? labels source).getD source,
          (root? labels source).getD source] :=
  rfl

@[simp]
theorem length_after {n : ℕ} (labels : RootLabels)
    (operation : Operation n) :
    (after labels operation).length =
      labels.length +
        match operation with
        | .create _ => 1
        | .split _ _ => 2
        | _ => 0 := by
  cases operation <;> simp [after]

@[simp]
theorem create_root? {n : ℕ} (labels : RootLabels) (creator : Element n) :
    root? (after labels (.create creator)) labels.length =
      some labels.length := by
  simp [root?, after]

theorem split_left_root? {n : ℕ} (labels : RootLabels)
    (source prefixLength : ℕ) :
    root? (after labels (.split source prefixLength : Operation n))
        labels.length =
      some ((root? labels source).getD source) := by
  simp [root?, after]

theorem split_right_root? {n : ℕ} (labels : RootLabels)
    (source prefixLength : ℕ) :
    root? (after labels (.split source prefixLength : Operation n))
        (labels.length + 1) =
      some ((root? labels source).getD source) := by
  simp [root?, after]

end RootLabels

/-- The number of blocks appended by an operation. -/
def Operation.blockIncrease {n : ℕ} : Operation n → ℕ
  | .create _ => 1
  | .split _ _ => 2
  | _ => 0

namespace Operation

@[simp]
theorem blockIncrease_create {n : ℕ} (creator : Element n) :
    (Operation.create creator).blockIncrease = 1 :=
  rfl

@[simp]
theorem blockIncrease_split {n : ℕ} (source prefixLength : ℕ) :
    (Operation.split source prefixLength : Operation n).blockIncrease = 2 :=
  rfl

end Operation

/-- Updating pass destinations never changes the number of blocks. -/
theorem length_insertAtDestinations {n : ℕ} (blocks : List (Block n))
    (matching : List (Pairing n)) :
    (insertAtDestinations blocks matching).length = blocks.length := by
  induction matching generalizing blocks with
  | nil =>
      rfl
  | cons pairing matching ih =>
      simpa [insertAtDestinations] using
        ih (blocks.modify pairing.destination fun destination =>
          { destination with
            elements := pairing.loser :: destination.elements })

/--
Destination updates leave a distinct source block at the same stable
identifier.
-/
theorem block?_insertAtDestinations_of_ne {n : ℕ}
    (blocks : List (Block n)) (matching : List (Pairing n))
    (sourceId : BlockId)
    (destinations_ne :
      ∀ pairing ∈ matching, pairing.destination ≠ sourceId) :
    (insertAtDestinations blocks matching)[sourceId]? =
      blocks[sourceId]? := by
  induction matching generalizing blocks with
  | nil =>
      rfl
  | cons pairing matching ih =>
      rw [show insertAtDestinations blocks (pairing :: matching) =
        insertAtDestinations
          (blocks.modify pairing.destination fun destination =>
            { destination with
              elements := pairing.loser :: destination.elements })
          matching by rfl]
      rw [ih]
      · simp [destinations_ne pairing (by simp)]
      · intro later later_mem
        exact destinations_ne later (by simp [later_mem])

/-- A pass changes block contents but not the block identifier space. -/
theorem length_passBlocks {n : ℕ} (blocks : List (Block n))
    (sourceId : BlockId) (source : Block n) (matching : List (Pairing n)) :
    (passBlocks blocks sourceId source matching).length = blocks.length := by
  simp [passBlocks, length_insertAtDestinations]

/-- Exact change in the length of the block list for every interface effect. -/
theorem Effect.blocks_length {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    (effect : Effect params before operation after) :
    after.blocks.length =
      before.blocks.length + operation.blockIncrease := by
  cases effect with
  | convert found growing blocks_eq values_eq =>
      simp [blocks_eq, Operation.blockIncrease]
  | create room blocks_eq values_eq =>
      simp [blocks_eq, Operation.blockIncrease]
  | insert found growing unassigned value_order blocks_eq values_eq =>
      simp [blocks_eq, Operation.blockIncrease]
  | delete found shrinking present blocks_eq values_eq =>
      simp [blocks_eq, Operation.blockIncrease]
  | pass found valid_matching blocks_eq values_eq =>
      simp [blocks_eq, Operation.blockIncrease, length_passBlocks]
  | split found shrinking prefix_le blocks_eq values_eq =>
      simp [blocks_eq, splitBlocks, Operation.blockIncrease]
  | decrease can_decrease blocks_eq values_eq =>
      simp [blocks_eq, Operation.blockIncrease]
  | increase can_increase blocks_eq values_eq =>
      simp [blocks_eq, Operation.blockIncrease]

/-- The block appended by `create` occupies its fresh stable identifier. -/
theorem Effect.create_block? {n : ℕ} {params : Parameters}
    {before after : State n} {creator : Element n}
    (effect : Effect params before (.create creator) after) :
    after.block? before.blocks.length =
      some
        { creator := creator
          passCount := 0
          mode := .growing
          elements := [] } := by
  cases effect with
  | create room blocks_eq values_eq =>
      simp [State.block?, blocks_eq]

/-- The first block appended by `split` is the source prefix. -/
theorem Effect.split_left_child? {n : ℕ} {params : Parameters}
    {before after : State n} {sourceId prefixLength : ℕ}
    (effect :
      Effect params before (.split sourceId prefixLength) after) :
    ∃ source,
      before.block? sourceId = some source ∧
        after.block? before.blocks.length =
          some { source with
            elements := source.elements.take prefixLength } := by
  cases effect with
  | split found shrinking prefix_le blocks_eq values_eq =>
      rename_i source
      refine ⟨source, found, ?_⟩
      simp [State.block?, blocks_eq, splitBlocks]

/-- The second block appended by `split` is the source suffix. -/
theorem Effect.split_right_child? {n : ℕ} {params : Parameters}
    {before after : State n} {sourceId prefixLength : ℕ}
    (effect :
      Effect params before (.split sourceId prefixLength) after) :
    ∃ source,
      before.block? sourceId = some source ∧
        after.block? (before.blocks.length + 1) =
          some { source with
            elements := source.elements.drop prefixLength } := by
  cases effect with
  | split found shrinking prefix_le blocks_eq values_eq =>
      rename_i source
      refine ⟨source, found, ?_⟩
      simp [State.block?, blocks_eq, splitBlocks]

/--
A pass increments the source pass counter, removes exactly the listed losers
from its element sequence, and preserves its lineage-relevant metadata.
-/
theorem Effect.pass_source? {n : ℕ} {params : Parameters}
    {before after : State n} {sourceId : BlockId}
    {matching : List (Pairing n)}
    (effect : Effect params before (.pass sourceId matching) after) :
    ∃ source,
      before.block? sourceId = some source ∧
        after.block? sourceId =
          some
            { source with
              passCount := source.passCount + 1
              elements := removeLosers source.elements matching } := by
  cases effect with
  | pass found valid_matching blocks_eq values_eq =>
      rename_i source
      refine ⟨source, found, ?_⟩
      unfold State.block?
      unfold State.block? at found
      rw [blocks_eq]
      unfold passBlocks
      rw [block?_insertAtDestinations_of_ne]
      · simp [found]
      · intro pairing pairing_mem
        exact (valid_matching.2.2.2.1 pairing pairing_mem).2.2.1

/--
One ordinary interface step together with its deterministic ghost-lineage
update.  Erasing the labels recovers exactly the original `Step`.
-/
structure HistoryStep {n : ℕ} (params : Parameters)
    (before : State n) (beforeLabels : RootLabels)
    (operation : Operation n)
    (after : State n) (afterLabels : RootLabels) : Prop where
  step : Step params before operation after
  labels_eq : afterLabels = RootLabels.after beforeLabels operation

namespace HistoryStep

/-- Forgetting lineage annotations is a projection to the original semantics. -/
theorem erase {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {operation : Operation n}
    (historyStep :
      HistoryStep params before beforeLabels operation after afterLabels) :
    Step params before operation after :=
  historyStep.step

/-- Aligned labels remain aligned after every valid annotated step. -/
theorem labels_length {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {operation : Operation n}
    (historyStep :
      HistoryStep params before beforeLabels operation after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length) :
    afterLabels.length = after.blocks.length := by
  rw [historyStep.labels_eq, RootLabels.length_after, aligned]
  exact historyStep.step.2.1.blocks_length.symm

/--
The block appended by `create` has a fresh identifier and is the root of its
own lineage.
-/
theorem create_is_new_root {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {creator : Element n}
    (historyStep :
      HistoryStep params before beforeLabels (.create creator)
        after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length) :
    RootLabels.root? afterLabels before.blocks.length =
      some before.blocks.length := by
  rw [historyStep.labels_eq]
  simpa [aligned] using RootLabels.create_root? beforeLabels creator

/--
Both fresh block identifiers appended by a split keep the source lineage root.
-/
theorem split_children_inherit_root {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {sourceId prefixLength : ℕ}
    (historyStep :
      HistoryStep params before beforeLabels
        (.split sourceId prefixLength) after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length)
    {sourceRoot : RootId}
    (source_found :
      RootLabels.root? beforeLabels sourceId = some sourceRoot) :
    RootLabels.root? afterLabels before.blocks.length = some sourceRoot ∧
      RootLabels.root? afterLabels (before.blocks.length + 1) =
        some sourceRoot := by
  rw [historyStep.labels_eq]
  constructor
  · simpa [aligned, source_found] using
      RootLabels.split_left_root? (n := n) beforeLabels sourceId prefixLength
  · simpa [aligned, source_found] using
      RootLabels.split_right_root? (n := n) beforeLabels sourceId prefixLength

/-- A valid aligned split source always has a lineage root label. -/
theorem split_source_root_exists {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {sourceId prefixLength : ℕ}
    (historyStep :
      HistoryStep params before beforeLabels
        (.split sourceId prefixLength) after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length) :
    ∃ sourceRoot,
      RootLabels.root? beforeLabels sourceId = some sourceRoot := by
  obtain ⟨source, source_found, _left_found⟩ :=
    historyStep.step.2.1.split_left_child?
  obtain ⟨source_lt, _source_eq⟩ :=
    List.getElem?_eq_some_iff.mp source_found
  have label_lt : sourceId < beforeLabels.length := by
    simpa [aligned] using source_lt
  exact
    ⟨beforeLabels[sourceId],
      List.getElem?_eq_getElem label_lt⟩

/-- Both split children inherit some existing source root, without a fallback. -/
theorem split_children_have_source_root {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {sourceId prefixLength : ℕ}
    (historyStep :
      HistoryStep params before beforeLabels
        (.split sourceId prefixLength) after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length) :
    ∃ sourceRoot,
      RootLabels.root? beforeLabels sourceId = some sourceRoot ∧
        RootLabels.root? afterLabels before.blocks.length =
          some sourceRoot ∧
        RootLabels.root? afterLabels (before.blocks.length + 1) =
          some sourceRoot := by
  obtain ⟨sourceRoot, source_found⟩ :=
    historyStep.split_source_root_exists aligned
  obtain ⟨left_inherits, right_inherits⟩ :=
    historyStep.split_children_inherit_root aligned source_found
  exact ⟨sourceRoot, source_found, left_inherits, right_inherits⟩

/--
Both blocks appended by a split inherit the source's pass counter.  This is
the concrete state fact paired with `split_children_inherit_root`.
-/
theorem split_children_inherit_passCount {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {sourceId prefixLength : ℕ}
    (historyStep :
      HistoryStep params before beforeLabels
        (.split sourceId prefixLength) after afterLabels) :
    ∃ source,
      before.block? sourceId = some source ∧
        (∃ left,
          after.block? before.blocks.length = some left ∧
            left.passCount = source.passCount) ∧
        ∃ right,
          after.block? (before.blocks.length + 1) = some right ∧
            right.passCount = source.passCount := by
  obtain ⟨source, source_found, left_found⟩ :=
    historyStep.step.2.1.split_left_child?
  obtain ⟨source', source_found', right_found⟩ :=
    historyStep.step.2.1.split_right_child?
  have source_eq : source' = source := by
    rw [source_found] at source_found'
    exact (Option.some.inj source_found').symm
  subst source'
  refine ⟨source, source_found, ?_, ?_⟩
  · refine
      ⟨{ source with elements := source.elements.take prefixLength },
        left_found, ?_⟩
    rfl
  · refine
      ⟨{ source with elements := source.elements.drop prefixLength },
        right_found, ?_⟩
    rfl

end HistoryStep

/--
A ghost lineage annotation of a complete interface trace.

The state sequence and operations are unchanged.  The extra endpoint lists
record the lineage root of every stable block identifier.
-/
inductive HistoryTrace {n : ℕ} (params : Parameters) :
    State n → RootLabels → List (Operation n) →
      State n → RootLabels → Prop
  | nil {state : State n} {labels : RootLabels}
      (valid : state.Valid params) :
      HistoryTrace params state labels [] state labels
  | cons {before middle after : State n}
      {beforeLabels afterLabels : RootLabels}
      {operation : Operation n} {operations : List (Operation n)}
      (head : Step params before operation middle)
      (tail :
        HistoryTrace params middle
          (RootLabels.after beforeLabels operation)
          operations after afterLabels) :
      HistoryTrace params before beforeLabels
        (operation :: operations) after afterLabels

namespace HistoryTrace

/-- Erasing all root labels recovers the underlying interface trace. -/
theorem erase {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    (history :
      HistoryTrace params initial initialLabels operations final finalLabels) :
    Trace params initial operations final := by
  induction history with
  | nil valid =>
      exact .nil valid
  | cons head tail ih =>
      exact .cons head ih

/-- Every ordinary trace admits the deterministic lineage annotation. -/
theorem lift {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (trace : Trace params initial operations final)
    (initialLabels : RootLabels) :
    ∃ finalLabels,
      HistoryTrace params initial initialLabels operations final finalLabels := by
  induction trace generalizing initialLabels with
  | nil valid =>
      exact ⟨initialLabels, .nil valid⟩
  | cons head tail ih =>
      obtain ⟨finalLabels, historyTail⟩ :=
        ih (RootLabels.after initialLabels _)
      exact ⟨finalLabels, .cons head historyTail⟩

/-- Alignment of root labels with block identifiers telescopes over a trace. -/
theorem labels_length {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    (history :
      HistoryTrace params initial initialLabels operations final finalLabels)
    (aligned : initialLabels.length = initial.blocks.length) :
    finalLabels.length = final.blocks.length := by
  induction history with
  | nil valid =>
      exact aligned
  | @cons before middle after beforeLabels afterLabels operation operations
      head tail ih =>
      apply ih
      rw [RootLabels.length_after, aligned]
      exact head.2.1.blocks_length.symm

/--
Every trace from an interface initial state has a canonical, aligned lineage
history starting with no root labels.
-/
theorem lift_initial {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (initialState : initial.Initial params)
    (trace : Trace params initial operations final) :
    ∃ finalLabels,
      HistoryTrace params initial [] operations final finalLabels ∧
        finalLabels.length = final.blocks.length := by
  obtain ⟨finalLabels, history⟩ := lift trace []
  refine ⟨finalLabels, history, history.labels_length ?_⟩
  simp [initialState.2]

end HistoryTrace

end Splay.Interface
