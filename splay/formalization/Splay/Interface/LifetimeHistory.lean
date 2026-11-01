import Splay.Interface.JoinHistory

namespace Splay.Interface

/-- Why an active block-residence episode ends. -/
inductive LeaveReason (n : ℕ)
  | delete
  | pass (destination : BlockId) (winner : Element n)
  deriving DecidableEq, Repr

/-- Exact pre-state data for one element leaving its current block. -/
structure LeaveOccurrence (n : ℕ) where
  reason : LeaveReason n
  element : Element n
  source : BlockId
  sourceRoot : RootId
  valueAtLeave : ℕ
  sourceCreator : Element n
  sourcePassCount : ℕ
  deriving DecidableEq, Repr

/-- Total constructor; legal aligned steps prove that no fallback is used. -/
def makeLeaveOccurrence {n : ℕ}
    (before : State n) (labels : RootLabels)
    (reason : LeaveReason n) (element : Element n)
    (source : BlockId) (fallbackCreator : Element n) :
    LeaveOccurrence n :=
  let sourceBlock? := before.block? source
  { reason := reason
    element := element
    source := source
    sourceRoot := (RootLabels.root? labels source).getD source
    valueAtLeave := before.value element
    sourceCreator :=
      (sourceBlock?.map Block.creator).getD fallbackCreator
    sourcePassCount :=
      (sourceBlock?.map Block.passCount).getD 0 }

/--
Deterministic block-leave events of one operation.

A split is deliberately not a leave: the element survives in a descendant
block with the same lineage root.  Pass losers leave the source immediately
before their corresponding joins from `operationJoinOccurrences`.
-/
def operationLeaveOccurrences {n : ℕ}
    (before : State n) (labels : RootLabels) :
    Operation n → List (LeaveOccurrence n)
  | .delete source element =>
      [makeLeaveOccurrence before labels .delete element source element]
  | .pass source matching =>
      matching.map fun pairing =>
        makeLeaveOccurrence before labels
          (.pass pairing.destination pairing.winner)
          pairing.loser source pairing.winner
  | _ => []

namespace Operation

/-- Number of block-residence episodes closed by one operation. -/
def leaveCount {n : ℕ} : Operation n → ℕ
  | .delete _ _ => 1
  | .pass _ matching => matching.length
  | _ => 0

end Operation

/-- Exact number of block leaves produced by one operation. -/
@[simp]
theorem length_operationLeaveOccurrences {n : ℕ}
    (before : State n) (labels : RootLabels)
    (operation : Operation n) :
    (operationLeaveOccurrences before labels operation).length =
      operation.leaveCount := by
  cases operation <;>
    simp [operationLeaveOccurrences, Operation.leaveCount]

@[simp]
theorem operationLeaveOccurrences_convert {n : ℕ}
    (before : State n) (labels : RootLabels) (blockId : BlockId) :
    operationLeaveOccurrences before labels (.convert blockId) = [] :=
  rfl

@[simp]
theorem operationLeaveOccurrences_create {n : ℕ}
    (before : State n) (labels : RootLabels) (creator : Element n) :
    operationLeaveOccurrences before labels (.create creator) = [] :=
  rfl

@[simp]
theorem operationLeaveOccurrences_insert {n : ℕ}
    (before : State n) (labels : RootLabels)
    (blockId : BlockId) (element : Element n) :
    operationLeaveOccurrences before labels (.insert blockId element) = [] :=
  rfl

@[simp]
theorem operationLeaveOccurrences_delete {n : ℕ}
    (before : State n) (labels : RootLabels)
    (blockId : BlockId) (element : Element n) :
    operationLeaveOccurrences before labels (.delete blockId element) =
      [makeLeaveOccurrence before labels .delete element blockId element] :=
  rfl

@[simp]
theorem operationLeaveOccurrences_pass {n : ℕ}
    (before : State n) (labels : RootLabels)
    (source : BlockId) (matching : List (Pairing n)) :
    operationLeaveOccurrences before labels (.pass source matching) =
      matching.map fun pairing =>
        makeLeaveOccurrence before labels
          (.pass pairing.destination pairing.winner)
          pairing.loser source pairing.winner :=
  rfl

@[simp]
theorem operationLeaveOccurrences_split {n : ℕ}
    (before : State n) (labels : RootLabels)
    (blockId prefixLength : BlockId) :
    operationLeaveOccurrences before labels
      (.split blockId prefixLength) = [] :=
  rfl

@[simp]
theorem operationLeaveOccurrences_valueChange {n : ℕ}
    (before : State n) (labels : RootLabels)
    (element : Element n) (delta : ValueDelta) :
    operationLeaveOccurrences before labels
      (.valueChange element delta) = [] :=
  rfl

namespace LeaveOccurrence

/-- Successful source lookup and exact inherited metadata at leave time. -/
def LookupValidAt {n : ℕ} (before : State n) (labels : RootLabels)
    (occurrence : LeaveOccurrence n) : Prop :=
  ∃ sourceBlock,
    before.block? occurrence.source = some sourceBlock ∧
      RootLabels.root? labels occurrence.source =
        some occurrence.sourceRoot ∧
      sourceBlock.mode = .shrinking ∧
      occurrence.sourceCreator = sourceBlock.creator ∧
      occurrence.sourcePassCount = sourceBlock.passCount ∧
      occurrence.valueAtLeave = before.value occurrence.element

end LeaveOccurrence

/-- Every leave stores the element's exact pre-state value. -/
theorem valueAtLeave_eq_of_mem_operationLeaveOccurrences
    {n : ℕ} {before : State n} {labels : RootLabels}
    {operation : Operation n} {occurrence : LeaveOccurrence n}
    (member :
      occurrence ∈ operationLeaveOccurrences before labels operation) :
    occurrence.valueAtLeave = before.value occurrence.element := by
  cases operation with
  | convert blockId =>
      simp at member
  | create creator =>
      simp at member
  | insert blockId element =>
      simp at member
  | delete blockId element =>
      simp only [operationLeaveOccurrences_delete,
        List.mem_singleton] at member
      subst occurrence
      rfl
  | pass source matching =>
      obtain ⟨pairing, pairing_mem, occurrence_eq⟩ :=
        List.mem_map.mp member
      subst occurrence
      rfl
  | split blockId prefixLength =>
      simp at member
  | valueChange element delta =>
      simp at member

/-- Every legal leave uses an actual shrinking source and its actual root. -/
theorem lookupValidAt_of_mem_operationLeaveOccurrences
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n} {occurrence : LeaveOccurrence n}
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    (member :
      occurrence ∈ operationLeaveOccurrences before labels operation) :
    occurrence.LookupValidAt before labels := by
  cases operation with
  | convert blockId =>
      simp at member
  | create creator =>
      simp at member
  | insert blockId element =>
      simp at member
  | delete blockId element =>
      rcases step with ⟨_before_valid, effect, _after_valid⟩
      cases effect with
      | delete found shrinking present blocks_eq values_eq =>
          rename_i sourceBlock
          obtain ⟨sourceRoot, root_found⟩ :=
            root_exists_of_aligned_block_found aligned found
          simp only [operationLeaveOccurrences_delete,
            List.mem_singleton] at member
          subst occurrence
          simp [LeaveOccurrence.LookupValidAt, makeLeaveOccurrence,
            found, root_found, shrinking]
  | pass source matching =>
      rcases step with ⟨_before_valid, effect, _after_valid⟩
      cases effect with
      | pass source_found valid_matching blocks_eq values_eq =>
          obtain ⟨pairing, pairing_mem, occurrence_eq⟩ :=
            List.mem_map.mp member
          obtain ⟨sourceRoot, root_found⟩ :=
            root_exists_of_aligned_block_found aligned source_found
          subst occurrence
          simp [LeaveOccurrence.LookupValidAt, makeLeaveOccurrence,
            source_found, root_found, valid_matching.1]
  | split blockId prefixLength =>
      simp at member
  | valueChange element delta =>
      simp at member

/-- Every legal leave freezes a value inside the global value bounds. -/
theorem valueAtLeave_bounds_of_mem_operationLeaveOccurrences
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n} {occurrence : LeaveOccurrence n}
    (step : Step params before operation after)
    (member :
      occurrence ∈ operationLeaveOccurrences before labels operation) :
    1 ≤ occurrence.valueAtLeave ∧
      occurrence.valueAtLeave ≤ params.valueBound := by
  rw [valueAtLeave_eq_of_mem_operationLeaveOccurrences member]
  exact step.1.2.1 occurrence.element

/-- In a valid state, one element cannot occur in two distinct block IDs. -/
theorem State.Valid.blockId_eq_of_element_mem
    {n : ℕ} {params : Parameters} {state : State n}
    (valid : state.Valid params)
    {firstId secondId : BlockId} {first second : Block n}
    {element : Element n}
    (first_found : state.block? firstId = some first)
    (first_mem : element ∈ first.elements)
    (second_found : state.block? secondId = some second)
    (second_mem : element ∈ second.elements) :
    firstId = secondId := by
  have global_nodup :
      (state.blocks.flatMap Block.elements).Nodup := by
    simpa [State.allElements] using valid.1
  have blocks_pairwise :
      state.blocks.Pairwise
        (fun first second =>
          List.Disjoint first.elements second.elements) :=
    (List.nodup_flatMap.mp global_nodup).2
  obtain ⟨first_lt, first_eq⟩ :=
    List.getElem?_eq_some_iff.mp first_found
  obtain ⟨second_lt, second_eq⟩ :=
    List.getElem?_eq_some_iff.mp second_found
  rcases lt_trichotomy firstId secondId with first_before | ids_eq |
      second_before
  · have disjoint :
        List.Disjoint state.blocks[firstId].elements
          state.blocks[secondId].elements :=
      (List.pairwise_iff_getElem.mp blocks_pairwise)
        firstId secondId first_lt second_lt first_before
    rw [first_eq, second_eq] at disjoint
    exact False.elim ((List.disjoint_left.mp disjoint) first_mem second_mem)
  · exact ids_eq
  · have disjoint :
        List.Disjoint state.blocks[secondId].elements
          state.blocks[firstId].elements :=
      (List.pairwise_iff_getElem.mp blocks_pairwise)
        secondId firstId second_lt first_lt second_before
    rw [second_eq, first_eq] at disjoint
    exact False.elim ((List.disjoint_left.mp disjoint) second_mem first_mem)

/-- A valid aligned state gives every assigned element a unique lineage root. -/
theorem State.Valid.lineage_root_unique
    {n : ℕ} {params : Parameters} {state : State n}
    (valid : state.Valid params) {labels : RootLabels}
    (aligned : labels.length = state.blocks.length)
    {element : Element n} {firstRoot secondRoot : RootId}
    (first_mem :
      element ∈ lineageElements state labels firstRoot)
    (second_mem :
      element ∈ lineageElements state labels secondRoot) :
    firstRoot = secondRoot := by
  obtain ⟨firstId, firstBlock, first_found, first_root_found,
      first_block_mem⟩ :=
    (mem_lineageElements_iff aligned).mp first_mem
  obtain ⟨secondId, secondBlock, second_found, second_root_found,
      second_block_mem⟩ :=
    (mem_lineageElements_iff aligned).mp second_mem
  have ids_eq :=
    valid.blockId_eq_of_element_mem first_found first_block_mem
      second_found second_block_mem
  subst secondId
  rw [first_root_found] at second_root_found
  exact Option.some.inj second_root_found

/-- Aligned lineage payloads partition exactly the assigned elements. -/
theorem mem_allElements_iff_exists_lineageElements
    {n : ℕ} {state : State n} {labels : RootLabels}
    (aligned : labels.length = state.blocks.length)
    {element : Element n} :
    element ∈ state.allElements ↔
      ∃ root, element ∈ lineageElements state labels root := by
  constructor
  · intro assigned
    obtain ⟨block, block_mem, element_mem⟩ :=
      List.mem_flatMap.mp (by
        simpa [State.allElements] using assigned)
    obtain ⟨blockId, block_found⟩ :=
      List.mem_iff_getElem?.mp block_mem
    have state_found : state.block? blockId = some block := by
      exact block_found
    obtain ⟨root, root_found⟩ :=
      root_exists_of_aligned_block_found aligned state_found
    exact
      ⟨root,
        (mem_lineageElements_iff aligned).mpr
          ⟨blockId, block, state_found, root_found, element_mem⟩⟩
  · rintro ⟨root, member⟩
    change element ∈ state.blocks.flatMap Block.elements
    exact mem_flatMap_elements_of_mem_lineageElementsOf member

/-- Removing other pass losers preserves an existing element. -/
theorem mem_removeLosers_of_mem_of_not_loser
    {n : ℕ} {element : Element n} {elements : List (Element n)}
    {matching : List (Pairing n)}
    (member : element ∈ elements)
    (not_loser : element ∉ pairingLosers matching) :
    element ∈ removeLosers elements matching := by
  induction matching generalizing elements with
  | nil =>
      simpa [removeLosers]
  | cons pairing matching ih =>
      have element_ne : element ≠ pairing.loser := by
        intro element_eq
        apply not_loser
        simp [pairingLosers, element_eq]
      have tail_not_loser : element ∉ pairingLosers matching := by
        intro tail_member
        apply not_loser
        change element ∈ pairing.loser :: pairingLosers matching
        exact List.mem_cons_of_mem pairing.loser tail_member
      apply ih
      · exact (List.mem_erase_of_ne element_ne).2 member
      · exact tail_not_loser

/--
Destination insertion preserves every element already in a block and never
changes that block's creator.
-/
theorem placement_insertAtDestinations
    {n : ℕ} {blocks : List (Block n)} {blockId : BlockId}
    {block : Block n} {element : Element n}
    (matching : List (Pairing n))
    (found : blocks[blockId]? = some block)
    (member : element ∈ block.elements) :
    ∃ afterBlock,
      (insertAtDestinations blocks matching)[blockId]? =
          some afterBlock ∧
        element ∈ afterBlock.elements ∧
        afterBlock.creator = block.creator := by
  induction matching generalizing blocks block with
  | nil =>
      exact ⟨block, found, member, rfl⟩
  | cons pairing matching ih =>
      let updated :=
        blocks.modify pairing.destination fun destination =>
          { destination with
            elements := pairing.loser :: destination.elements }
      by_cases id_eq : blockId = pairing.destination
      · subst blockId
        have updated_found :
            updated[pairing.destination]? =
              some
                { block with
                  elements := pairing.loser :: block.elements } := by
          simp [updated, found]
        obtain ⟨afterBlock, after_found, after_member, creator_eq⟩ :=
          ih updated_found (by simp [member])
        exact ⟨afterBlock, after_found, after_member, by
          simpa using creator_eq⟩
      · have updated_found :
            updated[blockId]? = some block := by
          have destination_ne : pairing.destination ≠ blockId :=
            Ne.symm id_eq
          simpa [updated, destination_ne] using found
        exact ih updated_found member

/--
With distinct destination IDs, the block selected by one pass pairing is
updated exactly once, by prepending that pairing's loser.
-/
theorem block?_insertAtDestinations_eq_of_mem
    {n : ℕ} (blocks : List (Block n)) {matching : List (Pairing n)}
    (destinations_nodup :
      (matching.map fun pairing => pairing.destination).Nodup)
    {pairing : Pairing n} (pairing_mem : pairing ∈ matching) :
    (insertAtDestinations blocks matching)[pairing.destination]? =
      (blocks[pairing.destination]?).map fun destination =>
        { destination with
          elements := pairing.loser :: destination.elements } := by
  induction matching generalizing blocks with
  | nil =>
      simp at pairing_mem
  | cons head matching ih =>
      have head_not_mem :
          head.destination ∉
            matching.map fun pairing => pairing.destination :=
        (List.nodup_cons.mp (by
          simpa using destinations_nodup)).1
      have tail_nodup :
          (matching.map fun pairing => pairing.destination).Nodup :=
        (List.nodup_cons.mp (by
          simpa using destinations_nodup)).2
      rcases List.mem_cons.mp pairing_mem with pairing_eq | tail_mem
      · subst pairing
        rw [show
          insertAtDestinations blocks (head :: matching) =
            insertAtDestinations
              (blocks.modify head.destination fun destination =>
                { destination with
                  elements := head.loser :: destination.elements })
              matching by rfl]
        rw [block?_insertAtDestinations_of_ne]
        · simp
        · intro later later_mem
          have later_destination_mem :
              later.destination ∈
                matching.map fun pairing => pairing.destination :=
            List.mem_map.mpr ⟨later, later_mem, rfl⟩
          exact fun destination_eq =>
            head_not_mem (destination_eq ▸ later_destination_mem)
      · rw [show
          insertAtDestinations blocks (head :: matching) =
            insertAtDestinations
              (blocks.modify head.destination fun destination =>
                { destination with
                  elements := head.loser :: destination.elements })
              matching by rfl]
        rw [ih (blocks :=
          blocks.modify head.destination fun destination =>
            { destination with
              elements := head.loser :: destination.elements })
          tail_nodup tail_mem]
        have destinations_ne :
            pairing.destination ≠ head.destination := by
          intro destination_eq
          apply head_not_mem
          apply List.mem_map.mpr
          exact ⟨pairing, tail_mem, destination_eq⟩
        simp [Ne.symm destinations_ne]

/--
The immutable snapshot that opens one block-residence episode.

`JoinOccurrence` already freezes the joining element's value.  The additional
field freezes the destination creator's value at the same pre-state, without
changing the lower-level join annotation API.
-/
structure EpisodeStart (n : ℕ) where
  join : JoinOccurrence n
  creatorValueAtJoin : ℕ
  deriving DecidableEq, Repr

namespace EpisodeStart

/-- Build the complete opening snapshot from a join and its exact pre-state. -/
def ofJoin {n : ℕ} (before : State n)
    (join : JoinOccurrence n) : EpisodeStart n :=
  { join := join
    creatorValueAtJoin := before.value join.destinationCreator }

@[simp]
theorem ofJoin_creatorValueAtJoin {n : ℕ} (before : State n)
    (join : JoinOccurrence n) :
    (ofJoin before join).creatorValueAtJoin =
      before.value join.destinationCreator :=
  rfl

/-- The join snapshot records that the joining element was above its creator. -/
def JoinValid {n : ℕ} (start : EpisodeStart n) : Prop :=
  start.creatorValueAtJoin + 1 ≤ start.join.valueAtJoin

end EpisodeStart

/-- Every start built from a legal join satisfies its frozen value gap. -/
theorem joinValid_of_mem_operationJoinOccurrences
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n} {join : JoinOccurrence n}
    (step : Step params before operation after)
    (member : join ∈ operationJoinOccurrences before labels operation) :
    (EpisodeStart.ofJoin before join).JoinValid := by
  cases operation with
  | convert blockId =>
      simp at member
  | create creator =>
      simp at member
  | insert destination element =>
      cases step.2.1 with
      | insert destination_found growing unassigned value_order
          blocks_eq values_eq =>
          simp only [operationJoinOccurrences_insert,
            List.mem_singleton] at member
          subst join
          simpa [EpisodeStart.JoinValid, EpisodeStart.ofJoin,
            makeJoinOccurrence, destination_found] using value_order
  | delete source element =>
      simp at member
  | pass source matching =>
      obtain ⟨pairing, pairing_mem, join_eq⟩ :=
        List.mem_map.mp member
      subst join
      cases step.2.1 with
      | pass source_found valid_matching blocks_eq values_eq =>
          have pairing_valid :=
            valid_matching.2.2.2.1 pairing pairing_mem
          obtain ⟨destinationBlock, destination_found,
              destination_growing, destination_creator⟩ :=
            pairing_valid.2.2.2
          simpa [EpisodeStart.JoinValid, EpisodeStart.ofJoin,
            makeJoinOccurrence, destination_found,
            destination_creator] using pairing_valid.2.1
  | split source prefixLength =>
      simp at member
  | valueChange element delta =>
      simp at member

/--
The currently open block-residence episode for each element.  Its payload is
the exact immutable snapshot that opened the episode.
-/
abbrev EpisodeLedger (n : ℕ) :=
  Element n → Option (EpisodeStart n)

namespace EpisodeLedger

def empty {n : ℕ} : EpisodeLedger n :=
  fun _ => none

/-- Install all pass joins, in matching order. -/
def installPassJoins {n : ℕ}
    (before : State n) (labels : RootLabels) (source : BlockId) :
    EpisodeLedger n → List (Pairing n) → EpisodeLedger n
  | ledger, [] => ledger
  | ledger, pairing :: matching =>
      installPassJoins before labels source
        (Function.update ledger pairing.loser
          (some
            (EpisodeStart.ofJoin before
              (makeJoinOccurrence before labels
                (.pass source pairing.winner) pairing.loser
                pairing.destination pairing.winner))))
        matching

/-- Exact active-episode update of one operation. -/
def after {n : ℕ} (before : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) : Operation n → EpisodeLedger n
  | .insert destination element =>
      Function.update ledger element
        (some
          (EpisodeStart.ofJoin before
            (makeJoinOccurrence before labels .insert element
              destination element)))
  | .delete _ element =>
      Function.update ledger element none
  | .pass source matching =>
      installPassJoins before labels source ledger matching
  | _ => ledger

/--
Every open episode points to its own element and to a lineage payload that
still contains that element.  The original destination block may since have
split; only the lineage root is intentionally required to survive.
-/
def SoundAt {n : ℕ} (state : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) : Prop :=
  ∀ element start,
    ledger element = some start →
      start.join.element = element ∧
        element ∈
          lineageElements state labels start.join.destinationRoot

/-- Every assigned element has an open episode. -/
def CompleteAt {n : ℕ} (state : State n)
    (ledger : EpisodeLedger n) : Prop :=
  ∀ element, element ∈ state.allElements →
    ∃ start, ledger element = some start

/-- Exact physical placement of an element in a block with a given creator. -/
def PlacementAt {n : ℕ} (state : State n) (element creator : Element n) :
    Prop :=
  ∃ blockId block,
    state.block? blockId = some block ∧
      element ∈ block.elements ∧
      block.creator = creator

/--
Every open episode remains in a current descendant block whose creator is the
creator frozen by the opening join.  In particular, a split may change the
block ID but cannot change this creator.
-/
def PlacementSoundAt {n : ℕ} (state : State n)
    (ledger : EpisodeLedger n) : Prop :=
  ∀ element start, ledger element = some start →
    PlacementAt state element start.join.destinationCreator

/-- Every open episode carries a legal frozen join-value gap. -/
def JoinSoundAt {n : ℕ} (ledger : EpisodeLedger n) : Prop :=
  ∀ element start, ledger element = some start →
    start.JoinValid

/-- The complete inductive invariant for the active episode ledger. -/
structure ExactAt {n : ℕ} (state : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) : Prop where
  sound : SoundAt state labels ledger
  complete : CompleteAt state ledger
  placement : PlacementSoundAt state ledger
  joinSound : JoinSoundAt ledger

@[simp]
theorem installPassJoins_nil {n : ℕ}
    (before : State n) (labels : RootLabels) (source : BlockId)
    (ledger : EpisodeLedger n) :
    installPassJoins before labels source ledger [] = ledger :=
  rfl

@[simp]
theorem installPassJoins_cons {n : ℕ}
    (before : State n) (labels : RootLabels) (source : BlockId)
    (ledger : EpisodeLedger n) (pairing : Pairing n)
    (matching : List (Pairing n)) :
    installPassJoins before labels source ledger (pairing :: matching) =
      installPassJoins before labels source
        (Function.update ledger pairing.loser
          (some
            (EpisodeStart.ofJoin before
              (makeJoinOccurrence before labels
                (.pass source pairing.winner) pairing.loser
                pairing.destination pairing.winner))))
        matching :=
  rfl

/-- A pass leaves an element's active episode unchanged when it is not a loser. -/
theorem installPassJoins_apply_of_not_mem
    {n : ℕ} (before : State n) (labels : RootLabels)
    (source : BlockId) (ledger : EpisodeLedger n)
    (matching : List (Pairing n)) (element : Element n)
    (not_loser : element ∉ pairingLosers matching) :
    installPassJoins before labels source ledger matching element =
      ledger element := by
  induction matching generalizing ledger with
  | nil =>
      rfl
  | cons pairing matching ih =>
      have not_cons :
          element ∉ pairing.loser :: pairingLosers matching := by
        simpa [pairingLosers] using not_loser
      have element_ne : element ≠ pairing.loser :=
        (List.ne_and_not_mem_of_not_mem_cons not_cons).1
      have not_tail : element ∉ pairingLosers matching :=
        (List.ne_and_not_mem_of_not_mem_cons not_cons).2
      rw [installPassJoins_cons]
      rw [ih _ not_tail]
      simp [Function.update, element_ne]

/--
Distinct pass losers make the installed episode at each loser independent of
all later matching entries.
-/
theorem installPassJoins_apply_of_mem
    {n : ℕ} (before : State n) (labels : RootLabels)
    (source : BlockId) (ledger : EpisodeLedger n)
    {matching : List (Pairing n)} (losers_nodup :
      (pairingLosers matching).Nodup)
    {pairing : Pairing n} (pairing_mem : pairing ∈ matching) :
    installPassJoins before labels source ledger matching pairing.loser =
      some
        (EpisodeStart.ofJoin before
          (makeJoinOccurrence before labels
            (.pass source pairing.winner) pairing.loser
            pairing.destination pairing.winner)) := by
  induction matching generalizing ledger pairing with
  | nil =>
      simp at pairing_mem
  | cons head matching ih =>
      rcases List.mem_cons.mp pairing_mem with pairing_eq | pairing_tail
      · subst pairing
        have head_not_tail :
            head.loser ∉ pairingLosers matching := by
          simpa [pairingLosers] using
            (List.nodup_cons.mp losers_nodup).1
        rw [installPassJoins_cons]
        rw [installPassJoins_apply_of_not_mem
          before labels source _ matching head.loser head_not_tail]
        simp
      · have tail_nodup : (pairingLosers matching).Nodup := by
          simpa [pairingLosers] using
            (List.nodup_cons.mp losers_nodup).2
        rw [installPassJoins_cons]
        exact ih _ tail_nodup pairing_tail

@[simp]
theorem after_convert {n : ℕ} (before : State n)
    (labels : RootLabels) (ledger : EpisodeLedger n)
    (blockId : BlockId) :
    after before labels ledger (.convert blockId) = ledger :=
  rfl

@[simp]
theorem after_create {n : ℕ} (before : State n)
    (labels : RootLabels) (ledger : EpisodeLedger n)
    (creator : Element n) :
    after before labels ledger (.create creator) = ledger :=
  rfl

@[simp]
theorem after_split {n : ℕ} (before : State n)
    (labels : RootLabels) (ledger : EpisodeLedger n)
    (blockId prefixLength : BlockId) :
    after before labels ledger (.split blockId prefixLength) = ledger :=
  rfl

@[simp]
theorem after_valueChange {n : ℕ} (before : State n)
    (labels : RootLabels) (ledger : EpisodeLedger n)
    (element : Element n) (delta : ValueDelta) :
    after before labels ledger (.valueChange element delta) = ledger :=
  rfl

/-- Every legal join opens exactly the occurrence carried by the annotation. -/
theorem after_apply_eq_some_of_join
    {n : ℕ} {params : Parameters}
    {before afterState : State n} {labels : RootLabels}
    {operation : Operation n} {occurrence : JoinOccurrence n}
    (step : Step params before operation afterState)
    (ledger : EpisodeLedger n)
    (member :
      occurrence ∈ operationJoinOccurrences before labels operation) :
    after before labels ledger operation occurrence.element =
      some (EpisodeStart.ofJoin before occurrence) := by
  cases operation with
  | convert blockId =>
      simp at member
  | create creator =>
      simp at member
  | insert blockId element =>
      simp only [operationJoinOccurrences_insert,
        List.mem_singleton] at member
      subst occurrence
      simp [after, makeJoinOccurrence, EpisodeStart.ofJoin]
  | delete blockId element =>
      simp at member
  | pass source matching =>
      rcases step with ⟨_before_valid, effect, _after_valid⟩
      cases effect with
      | pass source_found valid_matching blocks_eq values_eq =>
          obtain ⟨pairing, pairing_mem, occurrence_eq⟩ :=
            List.mem_map.mp member
          have losers_nodup :
              (pairingLosers matching).Nodup :=
            pairingLosers_nodup valid_matching.2.1
          subst occurrence
          exact
            installPassJoins_apply_of_mem before labels source ledger
              losers_nodup pairing_mem
  | split blockId prefixLength =>
      simp at member
  | valueChange element delta =>
      simp at member

/-- A legal join is physically placed in its actual destination block. -/
theorem placementAt_after_of_join
    {n : ℕ} {params : Parameters}
    {before next : State n} {labels : RootLabels}
    {operation : Operation n} {join : JoinOccurrence n}
    (step : Step params before operation next)
    (member : join ∈ operationJoinOccurrences before labels operation) :
    PlacementAt next join.element join.destinationCreator := by
  cases operation with
  | convert blockId =>
      simp at member
  | create creator =>
      simp at member
  | insert destination element =>
      cases step.2.1 with
      | insert destination_found growing unassigned value_order
          blocks_eq values_eq =>
          rename_i destinationBlock
          simp only [operationJoinOccurrences_insert,
            List.mem_singleton] at member
          subst join
          let nextBlock : Block n :=
            { destinationBlock with
              elements := element :: destinationBlock.elements }
          have destination_state_found :
              before.block? destination = some destinationBlock :=
            destination_found
          change before.blocks[destination]? = some destinationBlock at destination_found
          refine
            ⟨destination, nextBlock, ?_,
              by simp [nextBlock, makeJoinOccurrence], ?_⟩
          · simp [State.block?, blocks_eq, nextBlock,
              destination_found]
          · simp [nextBlock, makeJoinOccurrence, destination_state_found]
  | delete source element =>
      simp at member
  | pass source matching =>
      obtain ⟨pairing, pairing_mem, join_eq⟩ :=
        List.mem_map.mp member
      subst join
      cases step.2.1 with
      | pass source_found valid_matching blocks_eq values_eq =>
          rename_i sourceBlock
          have pairing_valid :=
            valid_matching.2.2.2.1 pairing pairing_mem
          obtain ⟨destinationBlock, destination_found,
              destination_growing, destination_creator⟩ :=
            pairing_valid.2.2.2
          let nextBlock : Block n :=
            { destinationBlock with
              elements := pairing.loser :: destinationBlock.elements }
          have destination_state_found :
              before.block? pairing.destination = some destinationBlock :=
            destination_found
          change before.blocks[pairing.destination]? =
            some destinationBlock at destination_found
          refine
            ⟨pairing.destination, nextBlock, ?_,
              by simp [nextBlock, makeJoinOccurrence], ?_⟩
          · change next.blocks[pairing.destination]? = some nextBlock
            rw [blocks_eq]
            unfold passBlocks
            rw [block?_insertAtDestinations_eq_of_mem _
              valid_matching.2.2.1 pairing_mem]
            have source_ne_destination :
                source ≠ pairing.destination :=
              Ne.symm pairing_valid.2.2.1
            simp [source_ne_destination, destination_found, nextBlock]
          · simp [nextBlock, makeJoinOccurrence, destination_state_found]
  | split source prefixLength =>
      simp at member
  | valueChange element delta =>
      simp at member

/--
The active-episode invariant is preserved by every aligned legal step.
In particular, split preserves the original join record while moving the
element into descendant blocks of the same lineage.
-/
theorem SoundAt.after_step
    {n : ℕ} {params : Parameters}
    {before next : State n} {labels : RootLabels}
    {operation : Operation n} {ledger : EpisodeLedger n}
    (sound : SoundAt before labels ledger)
    (step : Step params before operation next)
    (aligned : labels.length = before.blocks.length) :
    SoundAt next (RootLabels.after labels operation)
      (after before labels ledger operation) := by
  cases operation with
  | convert blockId =>
      intro element occurrence ledger_found
      have old := sound element occurrence (by simpa using ledger_found)
      refine ⟨old.1, ?_⟩
      let historyStep :
          HistoryStep params before labels (.convert blockId) next
            (RootLabels.after labels (.convert blockId)) :=
        ⟨step, rfl⟩
      rw [historyStep.lineageElements_convert aligned
        occurrence.join.destinationRoot]
      exact old.2
  | create creator =>
      intro element occurrence ledger_found
      have old := sound element occurrence (by simpa using ledger_found)
      refine ⟨old.1, ?_⟩
      let historyStep :
          HistoryStep params before labels (.create creator) next
            (RootLabels.after labels (.create creator)) :=
        ⟨step, rfl⟩
      rw [historyStep.lineageElements_create aligned
        occurrence.join.destinationRoot]
      exact old.2
  | insert blockId inserted =>
      intro element occurrence ledger_found
      by_cases element_eq : element = inserted
      · subst element
        let joined :=
          makeJoinOccurrence before labels .insert inserted blockId inserted
        have joined_member :
            joined ∈
              operationJoinOccurrences before labels
                (.insert blockId inserted) := by
          simp [joined]
        have installed :
            EpisodeLedger.after before labels ledger
                (.insert blockId inserted) inserted =
              some (EpisodeStart.ofJoin before joined) :=
          after_apply_eq_some_of_join step ledger joined_member
        rw [installed] at ledger_found
        have joined_eq : EpisodeStart.ofJoin before joined = occurrence :=
          Option.some.inj ledger_found
        subst occurrence
        have payload_member :=
          element_mem_lineageElements_after_of_mem_operationJoinOccurrences
            step aligned joined_member
        simpa [EpisodeStart.ofJoin, joined, makeJoinOccurrence] using
          And.intro (rfl : joined.element = inserted) payload_member
      · have old_found : ledger element = some occurrence := by
          simpa [EpisodeLedger.after, element_eq] using ledger_found
        have old := sound element occurrence old_found
        refine ⟨old.1, ?_⟩
        let historyStep :
            HistoryStep params before labels (.insert blockId inserted)
              next (RootLabels.after labels (.insert blockId inserted)) :=
          ⟨step, rfl⟩
        exact
          (historyStep.mem_lineageElements_insert_iff aligned
            occurrence.join.destinationRoot).mpr (Or.inl old.2)
  | delete blockId deleted =>
      intro element occurrence ledger_found
      by_cases element_eq : element = deleted
      · subst element
        simp [EpisodeLedger.after] at ledger_found
      · have old_found : ledger element = some occurrence := by
          simpa [EpisodeLedger.after, element_eq] using ledger_found
        have old := sound element occurrence old_found
        refine ⟨old.1, ?_⟩
        let historyStep :
            HistoryStep params before labels (.delete blockId deleted)
              next (RootLabels.after labels (.delete blockId deleted)) :=
          ⟨step, rfl⟩
        apply
          (historyStep.mem_lineageElements_delete_iff aligned
            occurrence.join.destinationRoot).mpr
        refine ⟨old.2, ?_⟩
        by_cases source_root :
            RootLabels.root? labels blockId =
              some occurrence.join.destinationRoot
        · simp [source_root, element_eq]
        · simp [source_root]
  | pass source matching =>
      intro element occurrence ledger_found
      have losers_nodup : (pairingLosers matching).Nodup := by
        cases step.2.1 with
        | pass source_found valid_matching blocks_eq values_eq =>
            exact pairingLosers_nodup valid_matching.2.1
      by_cases loser_mem : element ∈ pairingLosers matching
      · obtain ⟨pairing, pairing_mem, loser_eq⟩ :=
          List.mem_map.mp (by simpa [pairingLosers] using loser_mem)
        let joined :=
          makeJoinOccurrence before labels
            (.pass source pairing.winner) pairing.loser
            pairing.destination pairing.winner
        have joined_member :
            joined ∈
              operationJoinOccurrences before labels
                (.pass source matching) := by
          apply List.mem_map.mpr
          exact ⟨pairing, pairing_mem, rfl⟩
        have installed :
            EpisodeLedger.after before labels ledger
                (.pass source matching) pairing.loser =
              some (EpisodeStart.ofJoin before joined) :=
          after_apply_eq_some_of_join step ledger joined_member
        have installed_at_element :
            EpisodeLedger.after before labels ledger
                (.pass source matching) element =
              some (EpisodeStart.ofJoin before joined) := by
          simpa [loser_eq] using installed
        rw [installed_at_element] at ledger_found
        have joined_eq : EpisodeStart.ofJoin before joined = occurrence :=
          Option.some.inj ledger_found
        subst occurrence
        have payload_member :=
          element_mem_lineageElements_after_of_mem_operationJoinOccurrences
            step aligned joined_member
        refine ⟨?_, ?_⟩
        · simpa [EpisodeStart.ofJoin, joined, makeJoinOccurrence] using
            loser_eq
        · simpa [EpisodeStart.ofJoin, joined, makeJoinOccurrence,
            loser_eq] using payload_member
      · have old_found : ledger element = some occurrence := by
          change
            installPassJoins before labels source ledger matching element =
              some occurrence at ledger_found
          rw [installPassJoins_apply_of_not_mem
            before labels source ledger matching element loser_mem] at ledger_found
          exact ledger_found
        have old := sound element occurrence old_found
        have not_source_loser :
            element ∉
              sourceLineageLosers labels source matching
                occurrence.join.destinationRoot := by
          unfold sourceLineageLosers
          split
          · simpa using loser_mem
          · simp
        refine ⟨old.1, ?_⟩
        let historyStep :
            HistoryStep params before labels (.pass source matching)
              next (RootLabels.after labels (.pass source matching)) :=
          ⟨step, rfl⟩
        exact
          (historyStep.mem_lineageElements_pass_iff aligned
            occurrence.join.destinationRoot).mpr
            (Or.inl ⟨old.2, not_source_loser⟩)
  | split blockId prefixLength =>
      intro element occurrence ledger_found
      have old := sound element occurrence (by simpa using ledger_found)
      refine ⟨old.1, ?_⟩
      let historyStep :
          HistoryStep params before labels
            (.split blockId prefixLength) next
            (RootLabels.after labels (.split blockId prefixLength)) :=
        ⟨step, rfl⟩
      rw [historyStep.lineageElements_split aligned
        occurrence.join.destinationRoot]
      exact old.2
  | valueChange changed delta =>
      intro element occurrence ledger_found
      have old := sound element occurrence (by simpa using ledger_found)
      refine ⟨old.1, ?_⟩
      let historyStep :
          HistoryStep params before labels
            (.valueChange changed delta) next
            (RootLabels.after labels (.valueChange changed delta)) :=
        ⟨step, rfl⟩
      rw [historyStep.lineageElements_valueChange
        occurrence.join.destinationRoot]
      exact old.2

/-- Completeness of the active ledger is preserved by every aligned step. -/
theorem CompleteAt.after_step
    {n : ℕ} {params : Parameters}
    {before next : State n} {labels : RootLabels}
    {operation : Operation n} {ledger : EpisodeLedger n}
    (complete : CompleteAt before ledger)
    (step : Step params before operation next)
    (aligned : labels.length = before.blocks.length) :
    CompleteAt next (after before labels ledger operation) := by
  cases operation with
  | convert blockId =>
      intro element assigned
      let historyStep :
          HistoryStep params before labels (.convert blockId) next
            (RootLabels.after labels (.convert blockId)) :=
        ⟨step, rfl⟩
      have next_aligned :=
        historyStep.labels_length aligned
      obtain ⟨root, after_member⟩ :=
        (mem_allElements_iff_exists_lineageElements next_aligned).mp
          assigned
      have before_member :
          element ∈ lineageElements before labels root := by
        rw [← historyStep.lineageElements_convert aligned root]
        exact after_member
      obtain ⟨start, active⟩ :=
        complete element
          ((mem_allElements_iff_exists_lineageElements aligned).mpr
            ⟨root, before_member⟩)
      exact ⟨start, by simpa using active⟩
  | create creator =>
      intro element assigned
      let historyStep :
          HistoryStep params before labels (.create creator) next
            (RootLabels.after labels (.create creator)) :=
        ⟨step, rfl⟩
      have next_aligned :=
        historyStep.labels_length aligned
      obtain ⟨root, after_member⟩ :=
        (mem_allElements_iff_exists_lineageElements next_aligned).mp
          assigned
      have before_member :
          element ∈ lineageElements before labels root := by
        rw [← historyStep.lineageElements_create aligned root]
        exact after_member
      obtain ⟨start, active⟩ :=
        complete element
          ((mem_allElements_iff_exists_lineageElements aligned).mpr
            ⟨root, before_member⟩)
      exact ⟨start, by simpa using active⟩
  | insert blockId inserted =>
      intro element assigned
      let historyStep :
          HistoryStep params before labels (.insert blockId inserted) next
            (RootLabels.after labels (.insert blockId inserted)) :=
        ⟨step, rfl⟩
      by_cases element_eq : element = inserted
      · subst element
        let joined :=
          makeJoinOccurrence before labels .insert inserted blockId inserted
        have joined_member :
            joined ∈
              operationJoinOccurrences before labels
                (.insert blockId inserted) := by
          simp [joined]
        exact
          ⟨EpisodeStart.ofJoin before joined,
            after_apply_eq_some_of_join step ledger joined_member⟩
      · have next_aligned :=
          historyStep.labels_length aligned
        obtain ⟨root, after_member⟩ :=
          (mem_allElements_iff_exists_lineageElements next_aligned).mp
            assigned
        rcases
            (historyStep.mem_lineageElements_insert_iff aligned root).mp
              after_member with
          before_member | joined_here
        · obtain ⟨start, active⟩ :=
            complete element
              ((mem_allElements_iff_exists_lineageElements aligned).mpr
                ⟨root, before_member⟩)
          exact
            ⟨start, by
              simpa [EpisodeLedger.after, element_eq] using active⟩
        · exact False.elim (element_eq joined_here.2)
  | delete blockId deleted =>
      obtain ⟨sourceBlock, source_found, deleted_present⟩ :
          ∃ sourceBlock,
            before.block? blockId = some sourceBlock ∧
              deleted ∈ sourceBlock.elements := by
        cases step.2.1 with
        | delete found shrinking present blocks_eq values_eq =>
            exact ⟨_, found, present⟩
      obtain ⟨sourceRoot, source_root_found⟩ :=
        root_exists_of_aligned_block_found aligned source_found
      have deleted_source_payload :
          deleted ∈
            lineageElements before labels sourceRoot := by
        apply
          block_elements_subset_lineageElementsOf aligned
            source_found source_root_found
        simpa using deleted_present
      intro element assigned
      let historyStep :
          HistoryStep params before labels (.delete blockId deleted) next
            (RootLabels.after labels (.delete blockId deleted)) :=
        ⟨step, rfl⟩
      have next_aligned :=
        historyStep.labels_length aligned
      obtain ⟨root, after_member⟩ :=
        (mem_allElements_iff_exists_lineageElements next_aligned).mp
          assigned
      have transition :=
        (historyStep.mem_lineageElements_delete_iff aligned root).mp
          after_member
      have element_ne : element ≠ deleted := by
        intro element_eq
        subst element
        have roots_eq : root = sourceRoot :=
          step.1.lineage_root_unique aligned transition.1
            deleted_source_payload
        subst root
        simpa [source_root_found] using transition.2
      obtain ⟨start, active⟩ :=
        complete element
          ((mem_allElements_iff_exists_lineageElements aligned).mpr
            ⟨root, transition.1⟩)
      exact
        ⟨start, by
          simpa [EpisodeLedger.after, element_ne] using active⟩
  | pass source matching =>
      obtain ⟨sourceBlock, source_found, valid_matching⟩ :
          ∃ sourceBlock,
            before.block? source = some sourceBlock ∧
              MatchingValid params before source sourceBlock matching := by
        cases step.2.1 with
        | pass found valid_matching blocks_eq values_eq =>
            exact ⟨_, found, valid_matching⟩
      have losers_nodup : (pairingLosers matching).Nodup :=
        pairingLosers_nodup valid_matching.2.1
      intro element assigned
      by_cases loser_mem : element ∈ pairingLosers matching
      · obtain ⟨pairing, pairing_mem, loser_eq⟩ :=
          List.mem_map.mp (by simpa [pairingLosers] using loser_mem)
        subst element
        let joined :=
          makeJoinOccurrence before labels
            (.pass source pairing.winner) pairing.loser
            pairing.destination pairing.winner
        have joined_member :
            joined ∈
              operationJoinOccurrences before labels
                (.pass source matching) := by
          apply List.mem_map.mpr
          exact ⟨pairing, pairing_mem, rfl⟩
        refine ⟨EpisodeStart.ofJoin before joined, ?_⟩
        have installed :=
          after_apply_eq_some_of_join step ledger joined_member
        simpa [joined, makeJoinOccurrence] using installed
      · let historyStep :
            HistoryStep params before labels (.pass source matching) next
              (RootLabels.after labels (.pass source matching)) :=
          ⟨step, rfl⟩
        have next_aligned :=
          historyStep.labels_length aligned
        obtain ⟨root, after_member⟩ :=
          (mem_allElements_iff_exists_lineageElements next_aligned).mp
            assigned
        rcases
            (historyStep.mem_lineageElements_pass_iff aligned root).mp
              after_member with
          before_case | destination_case
        · obtain ⟨start, active⟩ :=
            complete element
              ((mem_allElements_iff_exists_lineageElements aligned).mpr
                ⟨root, before_case.1⟩)
          refine ⟨start, ?_⟩
          change
            installPassJoins before labels source ledger matching element =
              some start
          rw [installPassJoins_apply_of_not_mem
            before labels source ledger matching element loser_mem]
          exact active
        · obtain ⟨pairing, pairing_mem, loser_eq, _root_found⟩ :=
            mem_destinationLineageLosers_iff.mp destination_case
          apply False.elim
          apply loser_mem
          apply List.mem_map.mpr
          exact ⟨pairing, pairing_mem, loser_eq⟩
  | split blockId prefixLength =>
      intro element assigned
      let historyStep :
          HistoryStep params before labels
            (.split blockId prefixLength) next
            (RootLabels.after labels (.split blockId prefixLength)) :=
        ⟨step, rfl⟩
      have next_aligned :=
        historyStep.labels_length aligned
      obtain ⟨root, after_member⟩ :=
        (mem_allElements_iff_exists_lineageElements next_aligned).mp
          assigned
      have before_member :
          element ∈ lineageElements before labels root := by
        rw [← historyStep.lineageElements_split aligned root]
        exact after_member
      obtain ⟨start, active⟩ :=
        complete element
          ((mem_allElements_iff_exists_lineageElements aligned).mpr
            ⟨root, before_member⟩)
      exact ⟨start, by simpa using active⟩
  | valueChange changed delta =>
      intro element assigned
      let historyStep :
          HistoryStep params before labels
            (.valueChange changed delta) next
            (RootLabels.after labels (.valueChange changed delta)) :=
        ⟨step, rfl⟩
      have next_aligned :=
        historyStep.labels_length aligned
      obtain ⟨root, after_member⟩ :=
        (mem_allElements_iff_exists_lineageElements next_aligned).mp
          assigned
      have before_member :
          element ∈ lineageElements before labels root := by
        rw [← historyStep.lineageElements_valueChange root]
        exact after_member
      obtain ⟨start, active⟩ :=
        complete element
          ((mem_allElements_iff_exists_lineageElements aligned).mpr
            ⟨root, before_member⟩)
      exact ⟨start, by simpa using active⟩

/--
Physical placement, including the immutable episode creator, is preserved by
every operation.  Split is the only case that may replace the current block ID
by one of two fresh child IDs.
-/
theorem PlacementSoundAt.after_step
    {n : ℕ} {params : Parameters}
    {before next : State n} {labels : RootLabels}
    {operation : Operation n} {ledger : EpisodeLedger n}
    (placement : PlacementSoundAt before ledger)
    (step : Step params before operation next) :
    PlacementSoundAt next (after before labels ledger operation) := by
  cases operation with
  | convert changed =>
      intro element start active
      obtain ⟨blockId, block, found, member, creator_eq⟩ :=
        placement element start (by simpa using active)
      cases step.2.1 with
      | convert changed_found growing blocks_eq values_eq =>
          rename_i changedBlock
          change before.blocks[blockId]? = some block at found
          change before.blocks[changed]? = some changedBlock at changed_found
          by_cases ids_eq : blockId = changed
          · subst blockId
            rw [changed_found] at found
            have block_eq : changedBlock = block :=
              Option.some.inj found
            subst block
            let nextBlock : Block n :=
              { changedBlock with mode := .shrinking }
            refine
              ⟨changed, nextBlock, ?_, member, by
                simpa [nextBlock] using creator_eq⟩
            change next.blocks[changed]? = some nextBlock
            rw [blocks_eq, List.getElem?_modify_eq, changed_found]
            rfl
          · refine ⟨blockId, block, ?_, member, creator_eq⟩
            change next.blocks[blockId]? = some block
            rw [blocks_eq,
              List.getElem?_modify_ne _ _ (Ne.symm ids_eq)]
            exact found
  | create creator =>
      intro element start active
      obtain ⟨blockId, block, found, member, creator_eq⟩ :=
        placement element start (by simpa using active)
      cases step.2.1 with
      | create room blocks_eq values_eq =>
          change before.blocks[blockId]? = some block at found
          have blockId_lt : blockId < before.blocks.length :=
            (List.getElem?_eq_some_iff.mp found).1
          refine ⟨blockId, block, ?_, member, creator_eq⟩
          change next.blocks[blockId]? = some block
          rw [blocks_eq, List.getElem?_append_left blockId_lt]
          exact found
  | insert destination inserted =>
      intro element start active
      by_cases element_eq : element = inserted
      · subst element
        let joined :=
          makeJoinOccurrence before labels .insert inserted
            destination inserted
        have joined_mem :
            joined ∈
              operationJoinOccurrences before labels
                (.insert destination inserted) := by
          simp [joined]
        have installed :=
          after_apply_eq_some_of_join step ledger joined_mem
        change
          after before labels ledger (.insert destination inserted)
              inserted =
            some (EpisodeStart.ofJoin before joined) at installed
        rw [installed] at active
        have start_eq :
            EpisodeStart.ofJoin before joined = start :=
          Option.some.inj active
        subst start
        change PlacementAt next inserted joined.destinationCreator
        exact placementAt_after_of_join step joined_mem
      · have old_active : ledger element = some start := by
          simpa [after, element_eq] using active
        obtain ⟨blockId, block, found, member, creator_eq⟩ :=
          placement element start old_active
        cases step.2.1 with
        | insert destination_found growing unassigned value_order
            blocks_eq values_eq =>
            rename_i destinationBlock
            change before.blocks[blockId]? = some block at found
            change before.blocks[destination]? =
              some destinationBlock at destination_found
            by_cases ids_eq : blockId = destination
            · subst blockId
              rw [destination_found] at found
              have block_eq : destinationBlock = block :=
                Option.some.inj found
              subst block
              let nextBlock : Block n :=
                { destinationBlock with
                  elements := inserted :: destinationBlock.elements }
              refine
                ⟨destination, nextBlock, ?_, by
                  simp [nextBlock, member], by
                  simpa [nextBlock] using creator_eq⟩
              change next.blocks[destination]? = some nextBlock
              rw [blocks_eq, List.getElem?_modify_eq,
                destination_found]
              rfl
            · refine ⟨blockId, block, ?_, member, creator_eq⟩
              change next.blocks[blockId]? = some block
              rw [blocks_eq,
                List.getElem?_modify_ne _ _ (Ne.symm ids_eq)]
              exact found
  | delete source deleted =>
      intro element start active
      by_cases element_eq : element = deleted
      · subst element
        simp [after] at active
      · have old_active : ledger element = some start := by
          simpa [after, element_eq] using active
        obtain ⟨blockId, block, found, member, creator_eq⟩ :=
          placement element start old_active
        cases step.2.1 with
        | delete source_found shrinking deleted_present
            blocks_eq values_eq =>
            rename_i sourceBlock
            change before.blocks[blockId]? = some block at found
            change before.blocks[source]? = some sourceBlock at source_found
            by_cases ids_eq : blockId = source
            · subst blockId
              rw [source_found] at found
              have block_eq : sourceBlock = block :=
                Option.some.inj found
              subst block
              let nextBlock : Block n :=
                { sourceBlock with
                  elements := sourceBlock.elements.erase deleted }
              refine
                ⟨source, nextBlock, ?_,
                  (List.mem_erase_of_ne element_eq).2 member, by
                    simpa [nextBlock] using creator_eq⟩
              change next.blocks[source]? = some nextBlock
              rw [blocks_eq, List.getElem?_modify_eq, source_found]
              rfl
            · refine ⟨blockId, block, ?_, member, creator_eq⟩
              change next.blocks[blockId]? = some block
              rw [blocks_eq,
                List.getElem?_modify_ne _ _ (Ne.symm ids_eq)]
              exact found
  | pass source matching =>
      intro element start active
      obtain ⟨sourceBlock, source_found, valid_matching⟩ :
          ∃ sourceBlock,
            before.block? source = some sourceBlock ∧
              MatchingValid params before source sourceBlock matching := by
        cases step.2.1 with
        | pass found valid_matching blocks_eq values_eq =>
            exact ⟨_, found, valid_matching⟩
      by_cases loser_mem : element ∈ pairingLosers matching
      · obtain ⟨pairing, pairing_mem, loser_eq⟩ :=
          List.mem_map.mp (by simpa [pairingLosers] using loser_mem)
        subst element
        let joined :=
          makeJoinOccurrence before labels
            (.pass source pairing.winner) pairing.loser
            pairing.destination pairing.winner
        have joined_mem :
            joined ∈
              operationJoinOccurrences before labels
                (.pass source matching) := by
          apply List.mem_map.mpr
          exact ⟨pairing, pairing_mem, rfl⟩
        have installed :=
          after_apply_eq_some_of_join step ledger joined_mem
        change
          after before labels ledger (.pass source matching)
              pairing.loser =
            some (EpisodeStart.ofJoin before joined) at installed
        rw [installed] at active
        have start_eq :
            EpisodeStart.ofJoin before joined = start :=
          Option.some.inj active
        subst start
        change PlacementAt next pairing.loser joined.destinationCreator
        exact placementAt_after_of_join step joined_mem
      · have old_active : ledger element = some start := by
          change
            installPassJoins before labels source ledger matching element =
              some start at active
          rw [installPassJoins_apply_of_not_mem
            before labels source ledger matching element loser_mem] at active
          exact active
        obtain ⟨blockId, block, found, member, creator_eq⟩ :=
          placement element start old_active
        cases step.2.1 with
        | pass source_found' valid_matching' blocks_eq values_eq =>
            rename_i sourceBlock'
            have sourceBlock_eq : sourceBlock' = sourceBlock := by
              rw [source_found] at source_found'
              exact (Option.some.inj source_found').symm
            subst sourceBlock'
            change before.blocks[blockId]? = some block at found
            change before.blocks[source]? = some sourceBlock at source_found
            by_cases ids_eq : blockId = source
            · subst blockId
              rw [source_found] at found
              have block_eq : sourceBlock = block :=
                Option.some.inj found
              subst block
              let nextBlock : Block n :=
                { sourceBlock with
                  passCount := sourceBlock.passCount + 1
                  elements := removeLosers sourceBlock.elements matching }
              refine
                ⟨source, nextBlock, ?_,
                  mem_removeLosers_of_mem_of_not_loser member loser_mem, by
                    simpa [nextBlock] using creator_eq⟩
              change next.blocks[source]? = some nextBlock
              rw [blocks_eq]
              unfold passBlocks
              rw [block?_insertAtDestinations_of_ne]
              · rw [List.getElem?_modify_eq, source_found]
                rfl
              · intro pairing pairing_mem
                exact
                  (valid_matching'.2.2.2.1 pairing pairing_mem).2.2.1
            · let sourceAfter : Block n :=
                { sourceBlock with
                  passCount := sourceBlock.passCount + 1
                  elements := removeLosers sourceBlock.elements matching }
              let sourceUpdated :=
                before.blocks.modify source fun _ => sourceAfter
              have source_updated_found :
                  sourceUpdated[blockId]? = some block := by
                rw [show sourceUpdated =
                  before.blocks.modify source (fun _ => sourceAfter) by rfl]
                rw [List.getElem?_modify_ne _ _ (Ne.symm ids_eq)]
                exact found
              obtain ⟨nextBlock, next_found, next_member,
                  next_creator⟩ :=
                placement_insertAtDestinations matching
                  source_updated_found member
              refine
                ⟨blockId, nextBlock, ?_, next_member,
                  next_creator.trans creator_eq⟩
              change next.blocks[blockId]? = some nextBlock
              rw [blocks_eq]
              simpa [passBlocks, sourceAfter, sourceUpdated] using next_found
  | split source prefixLength =>
      intro element start active
      obtain ⟨blockId, block, found, member, creator_eq⟩ :=
        placement element start (by simpa using active)
      cases step.2.1 with
      | split source_found shrinking prefix_le blocks_eq values_eq =>
          rename_i sourceBlock
          change before.blocks[blockId]? = some block at found
          change before.blocks[source]? = some sourceBlock at source_found
          by_cases ids_eq : blockId = source
          · subst blockId
            rw [source_found] at found
            have block_eq : sourceBlock = block :=
              Option.some.inj found
            subst block
            have pieces :
                element ∈ sourceBlock.elements.take prefixLength ∨
                  element ∈ sourceBlock.elements.drop prefixLength := by
              apply List.mem_append.mp
              rw [List.take_append_drop]
              exact member
            rcases pieces with left_mem | right_mem
            · let leftBlock : Block n :=
                { sourceBlock with
                  elements := sourceBlock.elements.take prefixLength }
              refine
                ⟨before.blocks.length, leftBlock, ?_, left_mem, by
                  simpa [leftBlock] using creator_eq⟩
              change next.blocks[before.blocks.length]? = some leftBlock
              simp [blocks_eq, splitBlocks, leftBlock]
            · let rightBlock : Block n :=
                { sourceBlock with
                  elements := sourceBlock.elements.drop prefixLength }
              refine
                ⟨before.blocks.length + 1, rightBlock, ?_, right_mem, by
                  simpa [rightBlock] using creator_eq⟩
              change next.blocks[before.blocks.length + 1]? =
                some rightBlock
              simp [blocks_eq, splitBlocks, rightBlock]
          · have blockId_lt : blockId < before.blocks.length :=
              (List.getElem?_eq_some_iff.mp found).1
            refine ⟨blockId, block, ?_, member, creator_eq⟩
            change next.blocks[blockId]? = some block
            rw [blocks_eq]
            unfold splitBlocks
            rw [List.getElem?_append_left (by simpa using blockId_lt)]
            rw [List.getElem?_modify_ne _ _ (Ne.symm ids_eq)]
            exact found
  | valueChange changed delta =>
      intro element start active
      obtain ⟨blockId, block, found, member, creator_eq⟩ :=
        placement element start (by simpa using active)
      cases step.2.1 with
      | decrease can_decrease blocks_eq values_eq =>
          refine ⟨blockId, block, ?_, member, creator_eq⟩
          simpa [State.block?, blocks_eq] using found
      | increase can_increase blocks_eq values_eq =>
          refine ⟨blockId, block, ?_, member, creator_eq⟩
          simpa [State.block?, blocks_eq] using found

/-- Frozen join-gap soundness is preserved by the deterministic ledger update. -/
theorem JoinSoundAt.after_step
    {n : ℕ} {params : Parameters}
    {before next : State n} {labels : RootLabels}
    {operation : Operation n} {ledger : EpisodeLedger n}
    (joinSound : JoinSoundAt ledger)
    (step : Step params before operation next) :
    JoinSoundAt (after before labels ledger operation) := by
  cases operation with
  | convert blockId =>
      simpa using joinSound
  | create creator =>
      simpa using joinSound
  | insert destination inserted =>
      intro element start active
      by_cases element_eq : element = inserted
      · subst element
        let joined :=
          makeJoinOccurrence before labels .insert inserted
            destination inserted
        have joined_mem :
            joined ∈
              operationJoinOccurrences before labels
                (.insert destination inserted) := by
          simp [joined]
        have installed :=
          after_apply_eq_some_of_join step ledger joined_mem
        change
          after before labels ledger (.insert destination inserted)
              inserted =
            some (EpisodeStart.ofJoin before joined) at installed
        rw [installed] at active
        have start_eq :
            EpisodeStart.ofJoin before joined = start :=
          Option.some.inj active
        subst start
        exact joinValid_of_mem_operationJoinOccurrences step joined_mem
      · apply joinSound element start
        simpa [after, element_eq] using active
  | delete source deleted =>
      intro element start active
      by_cases element_eq : element = deleted
      · subst element
        simp [after] at active
      · apply joinSound element start
        simpa [after, element_eq] using active
  | pass source matching =>
      intro element start active
      obtain ⟨sourceBlock, source_found, valid_matching⟩ :
          ∃ sourceBlock,
            before.block? source = some sourceBlock ∧
              MatchingValid params before source sourceBlock matching := by
        cases step.2.1 with
        | pass found valid_matching blocks_eq values_eq =>
            exact ⟨_, found, valid_matching⟩
      by_cases loser_mem : element ∈ pairingLosers matching
      · obtain ⟨pairing, pairing_mem, loser_eq⟩ :=
          List.mem_map.mp (by simpa [pairingLosers] using loser_mem)
        subst element
        let joined :=
          makeJoinOccurrence before labels
            (.pass source pairing.winner) pairing.loser
            pairing.destination pairing.winner
        have joined_mem :
            joined ∈
              operationJoinOccurrences before labels
                (.pass source matching) := by
          apply List.mem_map.mpr
          exact ⟨pairing, pairing_mem, rfl⟩
        have installed :=
          after_apply_eq_some_of_join step ledger joined_mem
        change
          after before labels ledger (.pass source matching)
              pairing.loser =
            some (EpisodeStart.ofJoin before joined) at installed
        rw [installed] at active
        have start_eq :
            EpisodeStart.ofJoin before joined = start :=
          Option.some.inj active
        subst start
        exact joinValid_of_mem_operationJoinOccurrences step joined_mem
      · apply joinSound element start
        change
          installPassJoins before labels source ledger matching element =
            some start at active
        rw [installPassJoins_apply_of_not_mem
          before labels source ledger matching element loser_mem] at active
        exact active
  | split source prefixLength =>
      simpa using joinSound
  | valueChange changed delta =>
      simpa using joinSound

/-- Exactness is the inductive active-episode invariant. -/
theorem ExactAt.after_step
    {n : ℕ} {params : Parameters}
    {before next : State n} {labels : RootLabels}
    {operation : Operation n} {ledger : EpisodeLedger n}
    (exact : ExactAt before labels ledger)
    (step : Step params before operation next)
    (aligned : labels.length = before.blocks.length) :
    ExactAt next (RootLabels.after labels operation)
      (after before labels ledger operation) where
  sound := exact.sound.after_step step aligned
  complete := exact.complete.after_step step aligned
  placement := exact.placement.after_step step
  joinSound := exact.joinSound.after_step step

/-- The empty ledger exactly tracks an interface initial state. -/
theorem ExactAt.initial
    {n : ℕ} {params : Parameters} {state : State n}
    (initial : state.Initial params) :
    ExactAt state [] (empty : EpisodeLedger n) := by
  refine
    { sound := ?_
      complete := ?_
      placement := ?_
      joinSound := ?_ }
  · intro element start active
    simp [empty] at active
  · intro element assigned
    unfold State.allElements at assigned
    rw [initial.2] at assigned
    simp at assigned
  · intro element start active
    simp [empty] at active
  · intro element start active
    simp [empty] at active

/-- A physical placement has a unique block ID in a valid state. -/
theorem PlacementAt.exists_unique_blockId
    {n : ℕ} {params : Parameters} {state : State n}
    (valid : state.Valid params) {element creator : Element n}
    (placement : PlacementAt state element creator) :
    ∃ blockId block,
      state.block? blockId = some block ∧
        element ∈ block.elements ∧
        block.creator = creator ∧
        ∀ otherId otherBlock,
          state.block? otherId = some otherBlock →
          element ∈ otherBlock.elements →
          otherId = blockId := by
  obtain ⟨blockId, block, found, member, creator_eq⟩ := placement
  refine
    ⟨blockId, block, found, member, creator_eq, ?_⟩
  intro otherId otherBlock other_found other_member
  exact
    valid.blockId_eq_of_element_mem other_found other_member
      found member

/-- Complete current-start data for both endpoints of a legal pass pairing. -/
structure PassPairingStartsAt {n : ℕ}
    (state : State n) (labels : RootLabels) (ledger : EpisodeLedger n)
    (source : BlockId) (pairing : Pairing n) : Type where
  sourceBlock : Block n
  sourceRoot : RootId
  winnerStart : EpisodeStart n
  loserStart : EpisodeStart n
  sourceFound : state.block? source = some sourceBlock
  sourceRootFound : RootLabels.root? labels source = some sourceRoot
  winnerActive : ledger pairing.winner = some winnerStart
  loserActive : ledger pairing.loser = some loserStart
  winnerElement : winnerStart.join.element = pairing.winner
  loserElement : loserStart.join.element = pairing.loser
  winnerRoot : winnerStart.join.destinationRoot = sourceRoot
  loserRoot : loserStart.join.destinationRoot = sourceRoot
  winnerCreator :
    winnerStart.join.destinationCreator = sourceBlock.creator
  loserCreator :
    loserStart.join.destinationCreator = sourceBlock.creator
  winnerPlacement :
    PlacementAt state pairing.winner
      winnerStart.join.destinationCreator
  loserPlacement :
    PlacementAt state pairing.loser
      loserStart.join.destinationCreator
  winnerJoinValid : winnerStart.JoinValid
  loserJoinValid : loserStart.JoinValid

/--
Exactness supplies the two old starts of every legal pass pairing, including
their common current source creator and frozen join-gap facts.
-/
theorem ExactAt.pass_pairing_starts_nonempty
    {n : ℕ} {params : Parameters}
    {before next : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (exact : ExactAt before labels ledger)
    (step : Step params before (.pass source matching) next)
    (aligned : labels.length = before.blocks.length)
    (pairing_mem : pairing ∈ matching) :
    Nonempty (PassPairingStartsAt before labels ledger source pairing) := by
  obtain ⟨sourceBlock, source_found, valid_matching⟩ :
      ∃ sourceBlock,
        before.block? source = some sourceBlock ∧
          MatchingValid params before source sourceBlock matching := by
    cases step.2.1 with
    | pass found valid_matching blocks_eq values_eq =>
        exact ⟨_, found, valid_matching⟩
  have pairing_valid :=
    valid_matching.2.2.2.1 pairing pairing_mem
  have winner_mem : pairing.winner ∈ sourceBlock.elements :=
    pairing_valid.1.first_mem
  have loser_mem : pairing.loser ∈ sourceBlock.elements :=
    pairing_valid.1.second_mem
  obtain ⟨sourceRoot, source_root_found⟩ :=
    root_exists_of_aligned_block_found aligned source_found
  have winner_payload :
      pairing.winner ∈
        lineageElements before labels sourceRoot := by
    apply
      block_elements_subset_lineageElementsOf aligned
        source_found source_root_found
    simpa using winner_mem
  have loser_payload :
      pairing.loser ∈
        lineageElements before labels sourceRoot := by
    apply
      block_elements_subset_lineageElementsOf aligned
        source_found source_root_found
    simpa using loser_mem
  have winner_assigned : pairing.winner ∈ before.allElements :=
    (mem_allElements_iff_exists_lineageElements aligned).mpr
      ⟨sourceRoot, winner_payload⟩
  have loser_assigned : pairing.loser ∈ before.allElements :=
    (mem_allElements_iff_exists_lineageElements aligned).mpr
      ⟨sourceRoot, loser_payload⟩
  obtain ⟨winnerStart, winner_active⟩ :=
    exact.complete pairing.winner winner_assigned
  obtain ⟨loserStart, loser_active⟩ :=
    exact.complete pairing.loser loser_assigned
  have winner_sound :=
    exact.sound pairing.winner winnerStart winner_active
  have loser_sound :=
    exact.sound pairing.loser loserStart loser_active
  have winner_root :
      winnerStart.join.destinationRoot = sourceRoot :=
    step.1.lineage_root_unique aligned winner_sound.2 winner_payload
  have loser_root :
      loserStart.join.destinationRoot = sourceRoot :=
    step.1.lineage_root_unique aligned loser_sound.2 loser_payload
  have winner_placement :=
    exact.placement pairing.winner winnerStart winner_active
  have loser_placement :=
    exact.placement pairing.loser loserStart loser_active
  have winner_placement_full := winner_placement
  have loser_placement_full := loser_placement
  obtain ⟨winnerId, winnerBlock, winner_found,
      winner_block_mem, winner_creator⟩ :=
    winner_placement
  have winner_id_eq : winnerId = source :=
    step.1.blockId_eq_of_element_mem winner_found winner_block_mem
      source_found winner_mem
  subst winnerId
  rw [source_found] at winner_found
  have source_winner_block : sourceBlock = winnerBlock :=
    Option.some.inj winner_found
  have winner_creator_eq :
      winnerStart.join.destinationCreator = sourceBlock.creator := by
    rw [source_winner_block]
    exact winner_creator.symm
  obtain ⟨loserId, loserBlock, loser_found,
      loser_block_mem, loser_creator⟩ :=
    loser_placement
  have loser_id_eq : loserId = source :=
    step.1.blockId_eq_of_element_mem loser_found loser_block_mem
      source_found loser_mem
  subst loserId
  rw [source_found] at loser_found
  have source_loser_block : sourceBlock = loserBlock :=
    Option.some.inj loser_found
  have loser_creator_eq :
      loserStart.join.destinationCreator = sourceBlock.creator := by
    rw [source_loser_block]
    exact loser_creator.symm
  constructor
  exact
    { sourceBlock := sourceBlock
      sourceRoot := sourceRoot
      winnerStart := winnerStart
      loserStart := loserStart
      sourceFound := source_found
      sourceRootFound := source_root_found
      winnerActive := winner_active
      loserActive := loser_active
      winnerElement := winner_sound.1
      loserElement := loser_sound.1
      winnerRoot := winner_root
      loserRoot := loser_root
      winnerCreator := winner_creator_eq
      loserCreator := loser_creator_eq
      winnerPlacement := winner_placement_full
      loserPlacement := loser_placement_full
      winnerJoinValid :=
        exact.joinSound pairing.winner winnerStart winner_active
      loserJoinValid :=
        exact.joinSound pairing.loser loserStart loser_active }

/-- Canonical choice of the exact current starts for one pass pairing. -/
noncomputable def ExactAt.pass_pairing_starts
    {n : ℕ} {params : Parameters}
    {before next : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (exact : ExactAt before labels ledger)
    (step : Step params before (.pass source matching) next)
    (aligned : labels.length = before.blocks.length)
    (pairing_mem : pairing ∈ matching) :
    PassPairingStartsAt before labels ledger source pairing :=
  Classical.choice
    (exact.pass_pairing_starts_nonempty step aligned pairing_mem)

/-- A dependent snapshot packages one pairing with its exact two old starts. -/
abbrev PassPairingSnapshotAt {n : ℕ}
    (state : State n) (labels : RootLabels) (ledger : EpisodeLedger n)
    (source : BlockId) :=
  Σ pairing : Pairing n,
    PassPairingStartsAt state labels ledger source pairing

/-- Canonical pairing-aligned snapshot list for one complete pass. -/
noncomputable def ExactAt.pass_pairing_snapshots
    {n : ℕ} {params : Parameters}
    {before next : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)}
    (exact : ExactAt before labels ledger)
    (step : Step params before (.pass source matching) next)
    (aligned : labels.length = before.blocks.length) :
    List (PassPairingSnapshotAt before labels ledger source) :=
  matching.attach.map fun pairing =>
    ⟨pairing.1,
      exact.pass_pairing_starts step aligned pairing.2⟩

/-- The snapshot list is pointwise aligned with the original matching. -/
theorem ExactAt.pass_pairing_snapshots_forall₂
    {n : ℕ} {params : Parameters}
    {before next : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)}
    (exact : ExactAt before labels ledger)
    (step : Step params before (.pass source matching) next)
    (aligned : labels.length = before.blocks.length) :
    List.Forall₂
      (fun pairing snapshot => snapshot.1 = pairing)
      matching (exact.pass_pairing_snapshots step aligned) := by
  let snapshots := exact.pass_pairing_snapshots step aligned
  have firsts_eq :
      snapshots.map (fun snapshot => snapshot.1) = matching := by
    simp [snapshots, ExactAt.pass_pairing_snapshots]
  change
    List.Forall₂
      (fun pairing snapshot => snapshot.1 = pairing)
      matching snapshots
  rw [← firsts_eq]
  induction snapshots with
  | nil =>
      exact .nil
  | cons snapshot snapshots ih =>
      exact .cons rfl ih

/-- In particular, one exact snapshot is produced for every pass pairing. -/
@[simp]
theorem ExactAt.length_pass_pairing_snapshots
    {n : ℕ} {params : Parameters}
    {before next : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)}
    (exact : ExactAt before labels ledger)
    (step : Step params before (.pass source matching) next)
    (aligned : labels.length = before.blocks.length) :
    (exact.pass_pairing_snapshots step aligned).length =
      matching.length := by
  simp [ExactAt.pass_pairing_snapshots]

/-- Existential list-level API, convenient for downstream extraction proofs. -/
theorem ExactAt.exists_pass_pairing_snapshots
    {n : ℕ} {params : Parameters}
    {before next : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)}
    (exact : ExactAt before labels ledger)
    (step : Step params before (.pass source matching) next)
    (aligned : labels.length = before.blocks.length) :
    ∃ snapshots : List
        (PassPairingSnapshotAt before labels ledger source),
      List.Forall₂
          (fun pairing snapshot => snapshot.1 = pairing)
          matching snapshots ∧
        snapshots.length = matching.length :=
  ⟨exact.pass_pairing_snapshots step aligned,
    exact.pass_pairing_snapshots_forall₂ step aligned,
    exact.length_pass_pairing_snapshots step aligned⟩

end EpisodeLedger

/-- One completed block-residence episode. -/
structure ClosedEpisode (n : ℕ) where
  start : EpisodeStart n
  finish : LeaveOccurrence n
  deriving DecidableEq, Repr

namespace ClosedEpisode

/--
The episode closes on the same element and lineage root on which it started.
The destination block itself may have split in the meantime.
-/
def Coherent {n : ℕ} (episode : ClosedEpisode n) : Prop :=
  episode.start.join.element = episode.finish.element ∧
    episode.start.join.destinationRoot = episode.finish.sourceRoot

end ClosedEpisode

/-- Close exactly the active episodes selected by this operation's leaves. -/
def operationClosedEpisodes {n : ℕ}
    (before : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (operation : Operation n) :
    List (ClosedEpisode n) :=
  (operationLeaveOccurrences before labels operation).filterMap fun finish =>
    (ledger finish.element).map fun start =>
      { start := start, finish := finish }

/-- An actual leave with an active start contributes its exact closed episode. -/
theorem mem_operationClosedEpisodes_of_active
    {n : ℕ} {before : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {operation : Operation n}
    {finish : LeaveOccurrence n} {start : EpisodeStart n}
    (finish_mem :
      finish ∈ operationLeaveOccurrences before labels operation)
    (active : ledger finish.element = some start) :
    ({ start := start, finish := finish } : ClosedEpisode n) ∈
      operationClosedEpisodes before labels ledger operation := by
  apply List.mem_filterMap.mpr
  exact
    ⟨finish, finish_mem, by
      simp [active]⟩

/--
Exact pass transition for one pairing.

The old active episode closes at the shrinking source, while a new episode
opens at the actual destination.  The leave value and the new join value are
identical because both are sampled from the same pass pre-state.
-/
theorem pass_transition
    {n : ℕ} {params : Parameters}
    {before next : State n} {labels : RootLabels}
    {source : BlockId} {matching : List (Pairing n)}
    (step : Step params before (.pass source matching) next)
    (aligned : labels.length = before.blocks.length)
    (ledger : EpisodeLedger n)
    (sound : EpisodeLedger.SoundAt before labels ledger)
    {pairing : Pairing n} (pairing_mem : pairing ∈ matching)
    {start : EpisodeStart n}
    (active : ledger pairing.loser = some start) :
    ∃ (finish : LeaveOccurrence n) (joined : JoinOccurrence n),
      finish ∈
          operationLeaveOccurrences before labels
            (.pass source matching) ∧
        joined ∈
          operationJoinOccurrences before labels
            (.pass source matching) ∧
        ({ start := start, finish := finish } : ClosedEpisode n) ∈
          operationClosedEpisodes before labels ledger
            (.pass source matching) ∧
        ClosedEpisode.Coherent
          ({ start := start, finish := finish } : ClosedEpisode n) ∧
        EpisodeLedger.after before labels ledger
            (.pass source matching) pairing.loser =
          some (EpisodeStart.ofJoin before joined) ∧
        (EpisodeStart.ofJoin before joined).creatorValueAtJoin =
          before.value joined.destinationCreator ∧
        joined.destinationCreator = pairing.winner ∧
        (EpisodeStart.ofJoin before joined).creatorValueAtJoin =
          before.value pairing.winner ∧
        (EpisodeStart.ofJoin before joined).JoinValid ∧
        finish.valueAtLeave = joined.valueAtJoin ∧
        finish.reason =
          .pass pairing.destination pairing.winner ∧
        joined.origin = .pass source pairing.winner ∧
        finish.source = source ∧
        joined.destination = pairing.destination := by
  let finish :=
    makeLeaveOccurrence before labels
      (.pass pairing.destination pairing.winner)
      pairing.loser source pairing.winner
  let joined :=
    makeJoinOccurrence before labels
      (.pass source pairing.winner) pairing.loser
      pairing.destination pairing.winner
  have finish_mem :
      finish ∈
        operationLeaveOccurrences before labels
          (.pass source matching) := by
    apply List.mem_map.mpr
    exact ⟨pairing, pairing_mem, rfl⟩
  have joined_mem :
      joined ∈
        operationJoinOccurrences before labels
          (.pass source matching) := by
    apply List.mem_map.mpr
    exact ⟨pairing, pairing_mem, rfl⟩
  have active_finish : ledger finish.element = some start := by
    simpa [finish, makeLeaveOccurrence] using active
  have closed_mem :
      ({ start := start, finish := finish } : ClosedEpisode n) ∈
        operationClosedEpisodes before labels ledger
          (.pass source matching) :=
    mem_operationClosedEpisodes_of_active finish_mem active_finish
  obtain ⟨sourceBlock, source_found, valid_matching⟩ :
      ∃ sourceBlock,
        before.block? source = some sourceBlock ∧
          MatchingValid params before source sourceBlock matching := by
    cases step.2.1 with
    | pass found valid_matching blocks_eq values_eq =>
        exact ⟨_, found, valid_matching⟩
  obtain ⟨sourceRoot, root_found⟩ :=
    root_exists_of_aligned_block_found aligned source_found
  have source_payload :
      pairing.loser ∈
        lineageElements before labels sourceRoot := by
    apply
      block_elements_subset_lineageElementsOf aligned
        source_found root_found
    simpa using valid_matching.loser_mem pairing_mem
  have old_sound := sound pairing.loser start active
  have roots_eq :
      start.join.destinationRoot = sourceRoot :=
    step.1.lineage_root_unique aligned old_sound.2 source_payload
  have coherent :
      ClosedEpisode.Coherent
        ({ start := start, finish := finish } : ClosedEpisode n) := by
    constructor
    · simpa [finish, makeLeaveOccurrence] using old_sound.1
    · simpa [finish, makeLeaveOccurrence, source_found, root_found] using
        roots_eq
  have installed :
      EpisodeLedger.after before labels ledger
          (.pass source matching) pairing.loser =
        some (EpisodeStart.ofJoin before joined) :=
    EpisodeLedger.after_apply_eq_some_of_join step ledger joined_mem
  have pairing_valid :=
    valid_matching.2.2.2.1 pairing pairing_mem
  obtain ⟨destinationBlock, destination_found,
      destination_growing, destination_creator⟩ :=
    pairing_valid.2.2.2
  have joined_creator :
      joined.destinationCreator = pairing.winner := by
    simp [joined, makeJoinOccurrence, destination_found,
      destination_creator]
  have creator_snapshot :
      (EpisodeStart.ofJoin before joined).creatorValueAtJoin =
        before.value pairing.winner := by
    rw [EpisodeStart.ofJoin_creatorValueAtJoin, joined_creator]
  have joined_valid :
      (EpisodeStart.ofJoin before joined).JoinValid :=
    joinValid_of_mem_operationJoinOccurrences step joined_mem
  refine
    ⟨finish, joined, finish_mem, joined_mem, closed_mem, coherent,
      installed, rfl, joined_creator, creator_snapshot, joined_valid,
      ?_, rfl, rfl, rfl, rfl⟩
  rfl

/-- Exact delete transition: close the active episode and leave none open. -/
theorem delete_transition
    {n : ℕ} {params : Parameters}
    {before next : State n} {labels : RootLabels}
    {source : BlockId} {element : Element n}
    (step : Step params before (.delete source element) next)
    (aligned : labels.length = before.blocks.length)
    (ledger : EpisodeLedger n)
    (sound : EpisodeLedger.SoundAt before labels ledger)
    {start : EpisodeStart n}
    (active : ledger element = some start) :
    ∃ finish : LeaveOccurrence n,
      finish ∈
          operationLeaveOccurrences before labels
            (.delete source element) ∧
        ({ start := start, finish := finish } : ClosedEpisode n) ∈
          operationClosedEpisodes before labels ledger
            (.delete source element) ∧
        ClosedEpisode.Coherent
          ({ start := start, finish := finish } : ClosedEpisode n) ∧
        EpisodeLedger.after before labels ledger
            (.delete source element) element = none ∧
        finish.reason = .delete ∧
        finish.source = source ∧
        finish.element = element := by
  let finish :=
    makeLeaveOccurrence before labels .delete element source element
  have finish_mem :
      finish ∈
        operationLeaveOccurrences before labels
          (.delete source element) := by
    simp [finish]
  have active_finish : ledger finish.element = some start := by
    simpa [finish, makeLeaveOccurrence] using active
  have closed_mem :
      ({ start := start, finish := finish } : ClosedEpisode n) ∈
        operationClosedEpisodes before labels ledger
          (.delete source element) :=
    mem_operationClosedEpisodes_of_active finish_mem active_finish
  obtain ⟨sourceBlock, source_found, element_present⟩ :
      ∃ sourceBlock,
        before.block? source = some sourceBlock ∧
          element ∈ sourceBlock.elements := by
    cases step.2.1 with
    | delete found shrinking present blocks_eq values_eq =>
        exact ⟨_, found, present⟩
  obtain ⟨sourceRoot, root_found⟩ :=
    root_exists_of_aligned_block_found aligned source_found
  have source_payload :
      element ∈ lineageElements before labels sourceRoot := by
    apply
      block_elements_subset_lineageElementsOf aligned
        source_found root_found
    simpa using element_present
  have old_sound := sound element start active
  have roots_eq :
      start.join.destinationRoot = sourceRoot :=
    step.1.lineage_root_unique aligned old_sound.2 source_payload
  have coherent :
      ClosedEpisode.Coherent
        ({ start := start, finish := finish } : ClosedEpisode n) := by
    constructor
    · simpa [finish, makeLeaveOccurrence] using old_sound.1
    · simpa [finish, makeLeaveOccurrence, source_found, root_found] using
        roots_eq
  refine
    ⟨finish, finish_mem, closed_mem, coherent, ?_, rfl, rfl, rfl⟩
  simp [EpisodeLedger.after]

/-- Total number of element episodes closed by an operation list. -/
def totalLeaves {n : ℕ} (operations : List (Operation n)) : ℕ :=
  (operations.map Operation.leaveCount).sum

/-- Membership in a found block implies membership in the state's payload. -/
theorem mem_allElements_of_block_found
    {n : ℕ} {state : State n} {blockId : BlockId}
    {block : Block n} {element : Element n}
    (found : state.block? blockId = some block)
    (member : element ∈ block.elements) :
    element ∈ state.allElements := by
  change element ∈ state.blocks.flatMap Block.elements
  apply List.mem_flatMap.mpr
  refine ⟨block, ?_, member⟩
  exact List.mem_iff_getElem?.mpr ⟨blockId, found⟩

/-- Every legal leave concerns an element assigned in its exact pre-state. -/
theorem element_mem_allElements_of_mem_operationLeaveOccurrences
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n} {finish : LeaveOccurrence n}
    (step : Step params before operation after)
    (member :
      finish ∈ operationLeaveOccurrences before labels operation) :
    finish.element ∈ before.allElements := by
  cases operation with
  | convert blockId =>
      simp at member
  | create creator =>
      simp at member
  | insert destination element =>
      simp at member
  | delete source element =>
      simp only [operationLeaveOccurrences_delete,
        List.mem_singleton] at member
      subst finish
      cases step.2.1 with
      | delete source_found shrinking present blocks_eq values_eq =>
          simpa [makeLeaveOccurrence] using
            mem_allElements_of_block_found source_found present
  | pass source matching =>
      obtain ⟨pairing, pairing_mem, finish_eq⟩ :=
        List.mem_map.mp member
      subst finish
      cases step.2.1 with
      | pass source_found valid_matching blocks_eq values_eq =>
          simpa [makeLeaveOccurrence] using
            mem_allElements_of_block_found source_found
              (valid_matching.loser_mem pairing_mem)
  | split source prefixLength =>
      simp at member
  | valueChange element delta =>
      simp at member

/-- A `filterMap` has full length when its function succeeds everywhere. -/
theorem length_filterMap_eq_of_forall_some
    {α β : Type*} (items : List α) (f : α → Option β)
    (success : ∀ item ∈ items, ∃ output, f item = some output) :
    (items.filterMap f).length = items.length := by
  induction items with
  | nil =>
      rfl
  | cons item items ih =>
      obtain ⟨output, output_eq⟩ :=
        success item (by simp)
      have tail_success :
          ∀ tailItem ∈ items, ∃ output, f tailItem = some output := by
        intro tailItem tail_mem
        exact success tailItem (by simp [tail_mem])
      simp [output_eq, ih tail_success]

/-- Completeness makes operation-level closing lossless. -/
theorem length_operationClosedEpisodes
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {operation : Operation n}
    (complete : EpisodeLedger.CompleteAt before ledger)
    (step : Step params before operation after) :
    (operationClosedEpisodes before labels ledger operation).length =
      (operationLeaveOccurrences before labels operation).length := by
  unfold operationClosedEpisodes
  apply length_filterMap_eq_of_forall_some
  intro finish finish_mem
  obtain ⟨start, active⟩ :=
    complete finish.element
      (element_mem_allElements_of_mem_operationLeaveOccurrences
        step finish_mem)
  exact
    ⟨({ start := start, finish := finish } : ClosedEpisode n), by
      simp [active]⟩

/-- Every episode closed by an aligned exact step has matching element/root. -/
theorem coherent_of_mem_operationClosedEpisodes
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {operation : Operation n}
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    (sound : EpisodeLedger.SoundAt before labels ledger)
    {episode : ClosedEpisode n}
    (member :
      episode ∈
        operationClosedEpisodes before labels ledger operation) :
    episode.Coherent := by
  obtain ⟨finish, finish_mem, mapped⟩ :=
    List.mem_filterMap.mp member
  cases active_eq : ledger finish.element with
  | none =>
      simp [active_eq] at mapped
  | some start =>
      have episode_eq :
          ({ start := start, finish := finish } : ClosedEpisode n) =
            episode := by
        simpa [active_eq] using mapped
      subst episode
      cases operation with
      | convert blockId =>
          simp at finish_mem
      | create creator =>
          simp at finish_mem
      | insert destination element =>
          simp at finish_mem
      | delete source element =>
          simp only [operationLeaveOccurrences_delete,
            List.mem_singleton] at finish_mem
          subst finish
          obtain ⟨sourceBlock, source_found, element_present⟩ :
              ∃ sourceBlock,
                before.block? source = some sourceBlock ∧
                  element ∈ sourceBlock.elements := by
            cases step.2.1 with
            | delete found shrinking present blocks_eq values_eq =>
                exact ⟨_, found, present⟩
          obtain ⟨sourceRoot, root_found⟩ :=
            root_exists_of_aligned_block_found aligned source_found
          have source_payload :
              element ∈
                lineageElements before labels sourceRoot := by
            apply
              block_elements_subset_lineageElementsOf aligned
                source_found root_found
            simpa using element_present
          have active :
              ledger element = some start := by
            simpa [makeLeaveOccurrence] using active_eq
          have old_sound := sound element start active
          have roots_eq :
              start.join.destinationRoot = sourceRoot :=
            step.1.lineage_root_unique aligned old_sound.2
              source_payload
          constructor
          · simpa [makeLeaveOccurrence] using old_sound.1
          · simpa [makeLeaveOccurrence, source_found, root_found] using
              roots_eq
      | pass source matching =>
          obtain ⟨pairing, pairing_mem, finish_eq⟩ :=
            List.mem_map.mp finish_mem
          subst finish
          obtain ⟨sourceBlock, source_found, valid_matching⟩ :
              ∃ sourceBlock,
                before.block? source = some sourceBlock ∧
                  MatchingValid params before source sourceBlock
                    matching := by
            cases step.2.1 with
            | pass found valid_matching blocks_eq values_eq =>
                exact ⟨_, found, valid_matching⟩
          obtain ⟨sourceRoot, root_found⟩ :=
            root_exists_of_aligned_block_found aligned source_found
          have source_payload :
              pairing.loser ∈
                lineageElements before labels sourceRoot := by
            apply
              block_elements_subset_lineageElementsOf aligned
                source_found root_found
            simpa using valid_matching.loser_mem pairing_mem
          have active :
              ledger pairing.loser = some start := by
            simpa [makeLeaveOccurrence] using active_eq
          have old_sound :=
            sound pairing.loser start active
          have roots_eq :
              start.join.destinationRoot = sourceRoot :=
            step.1.lineage_root_unique aligned old_sound.2
              source_payload
          constructor
          · simpa [makeLeaveOccurrence] using old_sound.1
          · simpa [makeLeaveOccurrence, source_found, root_found] using
              roots_eq
      | split source prefixLength =>
          simp at finish_mem
      | valueChange element delta =>
          simp at finish_mem

/--
A complete history carrying deterministic joins, leaves, closed episodes, and
the active ledger at every pre-state.
-/
inductive LifetimeHistory {n : ℕ} (params : Parameters) :
    State n → RootLabels → EpisodeLedger n →
      List (Operation n) → List (JoinOccurrence n) →
      List (LeaveOccurrence n) → List (ClosedEpisode n) →
      State n → RootLabels → EpisodeLedger n → Prop
  | nil {state : State n} {labels : RootLabels}
      {ledger : EpisodeLedger n}
      (valid : state.Valid params) :
      LifetimeHistory params state labels ledger
        [] [] [] [] state labels ledger
  | cons {before middle final : State n}
      {beforeLabels finalLabels : RootLabels}
      {beforeLedger finalLedger : EpisodeLedger n}
      {operation : Operation n} {operations : List (Operation n)}
      {tailJoins : List (JoinOccurrence n)}
      {tailLeaves : List (LeaveOccurrence n)}
      {tailClosed : List (ClosedEpisode n)}
      (head : Step params before operation middle)
      (tail :
        LifetimeHistory params middle
          (RootLabels.after beforeLabels operation)
          (EpisodeLedger.after before beforeLabels beforeLedger operation)
          operations tailJoins tailLeaves tailClosed
          final finalLabels finalLedger) :
      LifetimeHistory params before beforeLabels beforeLedger
        (operation :: operations)
        (operationJoinOccurrences before beforeLabels operation ++
          tailJoins)
        (operationLeaveOccurrences before beforeLabels operation ++
          tailLeaves)
        (operationClosedEpisodes before beforeLabels beforeLedger operation ++
          tailClosed)
        final finalLabels finalLedger

namespace LifetimeHistory

/-- Forgetting leave/ledger annotations recovers the exact join history. -/
theorem erase
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history :
      LifetimeHistory params initial initialLabels initialLedger
        operations joins leaves closed final finalLabels finalLedger) :
    JoinHistory params initial initialLabels operations joins
      final finalLabels := by
  induction history with
  | nil valid =>
      exact .nil valid
  | cons head tail ih =>
      exact .cons head ih

/-- Every join history has a deterministic lifetime annotation from any ledger. -/
theorem lift
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    (history :
      JoinHistory params initial initialLabels operations joins
        final finalLabels)
    (initialLedger : EpisodeLedger n) :
    ∃ finalLedger leaves closed,
      LifetimeHistory params initial initialLabels initialLedger
        operations joins leaves closed final finalLabels finalLedger := by
  induction history generalizing initialLedger with
  | nil valid =>
      exact ⟨initialLedger, [], [], .nil valid⟩
  | @cons before middle final beforeLabels finalLabels
      operation operations tailJoins head tail ih =>
      obtain ⟨finalLedger, tailLeaves, tailClosed, liftedTail⟩ :=
        ih (EpisodeLedger.after before beforeLabels initialLedger operation)
      exact
        ⟨finalLedger,
          operationLeaveOccurrences before beforeLabels operation ++
            tailLeaves,
          operationClosedEpisodes before beforeLabels initialLedger
              operation ++
            tailClosed,
          .cons head liftedTail⟩

/-- Label alignment is preserved at the endpoint. -/
theorem labels_length
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history :
      LifetimeHistory params initial initialLabels initialLedger
        operations joins leaves closed final finalLabels finalLedger)
    (aligned : initialLabels.length = initial.blocks.length) :
    finalLabels.length = final.blocks.length :=
  history.erase.labels_length aligned

/-- Exact active-ledger invariants telescope through a complete history. -/
theorem exact_final
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history :
      LifetimeHistory params initial initialLabels initialLedger
        operations joins leaves closed final finalLabels finalLedger)
    (aligned : initialLabels.length = initial.blocks.length)
    (exact :
      EpisodeLedger.ExactAt initial initialLabels initialLedger) :
    EpisodeLedger.ExactAt final finalLabels finalLedger := by
  induction history with
  | nil valid =>
      exact exact
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger operation operations tailJoins tailLeaves tailClosed
      head tail ih =>
      have middle_aligned :
          (RootLabels.after beforeLabels operation).length =
            middle.blocks.length :=
        (HistoryStep.mk head rfl).labels_length aligned
      have middle_exact :=
        exact.after_step head aligned
      exact ih middle_aligned middle_exact

/-- The global leave list has exactly the operation-prescribed length. -/
theorem leaves_length
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history :
      LifetimeHistory params initial initialLabels initialLedger
        operations joins leaves closed final finalLabels finalLedger) :
    leaves.length = totalLeaves operations := by
  induction history with
  | nil valid =>
      rfl
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger operation operations tailJoins tailLeaves tailClosed
      head tail ih =>
      simp only [List.length_append, length_operationLeaveOccurrences]
      rw [ih]
      simp [totalLeaves]

/--
Starting from an exact ledger, no legal leave is dropped while closing
episodes, globally as well as one step at a time.
-/
theorem closed_length_eq_leaves
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history :
      LifetimeHistory params initial initialLabels initialLedger
        operations joins leaves closed final finalLabels finalLedger)
    (aligned : initialLabels.length = initial.blocks.length)
    (exact :
      EpisodeLedger.ExactAt initial initialLabels initialLedger) :
    closed.length = leaves.length := by
  induction history with
  | nil valid =>
      rfl
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger operation operations tailJoins tailLeaves tailClosed
      head tail ih =>
      have head_length :=
        length_operationClosedEpisodes (labels := beforeLabels)
          exact.complete head
      have middle_aligned :
          (RootLabels.after beforeLabels operation).length =
            middle.blocks.length :=
        (HistoryStep.mk head rfl).labels_length aligned
      have middle_exact :=
        exact.after_step head aligned
      have tail_length :=
        ih middle_aligned middle_exact
      simp only [List.length_append]
      rw [head_length, tail_length]

/-- Exact histories close precisely `totalLeaves operations` episodes. -/
theorem closed_length
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history :
      LifetimeHistory params initial initialLabels initialLedger
        operations joins leaves closed final finalLabels finalLedger)
    (aligned : initialLabels.length = initial.blocks.length)
    (exact :
      EpisodeLedger.ExactAt initial initialLabels initialLedger) :
    closed.length = totalLeaves operations := by
  rw [history.closed_length_eq_leaves aligned exact]
  exact history.leaves_length

/-- Every globally recorded closed episode is coherent. -/
theorem closed_coherent
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history :
      LifetimeHistory params initial initialLabels initialLedger
        operations joins leaves closed final finalLabels finalLedger)
    (aligned : initialLabels.length = initial.blocks.length)
    (exact :
      EpisodeLedger.ExactAt initial initialLabels initialLedger)
    {episode : ClosedEpisode n} (member : episode ∈ closed) :
    episode.Coherent := by
  induction history with
  | nil valid =>
      simp at member
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger operation operations tailJoins tailLeaves tailClosed
      head tail ih =>
      rcases List.mem_append.mp member with head_member | tail_member
      · exact
          coherent_of_mem_operationClosedEpisodes
            head aligned exact.sound head_member
      · have middle_aligned :
            (RootLabels.after beforeLabels operation).length =
              middle.blocks.length :=
          (HistoryStep.mk head rfl).labels_length aligned
        have middle_exact :=
          exact.after_step head aligned
        exact ih middle_aligned middle_exact tail_member

/--
Every global closed episode exposes the exact aligned pre-step and exact
ledger at which it closed.
-/
theorem closed_step_snapshot
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history :
      LifetimeHistory params initial initialLabels initialLedger
        operations joins leaves closed final finalLabels finalLedger)
    (aligned : initialLabels.length = initial.blocks.length)
    (exact :
      EpisodeLedger.ExactAt initial initialLabels initialLedger)
    {episode : ClosedEpisode n} (member : episode ∈ closed) :
    ∃ (before after : State n) (labels : RootLabels)
        (ledger : EpisodeLedger n) (operation : Operation n),
      Step params before operation after ∧
        labels.length = before.blocks.length ∧
        EpisodeLedger.ExactAt before labels ledger ∧
        episode ∈
          operationClosedEpisodes before labels ledger operation := by
  induction history with
  | nil valid =>
      simp at member
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger operation operations tailJoins tailLeaves tailClosed
      head tail ih =>
      rcases List.mem_append.mp member with head_member | tail_member
      · exact
          ⟨before, middle, beforeLabels, beforeLedger, operation,
            head, aligned, exact, head_member⟩
      · have middle_aligned :
            (RootLabels.after beforeLabels operation).length =
              middle.blocks.length :=
          (HistoryStep.mk head rfl).labels_length aligned
        have middle_exact :=
          exact.after_step head aligned
        exact ih middle_aligned middle_exact tail_member

/--
Every ordinary trace from an interface initial state has a canonical exact
lifetime history with aligned endpoint, exact ledger, and exact list counts.
-/
theorem lift_initial
    {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (initialState : initial.Initial params)
    (trace : Trace params initial operations final) :
    ∃ finalLabels finalLedger joins leaves closed,
      LifetimeHistory params initial []
          (EpisodeLedger.empty : EpisodeLedger n)
          operations joins leaves closed final finalLabels finalLedger ∧
        finalLabels.length = final.blocks.length ∧
        EpisodeLedger.ExactAt final finalLabels finalLedger ∧
        joins.length =
          totalInserts operations + totalActivity operations ∧
        leaves.length = totalLeaves operations ∧
        closed.length = totalLeaves operations := by
  obtain ⟨finalLabels, joins, joinHistory, final_aligned,
      joins_length⟩ :=
    JoinHistory.lift_initial initialState trace
  obtain ⟨finalLedger, leaves, closed, lifetime⟩ :=
    LifetimeHistory.lift joinHistory
      (EpisodeLedger.empty : EpisodeLedger n)
  have initial_exact :
      EpisodeLedger.ExactAt initial []
        (EpisodeLedger.empty : EpisodeLedger n) :=
    EpisodeLedger.ExactAt.initial initialState
  have final_exact :=
    lifetime.exact_final (by simp [initialState.2]) initial_exact
  have leaves_length := lifetime.leaves_length
  have closed_length :=
    lifetime.closed_length (by simp [initialState.2]) initial_exact
  exact
    ⟨finalLabels, finalLedger, joins, leaves, closed, lifetime,
      final_aligned, final_exact, joins_length, leaves_length,
      closed_length⟩

end LifetimeHistory

end Splay.Interface
