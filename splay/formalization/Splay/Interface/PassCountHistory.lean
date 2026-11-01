import Splay.Interface.GlobalDecayHistory
import Splay.Interface.ConversionAccounting
import Splay.Interface.ActivityTail

namespace Splay.Interface

/--
The elementary temporal invariant behind pass-count history: a growing block
has never been passed, hence still has counter zero.
-/
def GrowingPassCountZero {n : ℕ} (state : State n) : Prop :=
  ∀ blockId block,
    state.block? blockId = some block →
      block.mode = .growing → block.passCount = 0

private theorem lookup_modify_of_update
    {α : Type*} {P : α → Prop} (values : List α) (index : ℕ)
    (update : α → α)
    (all : ∀ (valueId : ℕ) (value : α),
      values[valueId]? = some value → P value)
    (preserves : ∀ value, P value → P (update value)) :
    ∀ (valueId : ℕ) (value : α),
      (values.modify index update)[valueId]? = some value → P value := by
  intro valueId value found
  rw [List.getElem?_modify] at found
  cases original_found : values[valueId]? with
  | none =>
      simp [original_found] at found
  | some original =>
      by_cases same : index = valueId
      · simp [original_found, same] at found
        subst value
        exact preserves original (all valueId original original_found)
      · simp [original_found, same] at found
        subst value
        exact all valueId original original_found

private theorem growingZero_insertAtDestinations
    {n : ℕ} (blocks : List (Block n))
    (matching : List (Pairing n))
    (all : ∀ (blockId : ℕ) (block : Block n),
      blocks[blockId]? = some block →
        block.mode = .growing → block.passCount = 0) :
    ∀ (blockId : ℕ) (block : Block n),
      (insertAtDestinations blocks matching)[blockId]? = some block →
        block.mode = .growing → block.passCount = 0 := by
  induction matching generalizing blocks with
  | nil =>
      exact all
  | cons pairing matching ih =>
      apply ih
      apply lookup_modify_of_update blocks pairing.destination
        (fun destination =>
          { destination with
            elements := pairing.loser :: destination.elements })
        (P := fun block =>
          block.mode = .growing → block.passCount = 0) all
      intro destination destination_ok growing
      exact destination_ok growing

private theorem GrowingPassCountZero.effect
    {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    (invariant : GrowingPassCountZero before)
    (effect : Effect params before operation after) :
    GrowingPassCountZero after := by
  intro queryId block after_found growing
  unfold State.block? at after_found
  cases effect with
  | convert found source_growing blocks_eq values_eq =>
      rw [blocks_eq] at after_found
      refine lookup_modify_of_update before.blocks _ _
          (P := fun value =>
            value.mode = .growing → value.passCount = 0)
          (by
            intro id value lookup
            exact invariant id value lookup) ?_
          queryId block after_found growing
      intro source source_ok updated_growing
      simp at updated_growing
  | create room blocks_eq values_eq =>
      rw [blocks_eq, List.getElem?_append] at after_found
      by_cases old : queryId < before.blocks.length
      · simp only [old, if_pos] at after_found
        exact invariant queryId block after_found growing
      · simp only [old] at after_found
        have offset_le_one :
            queryId - before.blocks.length < 1 := by
          have in_bounds := (List.getElem?_eq_some_iff.mp after_found).choose
          simpa using in_bounds
        have offset_zero :
            queryId - before.blocks.length = 0 :=
          Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ offset_le_one)
        simp [offset_zero] at after_found
        subst block
        rfl
  | insert found target_growing unassigned value_order blocks_eq values_eq =>
      rw [blocks_eq] at after_found
      refine lookup_modify_of_update before.blocks _ _
          (P := fun value =>
            value.mode = .growing → value.passCount = 0)
          (by
            intro id value lookup
            exact invariant id value lookup) ?_
          queryId block after_found growing
      intro target target_ok updated_growing
      exact target_ok updated_growing
  | delete found source_shrinking present blocks_eq values_eq =>
      rw [blocks_eq] at after_found
      refine lookup_modify_of_update before.blocks _ _
          (P := fun value =>
            value.mode = .growing → value.passCount = 0)
          (by
            intro id value lookup
            exact invariant id value lookup) ?_
          queryId block after_found growing
      intro source source_ok updated_growing
      exact source_ok updated_growing
  | pass found valid_matching blocks_eq values_eq =>
      rename_i sourceId source matching
      rw [blocks_eq] at after_found
      unfold passBlocks at after_found
      apply growingZero_insertAtDestinations _ _ ?_
          queryId block after_found growing
      refine lookup_modify_of_update before.blocks sourceId _
        (P := fun value =>
          value.mode = .growing → value.passCount = 0)
        (by
          intro id value lookup
          exact invariant id value lookup) ?_
      intro updatedSource source_ok updated_growing
      have shrinking := valid_matching.1
      simp [shrinking] at updated_growing
  | split found source_shrinking prefix_le blocks_eq values_eq =>
      rename_i sourceId source prefixLength
      rw [blocks_eq] at after_found
      unfold splitBlocks at after_found
      rw [List.getElem?_append] at after_found
      by_cases old : queryId < before.blocks.length
      · simp only [List.length_modify, old, if_pos] at after_found
        refine lookup_modify_of_update before.blocks sourceId _
            (P := fun value =>
              value.mode = .growing → value.passCount = 0)
            (by
              intro id value lookup
              exact invariant id value lookup) ?_
            queryId block after_found growing
        intro updatedSource source_ok
        simpa using source_ok
      · simp only [List.length_modify, old] at after_found
        have offset_lt :
            queryId - before.blocks.length < 2 := by
          have in_bounds := (List.getElem?_eq_some_iff.mp after_found).choose
          simpa using in_bounds
        have offset_cases :
            queryId - before.blocks.length = 0 ∨
              queryId - before.blocks.length = 1 :=
          Nat.le_one_iff_eq_zero_or_eq_one.mp
            (Nat.le_of_lt_succ offset_lt)
        rcases offset_cases with offset | offset <;>
          simp [offset] at after_found <;>
          subst block <;>
          simp [source_shrinking] at growing
  | decrease can_decrease blocks_eq values_eq =>
      exact invariant queryId block (by
        simpa [State.block?, blocks_eq] using after_found) growing
  | increase can_increase blocks_eq values_eq =>
      exact invariant queryId block (by
        simpa [State.block?, blocks_eq] using after_found) growing

namespace HistoryTrace

theorem preserveGrowingPassCountZero
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    (history :
      HistoryTrace params initial initialLabels operations final finalLabels)
    (invariant : GrowingPassCountZero initial) :
    GrowingPassCountZero final := by
  induction history with
  | nil valid =>
      exact invariant
  | cons head tail ih =>
      exact ih (invariant.effect head.2.1)

/-- Every trace from an empty-block initial state has zero-count growing blocks. -/
theorem growingPassCountZero
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    (history :
      HistoryTrace params initial initialLabels operations final finalLabels)
    (initialState : initial.Initial params) :
    GrowingPassCountZero final := by
  have initialInvariant : GrowingPassCountZero initial := by
    intro blockId block found
    rw [State.block?, initialState.2] at found
    simp at found
  exact preserveGrowingPassCountZero history initialInvariant

end HistoryTrace

/--
Mass of the `(root, passCount)` fiber in one aligned state, counted over all
split descendants.
-/
def passCountMassOf {n : ℕ} :
    List (Block n) → RootLabels → RootId → ℕ → ℕ
  | block :: blocks, label :: labels, root, passCount =>
      (if label = root ∧ block.passCount = passCount
        then block.elements.length else 0) +
        passCountMassOf blocks labels root passCount
  | _, _, _, _ => 0

def passCountMass {n : ℕ} (state : State n) (labels : RootLabels)
    (root : RootId) (passCount : ℕ) : ℕ :=
  passCountMassOf state.blocks labels root passCount

/-- Source size contributed by a pass with the selected pre-pass fiber key. -/
def operationPassBeforeMass {n : ℕ} (state : State n)
    (labels : RootLabels) (root : RootId) (passCount : ℕ) :
    Operation n → ℕ
  | .pass sourceId _ =>
      match state.block? sourceId, RootLabels.root? labels sourceId with
      | some source, some sourceRoot =>
          if sourceRoot = root ∧ source.passCount = passCount
            then source.elements.length else 0
      | _, _ => 0
  | _ => 0

/-- Survivor size contributed by a pass with the selected pre-pass key. -/
def operationPassAfterMass {n : ℕ} (state : State n)
    (labels : RootLabels) (root : RootId) (passCount : ℕ) :
    Operation n → ℕ
  | .pass sourceId matching =>
      match state.block? sourceId, RootLabels.root? labels sourceId with
      | some source, some sourceRoot =>
          if sourceRoot = root ∧ source.passCount = passCount
            then (removeLosers source.elements matching).length else 0
      | _, _ => 0
  | _ => 0

/-- Root-filtered mass cashed out by one conversion operation. -/
def operationRootConversionMass {n : ℕ} (state : State n)
    (labels : RootLabels) (root : RootId) : Operation n → ℕ
  | .convert blockId =>
      if (RootLabels.root? labels blockId).getD blockId = root then
        (state.block? blockId).map
          (fun block => block.elements.length) |>.getD 0
      else 0
  | _ => 0

/-- Mass still eligible for its first pass in shrinking descendants. -/
def shrinkingZeroMassOf {n : ℕ} :
    List (Block n) → RootLabels → RootId → ℕ
  | block :: blocks, label :: labels, root =>
      (if label = root ∧ block.mode = .shrinking ∧ block.passCount = 0
        then block.elements.length else 0) +
        shrinkingZeroMassOf blocks labels root
  | _, _, _ => 0

def shrinkingZeroMass {n : ℕ} (state : State n)
    (labels : RootLabels) (root : RootId) : ℕ :=
  shrinkingZeroMassOf state.blocks labels root

private def blockShrinkingZeroMass {n : ℕ} (block : Block n)
    (label root : RootId) : ℕ :=
  if label = root ∧ block.mode = .shrinking ∧ block.passCount = 0
    then block.elements.length else 0

private def blockPassCountMass {n : ℕ} (block : Block n)
    (label root : RootId) (passCount : ℕ) : ℕ :=
  if label = root ∧ block.passCount = passCount
    then block.elements.length else 0

private theorem passCountMassOf_modify_balance
    {n : ℕ} (blocks : List (Block n)) (labels : RootLabels)
    (aligned : labels.length = blocks.length)
    (index : ℕ) (source : Block n)
    (found : blocks[index]? = some source)
    (update : Block n → Block n)
    (root : RootId) (passCount : ℕ) :
    passCountMassOf (blocks.modify index update) labels root passCount +
        blockPassCountMass source
          (labels[index]?.getD index) root passCount =
      passCountMassOf blocks labels root passCount +
        blockPassCountMass (update source)
          (labels[index]?.getD index) root passCount := by
  induction index generalizing blocks labels with
  | zero =>
      cases blocks with
      | nil =>
          simp at found
      | cons head tail =>
          cases labels with
          | nil =>
              simp at aligned
          | cons label labels =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst head
              simp [passCountMassOf, blockPassCountMass]
              omega
  | succ index ih =>
      cases blocks with
      | nil =>
          simp at found
      | cons head tail =>
          cases labels with
          | nil =>
              simp at aligned
          | cons label labels =>
              simp only [List.getElem?_cons_succ] at found
              have modify_eq :
                  (head :: tail).modify (index + 1) update =
                    head :: tail.modify index update := by
                rfl
              rw [modify_eq]
              simp only [passCountMassOf]
              have tailAligned : labels.length = tail.length := by
                simp at aligned
                exact aligned
              have index_lt : index < tail.length :=
                (List.getElem?_eq_some_iff.mp found).choose
              have label_lt : index < labels.length := by omega
              have tailBalance :=
                ih tail labels tailAligned found
              simp only [List.getElem?_cons_succ]
              rw [List.getElem?_eq_getElem label_lt] at tailBalance ⊢
              simp only [Option.getD_some] at tailBalance ⊢
              omega

private theorem passCountMassOf_append
    {n : ℕ} (firstBlocks secondBlocks : List (Block n))
    (firstLabels secondLabels : RootLabels)
    (aligned : firstLabels.length = firstBlocks.length)
    (root : RootId) (passCount : ℕ) :
    passCountMassOf (firstBlocks ++ secondBlocks)
        (firstLabels ++ secondLabels) root passCount =
      passCountMassOf firstBlocks firstLabels root passCount +
        passCountMassOf secondBlocks secondLabels root passCount := by
  induction firstBlocks generalizing firstLabels with
  | nil =>
      have labels_nil : firstLabels = [] := by
        simpa using aligned
      subst firstLabels
      simp [passCountMassOf]
  | cons block blocks ih =>
      cases firstLabels with
      | nil =>
          simp at aligned
      | cons label labels =>
          have tailAligned : labels.length = blocks.length := by
            simp at aligned
            exact aligned
          simp only [List.cons_append, passCountMassOf]
          rw [ih labels tailAligned]
          omega

private theorem shrinkingZeroMassOf_modify_balance
    {n : ℕ} (blocks : List (Block n)) (labels : RootLabels)
    (aligned : labels.length = blocks.length)
    (index : ℕ) (source : Block n)
    (found : blocks[index]? = some source)
    (update : Block n → Block n)
    (root : RootId) :
    shrinkingZeroMassOf (blocks.modify index update) labels root +
        blockShrinkingZeroMass source (labels[index]?.getD index) root =
      shrinkingZeroMassOf blocks labels root +
        blockShrinkingZeroMass (update source)
          (labels[index]?.getD index) root := by
  induction index generalizing blocks labels with
  | zero =>
      cases blocks with
      | nil =>
          simp at found
      | cons head tail =>
          cases labels with
          | nil =>
              simp at aligned
          | cons label labels =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst head
              simp [shrinkingZeroMassOf, blockShrinkingZeroMass]
              omega
  | succ index ih =>
      cases blocks with
      | nil =>
          simp at found
      | cons head tail =>
          cases labels with
          | nil =>
              simp at aligned
          | cons label labels =>
              simp only [List.getElem?_cons_succ] at found
              have modifyEq :
                  (head :: tail).modify (index + 1) update =
                    head :: tail.modify index update := by
                rfl
              rw [modifyEq]
              simp only [shrinkingZeroMassOf]
              have tailAligned : labels.length = tail.length := by
                simp at aligned
                exact aligned
              have indexLt : index < tail.length :=
                (List.getElem?_eq_some_iff.mp found).choose
              have labelLt : index < labels.length := by omega
              have tailBalance := ih tail labels tailAligned found
              simp only [List.getElem?_cons_succ]
              rw [List.getElem?_eq_getElem labelLt] at tailBalance ⊢
              simp only [Option.getD_some] at tailBalance ⊢
              omega

private theorem shrinkingZeroMassOf_append
    {n : ℕ} (firstBlocks secondBlocks : List (Block n))
    (firstLabels secondLabels : RootLabels)
    (aligned : firstLabels.length = firstBlocks.length)
    (root : RootId) :
    shrinkingZeroMassOf (firstBlocks ++ secondBlocks)
        (firstLabels ++ secondLabels) root =
      shrinkingZeroMassOf firstBlocks firstLabels root +
        shrinkingZeroMassOf secondBlocks secondLabels root := by
  induction firstBlocks generalizing firstLabels with
  | nil =>
      have labelsNil : firstLabels = [] := by simpa using aligned
      subst firstLabels
      simp [shrinkingZeroMassOf]
  | cons block blocks ih =>
      cases firstLabels with
      | nil =>
          simp at aligned
      | cons label labels =>
          have tailAligned : labels.length = blocks.length := by
            simp at aligned
            exact aligned
          simp only [List.cons_append, shrinkingZeroMassOf]
          rw [ih labels tailAligned]
          omega

private theorem shrinkingZeroMassOf_insertAtDestinations
    {n : ℕ} (blocks : List (Block n)) (labels : RootLabels)
    (aligned : labels.length = blocks.length)
    (matching : List (Pairing n))
    (destinationsNodup :
      (matching.map fun pairing => pairing.destination).Nodup)
    (destinationsGrowing :
      ∀ pairing ∈ matching,
        ∃ destination,
          blocks[pairing.destination]? = some destination ∧
            destination.mode = .growing)
    (root : RootId) :
    shrinkingZeroMassOf (insertAtDestinations blocks matching)
        labels root =
      shrinkingZeroMassOf blocks labels root := by
  induction matching generalizing blocks with
  | nil =>
      rfl
  | cons head tail ih =>
      have headNotMem :
          head.destination ∉
            tail.map fun pairing => pairing.destination :=
        (List.nodup_cons.mp (by simpa using destinationsNodup)).1
      have tailNodup :
          (tail.map fun pairing => pairing.destination).Nodup :=
        (List.nodup_cons.mp (by simpa using destinationsNodup)).2
      obtain ⟨destination, destinationFound, destinationGrowing⟩ :=
        destinationsGrowing head (by simp)
      let updated :=
        blocks.modify head.destination fun current =>
          { current with
            elements := head.loser :: current.elements }
      have updatedAligned : labels.length = updated.length := by
        simpa [updated] using aligned
      have tailGrowing :
          ∀ pairing ∈ tail,
            ∃ destination,
              updated[pairing.destination]? = some destination ∧
                destination.mode = .growing := by
        intro pairing pairingMem
        obtain ⟨later, laterFound, laterGrowing⟩ :=
          destinationsGrowing pairing (by simp [pairingMem])
        have destinationsNe :
            head.destination ≠ pairing.destination := by
          intro same
          apply headNotMem
          exact List.mem_map.mpr ⟨pairing, pairingMem, same.symm⟩
        refine ⟨later, ?_, laterGrowing⟩
        simpa [updated, destinationsNe] using laterFound
      have oneStep :=
        shrinkingZeroMassOf_modify_balance blocks labels aligned
          head.destination destination destinationFound
          (fun current =>
            { current with
              elements := head.loser :: current.elements })
          root
      have oneStepEq :
          shrinkingZeroMassOf updated labels root =
            shrinkingZeroMassOf blocks labels root := by
        dsimp [updated]
        simp [blockShrinkingZeroMass, destinationGrowing] at oneStep
        exact oneStep
      change
        shrinkingZeroMassOf (insertAtDestinations updated tail)
            labels root =
          shrinkingZeroMassOf blocks labels root
      rw [ih updated updatedAligned tailNodup tailGrowing, oneStepEq]

private theorem passCountMassOf_insertAtDestinations
    {n : ℕ} (blocks : List (Block n)) (labels : RootLabels)
    (aligned : labels.length = blocks.length)
    (matching : List (Pairing n))
    (destinationsNodup :
      (matching.map fun pairing => pairing.destination).Nodup)
    (destinationsZero :
      ∀ pairing ∈ matching,
        ∃ destination,
          blocks[pairing.destination]? = some destination ∧
            destination.passCount = 0)
    (root : RootId) (passCount : ℕ) (positive : 0 < passCount) :
    passCountMassOf (insertAtDestinations blocks matching)
        labels root passCount =
      passCountMassOf blocks labels root passCount := by
  induction matching generalizing blocks with
  | nil =>
      rfl
  | cons head tail ih =>
      have headNotMem :
          head.destination ∉
            tail.map fun pairing => pairing.destination :=
        (List.nodup_cons.mp (by simpa using destinationsNodup)).1
      have tailNodup :
          (tail.map fun pairing => pairing.destination).Nodup :=
        (List.nodup_cons.mp (by simpa using destinationsNodup)).2
      obtain ⟨destination, destinationFound, destinationZero⟩ :=
        destinationsZero head (by simp)
      let updated :=
        blocks.modify head.destination fun current =>
          { current with
            elements := head.loser :: current.elements }
      have updatedAligned : labels.length = updated.length := by
        simpa [updated] using aligned
      have tailZero :
          ∀ pairing ∈ tail,
            ∃ destination,
              updated[pairing.destination]? = some destination ∧
                destination.passCount = 0 := by
        intro pairing pairingMem
        obtain ⟨later, laterFound, laterZero⟩ :=
          destinationsZero pairing (by simp [pairingMem])
        have destinationsNe :
            head.destination ≠ pairing.destination := by
          intro same
          apply headNotMem
          exact List.mem_map.mpr ⟨pairing, pairingMem, same.symm⟩
        refine ⟨later, ?_, laterZero⟩
        simpa [updated, destinationsNe] using laterFound
      have oneStep :=
        passCountMassOf_modify_balance blocks labels aligned
          head.destination destination destinationFound
          (fun current =>
            { current with
              elements := head.loser :: current.elements })
          root passCount
      have oneStepEq :
          passCountMassOf updated labels root passCount =
            passCountMassOf blocks labels root passCount := by
        dsimp [updated]
        simp [blockPassCountMass, destinationZero,
          (Nat.ne_of_gt positive).symm] at oneStep
        exact oneStep
      change
        passCountMassOf (insertAtDestinations updated tail)
            labels root passCount =
          passCountMassOf blocks labels root passCount
      rw [ih updated updatedAligned tailNodup tailZero, oneStepEq]

private theorem Effect.passCountMass_successor_balance
    {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    (effect : Effect params before operation after)
    (labels : RootLabels)
    (aligned : labels.length = before.blocks.length)
    (growingZero : GrowingPassCountZero before)
    (root : RootId) (passCount : ℕ) :
    passCountMass after (RootLabels.after labels operation)
          root (passCount + 1) +
        operationPassBeforeMass before labels root (passCount + 1)
          operation ≤
      passCountMass before labels root (passCount + 1) +
        operationPassAfterMass before labels root passCount operation := by
  cases effect with
  | convert found sourceGrowing blocksEq valuesEq =>
      rename_i sourceId source
      unfold State.block? at found
      have balance :=
        passCountMassOf_modify_balance before.blocks labels aligned
          sourceId source found
          (fun current => { current with mode := .shrinking })
          root (passCount + 1)
      simpa [passCountMass, RootLabels.after, blocksEq,
        operationPassBeforeMass, operationPassAfterMass,
        blockPassCountMass] using balance.le
  | create room blocksEq valuesEq =>
      unfold passCountMass
      rw [blocksEq, RootLabels.after_create,
        passCountMassOf_append before.blocks _ labels _ aligned]
      simp [passCountMassOf, operationPassBeforeMass,
        operationPassAfterMass]
  | insert found targetGrowing unassigned valueOrder blocksEq valuesEq =>
      rename_i targetId target element
      unfold State.block? at found
      have targetZero : target.passCount = 0 :=
        growingZero targetId target found targetGrowing
      have balance :=
        passCountMassOf_modify_balance before.blocks labels aligned
          targetId target found
          (fun current =>
            { current with elements := element :: current.elements })
          root (passCount + 1)
      simpa [passCountMass, RootLabels.after, blocksEq,
        operationPassBeforeMass, operationPassAfterMass,
        blockPassCountMass, targetZero] using balance.le
  | delete found sourceShrinking present blocksEq valuesEq =>
      rename_i sourceId source element
      unfold State.block? at found
      let updated : Block n :=
        { source with elements := source.elements.erase element }
      have balance :=
        passCountMassOf_modify_balance before.blocks labels aligned
          sourceId source found
          (fun current =>
            { current with elements := current.elements.erase element })
          root (passCount + 1)
      have updatedWeightLe :
          blockPassCountMass updated
              (labels[sourceId]?.getD sourceId)
              root (passCount + 1) ≤
            blockPassCountMass source
              (labels[sourceId]?.getD sourceId)
              root (passCount + 1) := by
        simp only [blockPassCountMass]
        by_cases selected :
            labels[sourceId]?.getD sourceId = root ∧
              source.passCount = passCount + 1
        · simp [selected, updated, List.length_erase_le]
        · simp [selected, updated]
      dsimp [updated] at updatedWeightLe
      simp [passCountMass, RootLabels.after, blocksEq,
        operationPassBeforeMass, operationPassAfterMass]
      omega
  | pass found validMatching blocksEq valuesEq =>
      rename_i sourceId source matching
      unfold State.block? at found
      have sourceLt :
          sourceId < before.blocks.length :=
        (List.getElem?_eq_some_iff.mp found).choose
      have labelLt : sourceId < labels.length := by
        simpa [aligned] using sourceLt
      let sourceRoot : RootId := labels[sourceId]
      have rootFound :
          RootLabels.root? labels sourceId = some sourceRoot := by
        exact List.getElem?_eq_getElem labelLt
      let sourceAfter : Block n :=
        { source with
          passCount := source.passCount + 1
          elements := removeLosers source.elements matching }
      let sourceUpdated :=
        before.blocks.modify sourceId fun _ => sourceAfter
      have sourceUpdatedAligned :
          labels.length = sourceUpdated.length := by
        simpa [sourceUpdated] using aligned
      have destinationsZero :
          ∀ pairing ∈ matching,
            ∃ destination,
              sourceUpdated[pairing.destination]? = some destination ∧
                destination.passCount = 0 := by
        intro pairing pairingMem
        obtain
          ⟨destination, destinationFound, destinationGrowing,
            _creatorEq⟩ :=
          (validMatching.2.2.2.1 pairing pairingMem).2.2.2
        unfold State.block? at destinationFound
        have destinationNe : pairing.destination ≠ sourceId :=
          (validMatching.2.2.2.1 pairing pairingMem).2.2.1
        refine ⟨destination, ?_,
          growingZero pairing.destination destination
            destinationFound destinationGrowing⟩
        simpa [sourceUpdated, destinationNe.symm] using destinationFound
      have destinationsPreserve :=
        passCountMassOf_insertAtDestinations sourceUpdated labels
          sourceUpdatedAligned matching validMatching.2.2.1
          destinationsZero root (passCount + 1) (by omega)
      have sourceBalance :=
        passCountMassOf_modify_balance before.blocks labels aligned
          sourceId source found (fun _ => sourceAfter)
          root (passCount + 1)
      have rootLookup :
          labels[sourceId]?.getD sourceId = sourceRoot := by
        rw [List.getElem?_eq_getElem labelLt]
        rfl
      simp only [passCountMass, RootLabels.after, blocksEq]
      unfold passBlocks
      change
        passCountMassOf (insertAtDestinations sourceUpdated matching)
              labels root (passCount + 1) +
            operationPassBeforeMass before labels root
              (passCount + 1) (.pass sourceId matching) ≤
          passCountMassOf before.blocks labels root (passCount + 1) +
            operationPassAfterMass before labels root passCount
              (.pass sourceId matching)
      rw [destinationsPreserve]
      simpa [operationPassBeforeMass, operationPassAfterMass,
        State.block?, found, rootFound, blockPassCountMass,
        sourceAfter, sourceRoot, rootLookup] using sourceBalance.le
  | split found sourceShrinking prefixLe blocksEq valuesEq =>
      rename_i sourceId source prefixLength
      unfold State.block? at found
      let emptied : Block n := { source with elements := [] }
      let oldEmptied :=
        before.blocks.modify sourceId fun current =>
          { current with elements := [] }
      let sourceRoot :=
        (RootLabels.root? labels sourceId).getD sourceId
      have emptiedBalance :=
        passCountMassOf_modify_balance before.blocks labels aligned
          sourceId source found
          (fun current => { current with elements := [] })
          root (passCount + 1)
      have appendedBalance :=
        passCountMassOf_append oldEmptied
          [{ source with elements := source.elements.take prefixLength },
            { source with elements := source.elements.drop prefixLength }]
          labels [sourceRoot, sourceRoot]
          (by simpa [oldEmptied] using aligned)
          root (passCount + 1)
      simp only [passCountMass, operationPassBeforeMass,
        operationPassAfterMass, RootLabels.after, blocksEq,
        add_zero]
      unfold splitBlocks
      change
        passCountMassOf
              (oldEmptied ++
                [{ source with
                    elements := source.elements.take prefixLength },
                  { source with
                    elements := source.elements.drop prefixLength }])
              (labels ++ [sourceRoot, sourceRoot])
              root (passCount + 1) ≤
          passCountMassOf before.blocks labels root (passCount + 1)
      have splitLength :
          (source.elements.take prefixLength).length +
              (source.elements.drop prefixLength).length =
            source.elements.length := by
        rw [← List.length_append, List.take_append_drop]
      have childrenMass :
          passCountMassOf
              [{ source with
                  elements := source.elements.take prefixLength },
                { source with
                  elements := source.elements.drop prefixLength }]
              [sourceRoot, sourceRoot] root (passCount + 1) =
            blockPassCountMass source sourceRoot root
              (passCount + 1) := by
        simp only [passCountMassOf, blockPassCountMass]
        by_cases selected :
            sourceRoot = root ∧ source.passCount = passCount + 1
        · simp [selected]
          omega
        · simp [selected]
      rw [appendedBalance, childrenMass]
      simp [blockPassCountMass] at emptiedBalance
      dsimp [oldEmptied, sourceRoot, RootLabels.root?]
      rw [← emptiedBalance]
      simp [blockPassCountMass]
  | decrease canDecrease blocksEq valuesEq =>
      simp [passCountMass, RootLabels.after, blocksEq,
        operationPassBeforeMass, operationPassAfterMass]
  | increase canIncrease blocksEq valuesEq =>
      simp [passCountMass, RootLabels.after, blocksEq,
        operationPassBeforeMass, operationPassAfterMass]

private theorem Effect.shrinkingZeroMass_balance
    {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    (effect : Effect params before operation after)
    (labels : RootLabels)
    (aligned : labels.length = before.blocks.length)
    (growingZero : GrowingPassCountZero before)
    (root : RootId) :
    shrinkingZeroMass after (RootLabels.after labels operation) root +
        operationPassBeforeMass before labels root 0 operation ≤
      shrinkingZeroMass before labels root +
        operationRootConversionMass before labels root operation := by
  cases effect with
  | convert found sourceGrowing blocksEq valuesEq =>
      rename_i sourceId source
      unfold State.block? at found
      have sourceZero : source.passCount = 0 :=
        growingZero sourceId source found sourceGrowing
      have sourceLt :
          sourceId < before.blocks.length :=
        (List.getElem?_eq_some_iff.mp found).choose
      have labelLt : sourceId < labels.length := by
        simpa [aligned] using sourceLt
      let sourceRoot : RootId := labels[sourceId]
      have rootFound :
          RootLabels.root? labels sourceId = some sourceRoot :=
        List.getElem?_eq_getElem labelLt
      have rootLookup :
          labels[sourceId]?.getD sourceId = sourceRoot := by
        rw [List.getElem?_eq_getElem labelLt]
        rfl
      have balance :=
        shrinkingZeroMassOf_modify_balance before.blocks labels aligned
          sourceId source found
          (fun current => { current with mode := .shrinking }) root
      simpa [shrinkingZeroMass, RootLabels.after, blocksEq,
        operationPassBeforeMass, operationRootConversionMass,
        State.block?, found, blockShrinkingZeroMass,
        sourceGrowing, sourceZero, rootFound, sourceRoot,
        rootLookup] using balance.le
  | create room blocksEq valuesEq =>
      unfold shrinkingZeroMass
      rw [blocksEq, RootLabels.after_create,
        shrinkingZeroMassOf_append before.blocks _ labels _ aligned]
      simp [shrinkingZeroMassOf, operationPassBeforeMass,
        operationRootConversionMass]
  | insert found targetGrowing unassigned valueOrder blocksEq valuesEq =>
      rename_i targetId target element
      unfold State.block? at found
      have balance :=
        shrinkingZeroMassOf_modify_balance before.blocks labels aligned
          targetId target found
          (fun current =>
            { current with elements := element :: current.elements })
          root
      simpa [shrinkingZeroMass, RootLabels.after, blocksEq,
        operationPassBeforeMass, operationRootConversionMass,
        blockShrinkingZeroMass, targetGrowing] using balance.le
  | delete found sourceShrinking present blocksEq valuesEq =>
      rename_i sourceId source element
      unfold State.block? at found
      let updated : Block n :=
        { source with elements := source.elements.erase element }
      have balance :=
        shrinkingZeroMassOf_modify_balance before.blocks labels aligned
          sourceId source found
          (fun current =>
            { current with elements := current.elements.erase element })
          root
      have updatedWeightLe :
          blockShrinkingZeroMass updated
              (labels[sourceId]?.getD sourceId) root ≤
            blockShrinkingZeroMass source
              (labels[sourceId]?.getD sourceId) root := by
        simp only [blockShrinkingZeroMass]
        by_cases selected :
            labels[sourceId]?.getD sourceId = root ∧
              source.mode = .shrinking ∧ source.passCount = 0
        · simp [selected, updated, List.length_erase_le]
        · simp [selected, updated]
      dsimp [updated] at updatedWeightLe
      simp [shrinkingZeroMass, RootLabels.after, blocksEq,
        operationPassBeforeMass, operationRootConversionMass]
      omega
  | pass found validMatching blocksEq valuesEq =>
      rename_i sourceId source matching
      unfold State.block? at found
      have sourceLt :
          sourceId < before.blocks.length :=
        (List.getElem?_eq_some_iff.mp found).choose
      have labelLt : sourceId < labels.length := by
        simpa [aligned] using sourceLt
      let sourceRoot : RootId := labels[sourceId]
      have rootFound :
          RootLabels.root? labels sourceId = some sourceRoot :=
        List.getElem?_eq_getElem labelLt
      let sourceAfter : Block n :=
        { source with
          passCount := source.passCount + 1
          elements := removeLosers source.elements matching }
      let sourceUpdated :=
        before.blocks.modify sourceId fun _ => sourceAfter
      have sourceUpdatedAligned :
          labels.length = sourceUpdated.length := by
        simpa [sourceUpdated] using aligned
      have destinationsGrowing :
          ∀ pairing ∈ matching,
            ∃ destination,
              sourceUpdated[pairing.destination]? = some destination ∧
                destination.mode = .growing := by
        intro pairing pairingMem
        obtain
          ⟨destination, destinationFound, destinationGrowing,
            _creatorEq⟩ :=
          (validMatching.2.2.2.1 pairing pairingMem).2.2.2
        unfold State.block? at destinationFound
        have destinationNe : pairing.destination ≠ sourceId :=
          (validMatching.2.2.2.1 pairing pairingMem).2.2.1
        refine ⟨destination, ?_, destinationGrowing⟩
        simpa [sourceUpdated, destinationNe.symm] using destinationFound
      have destinationsPreserve :=
        shrinkingZeroMassOf_insertAtDestinations sourceUpdated labels
          sourceUpdatedAligned matching validMatching.2.2.1
          destinationsGrowing root
      have sourceBalance :=
        shrinkingZeroMassOf_modify_balance before.blocks labels aligned
          sourceId source found (fun _ => sourceAfter) root
      have rootLookup :
          labels[sourceId]?.getD sourceId = sourceRoot := by
        rw [List.getElem?_eq_getElem labelLt]
        rfl
      simp only [shrinkingZeroMass, RootLabels.after, blocksEq]
      unfold passBlocks
      change
        shrinkingZeroMassOf (insertAtDestinations sourceUpdated matching)
              labels root +
            operationPassBeforeMass before labels root 0
              (.pass sourceId matching) ≤
          shrinkingZeroMassOf before.blocks labels root
      rw [destinationsPreserve]
      simpa [operationPassBeforeMass, State.block?, found, rootFound,
        blockShrinkingZeroMass, sourceAfter, sourceRoot, rootLookup,
        sourceUpdated, validMatching.1] using sourceBalance.le
  | split found sourceShrinking prefixLe blocksEq valuesEq =>
      rename_i sourceId source prefixLength
      unfold State.block? at found
      let emptied : Block n := { source with elements := [] }
      let oldEmptied :=
        before.blocks.modify sourceId fun current =>
          { current with elements := [] }
      let sourceRoot :=
        (RootLabels.root? labels sourceId).getD sourceId
      have emptiedBalance :=
        shrinkingZeroMassOf_modify_balance before.blocks labels aligned
          sourceId source found
          (fun current => { current with elements := [] }) root
      have appendedBalance :=
        shrinkingZeroMassOf_append oldEmptied
          [{ source with elements := source.elements.take prefixLength },
            { source with elements := source.elements.drop prefixLength }]
          labels [sourceRoot, sourceRoot]
          (by simpa [oldEmptied] using aligned) root
      simp only [shrinkingZeroMass, operationPassBeforeMass,
        operationRootConversionMass, RootLabels.after, blocksEq,
        add_zero]
      unfold splitBlocks
      change
        shrinkingZeroMassOf
              (oldEmptied ++
                [{ source with
                    elements := source.elements.take prefixLength },
                  { source with
                    elements := source.elements.drop prefixLength }])
              (labels ++ [sourceRoot, sourceRoot]) root ≤
          shrinkingZeroMassOf before.blocks labels root
      have childrenMass :
          shrinkingZeroMassOf
              [{ source with
                  elements := source.elements.take prefixLength },
                { source with
                  elements := source.elements.drop prefixLength }]
              [sourceRoot, sourceRoot] root =
            blockShrinkingZeroMass source sourceRoot root := by
        simp only [shrinkingZeroMassOf, blockShrinkingZeroMass]
        by_cases selected :
            sourceRoot = root ∧ source.mode = .shrinking ∧
              source.passCount = 0
        · simp [selected]
          omega
        · simp [selected]
      rw [appendedBalance, childrenMass]
      simp [blockShrinkingZeroMass] at emptiedBalance
      dsimp [oldEmptied, sourceRoot, RootLabels.root?]
      rw [← emptiedBalance]
      simp [blockShrinkingZeroMass]
  | decrease canDecrease blocksEq valuesEq =>
      simp [shrinkingZeroMass, RootLabels.after, blocksEq,
        operationPassBeforeMass, operationRootConversionMass]
  | increase canIncrease blocksEq valuesEq =>
      simp [shrinkingZeroMass, RootLabels.after, blocksEq,
        operationPassBeforeMass, operationRootConversionMass]

namespace HeadFiberBatch

theorem beforeMass_eq_operationPassBeforeMass
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n} {root : RootId} {passCount : ℕ}
    {batch : DescendantBatch params}
    (realized :
      HeadFiberBatch before labels operation after
        (root, passCount) batch) :
    batch.beforeMass =
      operationPassBeforeMass before labels root passCount operation := by
  obtain
    ⟨sourceId, matching, source, sourceRoot, operationEq, _step,
      _aligned, sourceFound, rootFound, keyEq, _nonexempt,
      matchingValid, batchEq⟩ :=
    realized
  subst operation
  subst batch
  have rootEq : sourceRoot = root := congrArg Prod.fst keyEq
  have countEq : source.passCount = passCount :=
    congrArg Prod.snd keyEq
  simp [DescendantBatch.ofMatching, operationPassBeforeMass,
    sourceFound, rootFound, rootEq, countEq]

theorem afterMass_eq_operationPassAfterMass
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n} {root : RootId} {passCount : ℕ}
    {batch : DescendantBatch params}
    (realized :
      HeadFiberBatch before labels operation after
        (root, passCount) batch) :
    batch.afterMass =
      operationPassAfterMass before labels root passCount operation := by
  obtain
    ⟨sourceId, matching, source, sourceRoot, operationEq, _step,
      _aligned, sourceFound, rootFound, keyEq, _nonexempt,
      matchingValid, batchEq⟩ :=
    realized
  subst operation
  subst batch
  have rootEq : sourceRoot = root := congrArg Prod.fst keyEq
  have countEq : source.passCount = passCount :=
    congrArg Prod.snd keyEq
  simp [DescendantBatch.ofMatching, operationPassAfterMass,
    sourceFound, rootFound, rootEq, countEq]

end HeadFiberBatch

private theorem operationPassMass_eq_zero_of_activity_zero
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n}
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    (root : RootId) (passCount : ℕ)
    (nonexempt : params.exemptPasses ≤ passCount)
    (activityZero :
      lineageRunActivity
        (operationActivityOccurrences before labels operation)
        (root, passCount) = 0) :
    operationPassBeforeMass before labels root passCount operation = 0 ∧
      operationPassAfterMass before labels root passCount operation = 0 := by
  cases operation with
  | convert sourceId =>
      simp [operationPassBeforeMass, operationPassAfterMass]
  | create creator =>
      simp [operationPassBeforeMass, operationPassAfterMass]
  | insert targetId element =>
      simp [operationPassBeforeMass, operationPassAfterMass]
  | delete sourceId element =>
      simp [operationPassBeforeMass, operationPassAfterMass]
  | @pass sourceId matching =>
      obtain ⟨source, sourceFound, _afterFound⟩ :=
        step.2.1.pass_source?
      have sourceLt :
          sourceId < before.blocks.length :=
        (List.getElem?_eq_some_iff.mp sourceFound).choose
      have labelLt : sourceId < labels.length := by
        simpa [aligned] using sourceLt
      let sourceRoot : RootId := labels[sourceId]
      have rootFound :
          RootLabels.root? labels sourceId = some sourceRoot :=
        List.getElem?_eq_getElem labelLt
      have matchingValid :
          MatchingValid params before sourceId source matching := by
        cases effectEq : step.2.1 with
        | pass found valid blocksEq valuesEq =>
            rename_i actualSource
            have sourceEq : actualSource = source := by
              rw [sourceFound] at found
              exact (Option.some.inj found).symm
            subst actualSource
            exact valid
      by_cases selected :
          sourceRoot = root ∧ source.passCount = passCount
      · have matchingLengthZero : matching.length = 0 := by
          have noMember : ∀ pairing, pairing ∉ matching := by
            simpa [operationActivityOccurrences, lineageRunActivity,
              sourceFound, rootFound, ActivityOccurrence.key, selected] using
              activityZero
          have matchingNil :
              matching = [] :=
            List.eq_nil_iff_forall_not_mem.mpr noMember
          simp [matchingNil]
        have matchingNil : matching = [] :=
          List.length_eq_zero_iff.mp matchingLengthZero
        have sourceLengthZero : source.elements.length = 0 := by
          rcases matchingValid.2.2.2.2 with exempt | fraction
          · have sourceNonexempt :
                params.exemptPasses ≤ source.passCount := by
              simpa [selected.2] using nonexempt
            exact (Nat.not_lt_of_ge sourceNonexempt exempt).elim
          · rw [matchingLengthZero] at fraction
            simp only [Nat.mul_zero] at fraction
            have productZero :
                params.matchingNumerator * source.elements.length = 0 :=
              Nat.eq_zero_of_le_zero fraction
            rcases Nat.mul_eq_zero.mp productZero with numeratorZero |
                lengthZero
            · exact
                (Nat.ne_of_gt params.matchingNumerator_pos
                  numeratorZero).elim
            · exact lengthZero
        have sourceElementsNil : source.elements = [] :=
          List.length_eq_zero_iff.mp sourceLengthZero
        simp [operationPassBeforeMass, operationPassAfterMass,
          sourceFound, rootFound, selected, sourceElementsNil,
          matchingNil, removeLosers]
      · simp [operationPassBeforeMass, operationPassAfterMass,
          sourceFound, rootFound, selected]
  | split sourceId prefixLength =>
      simp [operationPassBeforeMass, operationPassAfterMass]
  | valueChange element delta =>
      simp [operationPassBeforeMass, operationPassAfterMass]

private theorem state_eq_of_fields
    {n : ℕ} {first second : State n}
    (blocksEq : first.blocks = second.blocks)
    (valuesEq : first.value = second.value) :
    first = second := by
  cases first
  cases second
  simp_all

private theorem Effect.after_eq
    {n : ℕ} {params : Parameters}
    {before firstAfter secondAfter : State n}
    {operation : Operation n}
    (first : Effect params before operation firstAfter)
    (second : Effect params before operation secondAfter) :
    firstAfter = secondAfter := by
  cases first with
  | convert firstFound firstGrowing firstBlocks firstValues =>
      cases second with
      | convert secondFound secondGrowing secondBlocks secondValues =>
          apply state_eq_of_fields
          · rw [firstBlocks, secondBlocks]
          · rw [firstValues, secondValues]
  | create firstRoom firstBlocks firstValues =>
      cases second with
      | create secondRoom secondBlocks secondValues =>
          apply state_eq_of_fields
          · rw [firstBlocks, secondBlocks]
          · rw [firstValues, secondValues]
  | insert firstFound firstGrowing firstUnassigned firstOrder
      firstBlocks firstValues =>
      cases second with
      | insert secondFound secondGrowing secondUnassigned secondOrder
          secondBlocks secondValues =>
          apply state_eq_of_fields
          · rw [firstBlocks, secondBlocks]
          · rw [firstValues, secondValues]
  | delete firstFound firstShrinking firstPresent firstBlocks firstValues =>
      cases second with
      | delete secondFound secondShrinking secondPresent secondBlocks
          secondValues =>
          apply state_eq_of_fields
          · rw [firstBlocks, secondBlocks]
          · rw [firstValues, secondValues]
  | pass firstFound firstValid firstBlocks firstValues =>
      rename_i sourceId source matching
      cases second with
      | pass secondFound secondValid secondBlocks secondValues =>
          rename_i secondSource
          have sourceEq : secondSource = source := by
            rw [firstFound] at secondFound
            exact (Option.some.inj secondFound).symm
          subst secondSource
          apply state_eq_of_fields
          · rw [firstBlocks, secondBlocks]
          · rw [firstValues, secondValues]
  | split firstFound firstShrinking firstPrefix firstBlocks firstValues =>
      rename_i sourceId source prefixLength
      cases second with
      | split secondFound secondShrinking secondPrefix secondBlocks
          secondValues =>
          rename_i secondSource
          have sourceEq : secondSource = source := by
            rw [firstFound] at secondFound
            exact (Option.some.inj secondFound).symm
          subst secondSource
          apply state_eq_of_fields
          · rw [firstBlocks, secondBlocks]
          · rw [firstValues, secondValues]
  | decrease firstCan firstBlocks firstValues =>
      cases second with
      | decrease secondCan secondBlocks secondValues =>
          apply state_eq_of_fields
          · rw [firstBlocks, secondBlocks]
          · rw [firstValues, secondValues]
  | increase firstCan firstBlocks firstValues =>
      cases second with
      | increase secondCan secondBlocks secondValues =>
          apply state_eq_of_fields
          · rw [firstBlocks, secondBlocks]
          · rw [firstValues, secondValues]

/--
The deterministic before/survivor pass-mass totals of one lineage fiber,
indexed by an occurrence-free lineage trace.
-/
inductive PassMassHistory {n : ℕ} (params : Parameters)
    (root : RootId) (passCount : ℕ) :
    ∀ {initial final : State n}
      {initialLabels finalLabels : RootLabels}
      {operations : List (Operation n)},
      HistoryTrace params initial initialLabels operations final finalLabels →
      ℕ → ℕ → Prop
  | nil {state : State n} {labels : RootLabels}
      (valid : state.Valid params) :
      PassMassHistory params root passCount
        (HistoryTrace.nil (labels := labels) valid) 0 0
  | cons {before middle after : State n}
      {beforeLabels afterLabels : RootLabels}
      {operation : Operation n} {operations : List (Operation n)}
      {tailBefore tailAfter : ℕ}
      (head : Step params before operation middle)
      (tail :
        HistoryTrace params middle
          (RootLabels.after beforeLabels operation)
          operations after afterLabels)
      (tailMass :
        PassMassHistory params root passCount
          tail tailBefore tailAfter) :
      PassMassHistory params root passCount
        (HistoryTrace.cons head tail)
        (operationPassBeforeMass before beforeLabels root passCount operation +
          tailBefore)
        (operationPassAfterMass before beforeLabels root passCount operation +
          tailAfter)

/-- Root-filtered conversion total along the same occurrence-free trace. -/
inductive RootConversionMassHistory {n : ℕ} (params : Parameters)
    (root : RootId) :
    ∀ {initial final : State n}
      {initialLabels finalLabels : RootLabels}
      {operations : List (Operation n)},
      HistoryTrace params initial initialLabels operations final finalLabels →
      ℕ → Prop
  | nil {state : State n} {labels : RootLabels}
      (valid : state.Valid params) :
      RootConversionMassHistory params root
        (HistoryTrace.nil (labels := labels) valid) 0
  | cons {before middle after : State n}
      {beforeLabels afterLabels : RootLabels}
      {operation : Operation n} {operations : List (Operation n)}
      {tailMass : ℕ}
      (head : Step params before operation middle)
      (tail :
        HistoryTrace params middle
          (RootLabels.after beforeLabels operation)
          operations after afterLabels)
      (tailConversions :
        RootConversionMassHistory params root tail tailMass) :
      RootConversionMassHistory params root
        (HistoryTrace.cons head tail)
        (operationRootConversionMass before beforeLabels root operation +
          tailMass)

/-- Sum of all conversions carrying one exact root label. -/
def rootConversionMass (occurrences : List ConversionOccurrence)
    (root : RootId) : ℕ :=
  ((occurrences.filter fun occurrence =>
      decide (occurrence.root = root)).map
    ConversionOccurrence.convertedMass).sum

/--
A proof-convenient finite width covering every pass count occurring in an
activity list.  It deliberately avoids a maximum operator.
-/
def activityTailSteps {n : ℕ}
    (occurrences : List (ActivityOccurrence n)) : ℕ :=
  (occurrences.map ActivityOccurrence.passCount).sum + 1

private theorem passCount_le_sum_of_mem
    {n : ℕ} {occurrence : ActivityOccurrence n}
    {occurrences : List (ActivityOccurrence n)}
    (member : occurrence ∈ occurrences) :
    occurrence.passCount ≤
      (occurrences.map ActivityOccurrence.passCount).sum := by
  induction occurrences with
  | nil =>
      simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with same | tailMember
      · subst occurrence
        simp
      · have tailLe := ih tailMember
        simp only [List.map_cons, List.sum_cons]
        omega

theorem passCount_lt_activityTailSteps
    {n : ℕ} {occurrence : ActivityOccurrence n}
    {occurrences : List (ActivityOccurrence n)}
    (member : occurrence ∈ occurrences) :
    occurrence.passCount < activityTailSteps occurrences := by
  unfold activityTailSteps
  have bound := passCount_le_sum_of_mem member
  omega

/--
Every actual high-count lineage key is represented by an index in the
canonical finite tail.
-/
theorem tailLineageRunKey_eq_threshold_add
    {n : ℕ} {occurrences : List (ActivityOccurrence n)}
    {threshold : ℕ} {key : LineageRunKey}
    (member : key ∈ tailLineageRunKeys occurrences threshold) :
    ∃ index < activityTailSteps occurrences,
      key.2 = threshold + index := by
  have keyMember :
      key ∈ lineageRunKeys occurrences :=
    (Finset.mem_filter.mp member).1
  have high : threshold ≤ key.2 :=
    (Finset.mem_filter.mp member).2
  obtain ⟨occurrence, occurrenceMember, keyEq⟩ :
      ∃ occurrence ∈ occurrences, occurrence.key = key := by
    simpa [lineageRunKeys] using keyMember
  have countLt :=
    passCount_lt_activityTailSteps occurrenceMember
  have occurrenceCountEq : occurrence.passCount = key.2 := by
    simpa [ActivityOccurrence.key] using congrArg Prod.snd keyEq
  let index := key.2 - threshold
  refine ⟨index, ?_, ?_⟩
  · dsimp [index]
    omega
  · dsimp [index]
    omega

theorem rootConversionMass_append
    (first second : List ConversionOccurrence) (root : RootId) :
    rootConversionMass (first ++ second) root =
      rootConversionMass first root + rootConversionMass second root := by
  simp [rootConversionMass, List.filter_append, List.map_append,
    List.sum_append]

private theorem rootConversionMass_operation
    {n : ℕ} (state : State n) (labels : RootLabels)
    (root : RootId) (operation : Operation n) :
    rootConversionMass
        (operationConversionOccurrences state labels operation) root =
      operationRootConversionMass state labels root operation := by
  cases operation with
  | convert blockId =>
      by_cases selected :
          (RootLabels.root? labels blockId).getD blockId = root
      · simp [rootConversionMass, operationConversionOccurrences,
          operationRootConversionMass, selected]
      · simp [rootConversionMass, operationConversionOccurrences,
          operationRootConversionMass, selected]
  | create creator =>
      simp [rootConversionMass, operationConversionOccurrences,
        operationRootConversionMass]
  | insert blockId element =>
      simp [rootConversionMass, operationConversionOccurrences,
        operationRootConversionMass]
  | delete blockId element =>
      simp [rootConversionMass, operationConversionOccurrences,
        operationRootConversionMass]
  | pass blockId matching =>
      simp [rootConversionMass, operationConversionOccurrences,
        operationRootConversionMass]
  | split blockId prefixLength =>
      simp [rootConversionMass, operationConversionOccurrences,
        operationRootConversionMass]
  | valueChange element delta =>
      simp [rootConversionMass, operationConversionOccurrences,
        operationRootConversionMass]

namespace RootConversionHistory

theorem toRootConversionMassHistory
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List ConversionOccurrence}
    (history :
      RootConversionHistory params initial initialLabels operations
        occurrences final finalLabels)
    (root : RootId) :
    RootConversionMassHistory params root history.erase
      (rootConversionMass occurrences root) := by
  induction history with
  | nil valid =>
      exact .nil valid
  | @cons before middle final beforeLabels finalLabels operation operations
      tailOccurrences head tail ih =>
      rw [rootConversionMass_append,
        rootConversionMass_operation]
      exact .cons head tail.erase ih

end RootConversionHistory

namespace FiberBatchHistory

theorem toPassMassHistory
    {n : ℕ} {params : Parameters} {root : RootId} {passCount : ℕ}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (ActivityOccurrence n)}
    {history :
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels}
    {batches : List (DescendantBatch params)}
    (summary :
      FiberBatchHistory params (root, passCount) history batches)
    (aligned : initialLabels.length = initial.blocks.length)
    (nonexempt : params.exemptPasses ≤ passCount) :
    PassMassHistory params root passCount history.erase
      (DescendantBatches.beforeMass batches)
      (DescendantBatches.afterMass batches) := by
  induction summary with
  | nil valid =>
      exact .nil valid
  | @skip before middle after beforeLabels afterLabels operation operations
      tailOccurrences batches head tail tailBatches headZero ih =>
      have nextAligned :
          (RootLabels.after beforeLabels operation).length =
            middle.blocks.length := by
        rw [RootLabels.length_after, aligned]
        exact head.2.1.blocks_length.symm
      have zero :=
        operationPassMass_eq_zero_of_activity_zero head aligned
          root passCount nonexempt headZero
      have tailMass := ih nextAligned
      simpa [zero.1, zero.2] using
        PassMassHistory.cons head tail.erase tailMass
  | @take before middle after beforeLabels afterLabels operation operations
      tailOccurrences batch batches head tail headBatch tailBatches ih =>
      have nextAligned :
          (RootLabels.after beforeLabels operation).length =
            middle.blocks.length := by
        rw [RootLabels.length_after, aligned]
        exact head.2.1.blocks_length.symm
      have tailMass := ih nextAligned
      have beforeEq :=
        headBatch.beforeMass_eq_operationPassBeforeMass
      have afterEq :=
        headBatch.afterMass_eq_operationPassAfterMass
      simpa [DescendantBatches.beforeMass,
        DescendantBatches.afterMass, beforeEq, afterEq] using
        PassMassHistory.cons head tail.erase tailMass

end FiberBatchHistory

namespace PassMassHistory

private theorem operationPassAfterMass_le_before
    {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    (step : Step params before operation after)
    (labels : RootLabels)
    (aligned : labels.length = before.blocks.length)
    (root : RootId) (passCount : ℕ) :
    operationPassAfterMass before labels root passCount operation ≤
      operationPassBeforeMass before labels root passCount operation := by
  cases operation with
  | convert blockId =>
      simp [operationPassAfterMass, operationPassBeforeMass]
  | create creator =>
      simp [operationPassAfterMass, operationPassBeforeMass]
  | insert blockId element =>
      simp [operationPassAfterMass, operationPassBeforeMass]
  | delete blockId element =>
      simp [operationPassAfterMass, operationPassBeforeMass]
  | @pass sourceId matching =>
      obtain ⟨source, sourceFound, _afterFound⟩ :=
        step.2.1.pass_source?
      have sourceLt :
          sourceId < before.blocks.length :=
        (List.getElem?_eq_some_iff.mp sourceFound).choose
      have labelLt : sourceId < labels.length := by
        simpa [aligned] using sourceLt
      let sourceRoot : RootId := labels[sourceId]
      have rootFound :
          RootLabels.root? labels sourceId = some sourceRoot :=
        List.getElem?_eq_getElem labelLt
      have validMatching :
          MatchingValid params before sourceId source matching := by
        cases effectEq : step.2.1 with
        | pass found valid blocksEq valuesEq =>
            rename_i actualSource
            have sourceEq : actualSource = source := by
              rw [sourceFound] at found
              exact (Option.some.inj found).symm
            subst actualSource
            exact valid
      by_cases selected :
          sourceRoot = root ∧ source.passCount = passCount
      · simp [operationPassAfterMass, operationPassBeforeMass,
          sourceFound, rootFound, selected]
        have balance := validMatching.removeLosers_length_add
        omega
      · simp [operationPassAfterMass, operationPassBeforeMass,
          sourceFound, rootFound, selected]
  | split blockId prefixLength =>
      simp [operationPassAfterMass, operationPassBeforeMass]
  | valueChange element delta =>
      simp [operationPassAfterMass, operationPassBeforeMass]

theorem after_le_before
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {history :
      HistoryTrace params initial initialLabels operations final finalLabels}
    {root : RootId} {passCount beforeMass afterMass : ℕ}
    (summary :
      PassMassHistory params root passCount history beforeMass afterMass)
    (aligned : initialLabels.length = initial.blocks.length) :
    afterMass ≤ beforeMass := by
  induction summary with
  | nil =>
      rfl
  | @cons before middle after beforeLabels afterLabels operation operations
      tailBefore tailAfter head tail tailMass ih =>
      have nextAligned :
          (RootLabels.after beforeLabels operation).length =
            middle.blocks.length := by
        rw [RootLabels.length_after, aligned]
        exact head.2.1.blocks_length.symm
      have headLe :=
        operationPassAfterMass_le_before head beforeLabels aligned
          root passCount
      have tailLe := ih nextAligned
      omega

theorem successor_balance
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {history :
      HistoryTrace params initial initialLabels operations final finalLabels}
    {root : RootId} {passCount : ℕ}
    {currentBefore currentAfter nextBefore nextAfter : ℕ}
    (current :
      PassMassHistory params root passCount history
        currentBefore currentAfter)
    (next :
      PassMassHistory params root (passCount + 1) history
        nextBefore nextAfter)
    (aligned : initialLabels.length = initial.blocks.length)
    (growingZero : GrowingPassCountZero initial) :
    nextBefore +
        passCountMass final finalLabels root (passCount + 1) ≤
      currentAfter +
        passCountMass initial initialLabels root (passCount + 1) := by
  induction current generalizing nextBefore nextAfter with
  | nil =>
      cases next
      simp
  | @cons before middle after beforeLabels afterLabels operation operations
      tailBefore tailAfter head tail tailMass ih =>
      cases next with
      | cons nextHead nextTail nextTailMass =>
          rename_i nextMiddle nextTailBefore nextTailAfter
          have middleEq : nextMiddle = middle :=
            Effect.after_eq nextHead.2.1 head.2.1
          subst nextMiddle
          have tailHistoryEq : nextTail = tail := Subsingleton.elim _ _
          cases tailHistoryEq
          have nextAligned :
              (RootLabels.after beforeLabels operation).length =
                middle.blocks.length := by
            rw [RootLabels.length_after, aligned]
            exact head.2.1.blocks_length.symm
          have nextGrowingZero :
              GrowingPassCountZero middle :=
            growingZero.effect head.2.1
          have localBalance :=
            head.2.1.passCountMass_successor_balance beforeLabels aligned
              growingZero root passCount
          have tailBalance :=
            ih nextTailMass nextAligned nextGrowingZero
          omega

theorem zero_before_add_final_le_conversions_add_initial
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {history :
      HistoryTrace params initial initialLabels operations final finalLabels}
    {root : RootId} {beforeMass afterMass conversionMass : ℕ}
    (passes :
      PassMassHistory params root 0 history beforeMass afterMass)
    (conversions :
      RootConversionMassHistory params root history conversionMass)
    (aligned : initialLabels.length = initial.blocks.length)
    (growingZero : GrowingPassCountZero initial) :
    beforeMass + shrinkingZeroMass final finalLabels root ≤
      conversionMass + shrinkingZeroMass initial initialLabels root := by
  induction passes generalizing conversionMass with
  | nil =>
      cases conversions
      simp
  | @cons before middle after beforeLabels afterLabels operation operations
      tailBefore tailAfter head tail tailPasses ih =>
      cases conversions with
      | cons conversionHead conversionTail tailConversions =>
          rename_i conversionMiddle tailConversionMass
          have middleEq : conversionMiddle = middle :=
            Effect.after_eq conversionHead.2.1 head.2.1
          subst conversionMiddle
          have tailHistoryEq : conversionTail = tail :=
            Subsingleton.elim _ _
          cases tailHistoryEq
          have nextAligned :
              (RootLabels.after beforeLabels operation).length =
                middle.blocks.length := by
            rw [RootLabels.length_after, aligned]
            exact head.2.1.blocks_length.symm
          have nextGrowingZero :
              GrowingPassCountZero middle :=
            growingZero.effect head.2.1
          have localBalance :=
            head.2.1.shrinkingZeroMass_balance beforeLabels aligned
              growingZero root
          have tailBound :=
            ih tailConversions nextAligned nextGrowingZero
          omega

end PassMassHistory

namespace HistoryTrace

theorem exists_passMassHistory
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    (history :
      HistoryTrace params initial initialLabels operations final finalLabels)
    (root : RootId) (passCount : ℕ) :
    ∃ beforeMass afterMass,
      PassMassHistory params root passCount history beforeMass afterMass := by
  induction history with
  | nil valid =>
      exact ⟨0, 0, .nil valid⟩
  | @cons before middle after beforeLabels afterLabels operation operations
      head tail ih =>
      obtain ⟨tailBefore, tailAfter, tailMass⟩ := ih
      exact
        ⟨operationPassBeforeMass before beforeLabels root passCount
            operation + tailBefore,
          operationPassAfterMass before beforeLabels root passCount
            operation + tailAfter,
          .cons head tail tailMass⟩

end HistoryTrace

namespace PassMassHistory

theorem before_le_countZero_of_initial
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {history :
      HistoryTrace params initial initialLabels operations final finalLabels}
    {root : RootId} {passCount beforeMass afterMass : ℕ}
    (summary :
      PassMassHistory params root passCount history beforeMass afterMass)
    (initialState : initial.Initial params)
    (aligned : initialLabels.length = initial.blocks.length) :
    ∃ zeroBefore zeroAfter,
      PassMassHistory params root 0 history zeroBefore zeroAfter ∧
        beforeMass ≤ zeroBefore := by
  have initialGrowingZero : GrowingPassCountZero initial := by
    intro blockId block found
    rw [State.block?, initialState.2] at found
    simp at found
  induction passCount generalizing beforeMass afterMass with
  | zero =>
      exact ⟨beforeMass, afterMass, summary, Nat.le_refl _⟩
  | succ passCount ih =>
      obtain ⟨currentBefore, currentAfter, current⟩ :=
        history.exists_passMassHistory root passCount
      have temporal :=
        current.successor_balance summary aligned initialGrowingZero
      have initialMassZero :
          passCountMass initial initialLabels root (passCount + 1) = 0 := by
        simp [passCountMass, passCountMassOf, initialState.2]
      rw [initialMassZero, Nat.add_zero] at temporal
      have currentAfterLe :=
        current.after_le_before aligned
      obtain ⟨zeroBefore, zeroAfter, zeroSummary, zeroBound⟩ :=
        ih current
      exact
        ⟨zeroBefore, zeroAfter, zeroSummary, by omega⟩

end PassMassHistory

namespace FiberBatchHistory

/--
The complete population of any nonexempt fiber is bounded by the exact total
mass converted under its root label.
-/
theorem beforeMass_le_rootConversionMass_of_initial
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {activityOccurrences : List (ActivityOccurrence n)}
    {conversionOccurrences : List ConversionOccurrence}
    {root : RootId} {passCount : ℕ}
    {batches : List (DescendantBatch params)}
    {activityHistory :
      ActivityHistory params initial initialLabels operations
        activityOccurrences final finalLabels}
    (summary :
      FiberBatchHistory params (root, passCount)
        activityHistory batches)
    (conversionHistory :
      RootConversionHistory params initial initialLabels operations
        conversionOccurrences final finalLabels)
    (initialState : initial.Initial params)
    (aligned : initialLabels.length = initial.blocks.length)
    (nonexempt : params.exemptPasses ≤ passCount) :
    DescendantBatches.beforeMass batches ≤
      rootConversionMass conversionOccurrences root := by
  have passMass :=
    summary.toPassMassHistory aligned nonexempt
  obtain ⟨zeroBefore, zeroAfter, zeroPasses, fiberToZero⟩ :=
    passMass.before_le_countZero_of_initial initialState aligned
  have conversionMass :=
    conversionHistory.toRootConversionMassHistory root
  have traceProofEq :
      conversionHistory.erase = activityHistory.erase :=
    Subsingleton.elim _ _
  cases traceProofEq
  have initialGrowingZero : GrowingPassCountZero initial := by
    intro blockId block found
    rw [State.block?, initialState.2] at found
    simp at found
  have zeroToConversion :=
    zeroPasses.zero_before_add_final_le_conversions_add_initial
      conversionMass aligned initialGrowingZero
  have initialShrinkingZero :
      shrinkingZeroMass initial initialLabels root = 0 := by
    simp [shrinkingZeroMass, shrinkingZeroMassOf, initialState.2]
  rw [initialShrinkingZero, Nat.add_zero] at zeroToConversion
  omega

end FiberBatchHistory

namespace ActivityHistory

/--
Every consecutive nonexempt fiber of an aligned history from an initial state
has automatic temporal coverage.  No re-entry premise is supplied by callers.
-/
theorem successorFiberCoverage_of_initial
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (ActivityOccurrence n)}
    (history :
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels)
    (initialState : initial.Initial params)
    (aligned : initialLabels.length = initial.blocks.length)
    (root : RootId) (passCount : ℕ)
    (nonexempt : params.exemptPasses ≤ passCount) :
    SuccessorFiberCoverage history root passCount := by
  have initialGrowingZero : GrowingPassCountZero initial := by
    intro blockId block found
    rw [State.block?, initialState.2] at found
    simp at found
  intro currentBatches nextBatches current next
  have currentMass :=
    current.toPassMassHistory aligned nonexempt
  have nextNonexempt :
      params.exemptPasses ≤ passCount + 1 := by omega
  have nextMass :=
    next.toPassMassHistory aligned nextNonexempt
  have temporal :=
    currentMass.successor_balance nextMass aligned initialGrowingZero
  have initialMassZero :
      passCountMass initial initialLabels root (passCount + 1) = 0 := by
    simp [passCountMass, passCountMassOf, initialState.2]
  rw [initialMassZero, Nat.add_zero] at temporal
  omega

/--
Initial histories construct the genuine adjacent-fiber layer directly; the
former explicit `SuccessorFiberCoverage` argument is discharged internally.
-/
theorem exists_nonexemptSuccessorFiberLayer_of_initial
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (ActivityOccurrence n)}
    (history :
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels)
    (initialState : initial.Initial params)
    (aligned : initialLabels.length = initial.blocks.length)
    (root : RootId) (passCount : ℕ)
    (nonexempt : params.exemptPasses ≤ passCount) :
    ∃ (currentBatches nextBatches : List (DescendantBatch params)),
      FiberBatchHistory params (root, passCount)
          history currentBatches ∧
        FiberBatchHistory params (root, passCount + 1)
          history nextBatches ∧
        Nonempty
          (FiberLayer params
            (DescendantBatches.beforeMass currentBatches)
            (DescendantBatches.beforeMass nextBatches)
            (lineageRunActivity occurrences (root, passCount))) := by
  exact history.exists_nonexemptSuccessorFiberLayer
    aligned root passCount nonexempt
    (history.successorFiberCoverage_of_initial
      initialState aligned root passCount nonexempt)

/--
One coherent choice of genuine batches builds both the logarithmic decay
prefix and an arbitrary finite tail.  The two profiles share their boundary
mass definitionally up to arithmetic normalization.
-/
theorem exists_decayPrefixAndTailProfiles_of_initial
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (ActivityOccurrence n)}
    (history :
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels)
    (initialState : initial.Initial params)
    (aligned : initialLabels.length = initial.blocks.length)
    (root : RootId) (tailSteps : ℕ) :
    ∃ (prefixProfile :
          FiberProfile params (FiberProfile.decaySteps params))
        (tail : FiberProfile params tailSteps)
        (initialBatches : List (DescendantBatch params)),
      FiberBatchHistory params (root, params.exemptPasses)
          history initialBatches ∧
        prefixProfile.mass 0 =
          DescendantBatches.beforeMass initialBatches ∧
        tail.mass 0 =
          prefixProfile.mass (FiberProfile.decaySteps params) ∧
        (∀ index,
          tail.activity index =
            lineageRunActivity occurrences
              (root,
                FiberProfile.insignificantThreshold params + index)) ∧
        4 * params.valueBound * tail.totalActivity ≤
          prefixProfile.mass 0 := by
  classical
  have summaries :
      ∀ offset : ℕ,
        ∃ batches : List (DescendantBatch params),
          FiberBatchHistory params
            (root, params.exemptPasses + offset)
            history batches := by
    intro offset
    apply history.exists_nonexemptFiberBatches aligned
    omega
  let batches (offset : ℕ) : List (DescendantBatch params) :=
    Classical.choose (summaries offset)
  have batchSummary (offset : ℕ) :
      FiberBatchHistory params
        (root, params.exemptPasses + offset)
        history (batches offset) :=
    Classical.choose_spec (summaries offset)
  let profile (base steps : ℕ) : FiberProfile params steps :=
    { mass := fun index =>
        DescendantBatches.beforeMass (batches (base + index))
      activity := fun index =>
        lineageRunActivity occurrences
          (root, params.exemptPasses + (base + index))
      layer := by
        intro index indexLt
        have current :=
          batchSummary (base + index)
        have nextRaw :=
          batchSummary (base + (index + 1))
        have next :
            FiberBatchHistory params
              (root,
                (params.exemptPasses + (base + index)) + 1)
              history (batches (base + (index + 1))) := by
          simpa only [Nat.add_assoc] using nextRaw
        have coverage :
            SuccessorFiberCoverage history root
              (params.exemptPasses + (base + index)) :=
          history.successorFiberCoverage_of_initial initialState aligned
            root (params.exemptPasses + (base + index)) (by omega)
        exact current.toSuccessorFiberLayer next coverage }
  let prefixProfile :=
    profile 0 (FiberProfile.decaySteps params)
  let tail :=
    profile (FiberProfile.decaySteps params) tailSteps
  have continuous :
      tail.mass 0 ≤
        prefixProfile.mass (FiberProfile.decaySteps params) := by
    dsimp [tail, prefixProfile, profile]
    simp
  have scaled :=
    prefixProfile.insignificant_tail_scaled_le_initialMass tail continuous
  exact
    ⟨prefixProfile, tail, batches 0, by
      simpa using batchSummary 0,
      by
        dsimp [prefixProfile, profile],
      by
        dsimp [tail, prefixProfile, profile]
        simp,
      by
        intro index
        dsimp [tail, profile]
        congr 2
        simp [FiberProfile.insignificantThreshold,
          FiberProfile.decaySteps, Nat.add_assoc],
      scaled⟩

/--
Profile construction already charged to the exact conversion total of its
root.  This is the per-root input required by global charge aggregation.
-/
theorem exists_decayProfiles_le_rootConversion_of_initial
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {activityOccurrences : List (ActivityOccurrence n)}
    {conversionOccurrences : List ConversionOccurrence}
    (history :
      ActivityHistory params initial initialLabels operations
        activityOccurrences final finalLabels)
    (conversionHistory :
      RootConversionHistory params initial initialLabels operations
        conversionOccurrences final finalLabels)
    (initialState : initial.Initial params)
    (aligned : initialLabels.length = initial.blocks.length)
    (root : RootId) (tailSteps : ℕ) :
    ∃ (prefixProfile :
          FiberProfile params (FiberProfile.decaySteps params))
        (tail : FiberProfile params tailSteps)
        (initialBatches : List (DescendantBatch params)),
      FiberBatchHistory params (root, params.exemptPasses)
          history initialBatches ∧
        prefixProfile.mass 0 =
          DescendantBatches.beforeMass initialBatches ∧
        prefixProfile.mass 0 ≤
          rootConversionMass conversionOccurrences root ∧
        tail.mass 0 =
          prefixProfile.mass (FiberProfile.decaySteps params) ∧
        (∀ index,
          tail.activity index =
            lineageRunActivity activityOccurrences
              (root,
                FiberProfile.insignificantThreshold params + index)) ∧
        4 * params.valueBound * tail.totalActivity ≤
          prefixProfile.mass 0 := by
  obtain
    ⟨prefixProfile, tail, initialBatches, initialSummary,
      initialMass, continuous, tailActivityEq, scaled⟩ :=
    history.exists_decayPrefixAndTailProfiles_of_initial
      initialState aligned root tailSteps
  have convertedBound :=
    initialSummary.beforeMass_le_rootConversionMass_of_initial
      conversionHistory initialState aligned (by omega)
  exact
    ⟨prefixProfile, tail, initialBatches, initialSummary,
      initialMass, by simpa [initialMass] using convertedBound,
      continuous, tailActivityEq, scaled⟩

end ActivityHistory

namespace Trace

/--
Trace-level construction of a real adjacent nonexempt fiber layer, including
its chronological batch witnesses and with no external coverage hypothesis.
-/
theorem exists_nonexemptSuccessorFiberLayer
    {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (initialState : initial.Initial params)
    (trace : Trace params initial operations final)
    (root : RootId) (passCount : ℕ)
    (nonexempt : params.exemptPasses ≤ passCount) :
    ∃ (finalLabels : RootLabels)
        (occurrences : List (ActivityOccurrence n))
        (history :
          ActivityHistory params initial [] operations occurrences
            final finalLabels)
        (currentBatches nextBatches : List (DescendantBatch params)),
      FiberBatchHistory params (root, passCount)
          history currentBatches ∧
        FiberBatchHistory params (root, passCount + 1)
          history nextBatches ∧
        Nonempty
          (FiberLayer params
            (DescendantBatches.beforeMass currentBatches)
            (DescendantBatches.beforeMass nextBatches)
            (lineageRunActivity occurrences (root, passCount))) := by
  obtain ⟨finalLabels, lineageHistory, aligned⟩ :=
    HistoryTrace.lift_initial initialState trace
  obtain ⟨occurrences, activityHistory⟩ :=
    ActivityHistory.lift lineageHistory
  obtain
    ⟨currentBatches, nextBatches, current, next, layer⟩ :=
    activityHistory.exists_nonexemptSuccessorFiberLayer_of_initial
      initialState (by simp [initialState.2])
      root passCount nonexempt
  exact
    ⟨finalLabels, occurrences, activityHistory,
      currentBatches, nextBatches, current, next, layer⟩

/--
Trace-level logarithmic prefix and finite insignificant tail for one root.
Taking `tailSteps = operations.length` is the canonical whole-trace choice.
-/
theorem exists_decayPrefixAndTailProfiles
    {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (initialState : initial.Initial params)
    (trace : Trace params initial operations final)
    (root : RootId) (tailSteps : ℕ) :
    ∃ (finalLabels : RootLabels)
        (occurrences : List (ActivityOccurrence n))
        (_history :
          ActivityHistory params initial [] operations occurrences
            final finalLabels)
        (prefixProfile :
          FiberProfile params (FiberProfile.decaySteps params))
        (tail : FiberProfile params tailSteps)
        (initialBatches : List (DescendantBatch params)),
      FiberBatchHistory params (root, params.exemptPasses)
          _history initialBatches ∧
        prefixProfile.mass 0 =
          DescendantBatches.beforeMass initialBatches ∧
        tail.mass 0 =
          prefixProfile.mass (FiberProfile.decaySteps params) ∧
        (∀ index,
          tail.activity index =
            lineageRunActivity occurrences
              (root,
                FiberProfile.insignificantThreshold params + index)) ∧
        4 * params.valueBound * tail.totalActivity ≤
          prefixProfile.mass 0 := by
  obtain ⟨finalLabels, lineageHistory, _aligned⟩ :=
    HistoryTrace.lift_initial initialState trace
  obtain ⟨occurrences, activityHistory⟩ :=
    ActivityHistory.lift lineageHistory
  obtain
    ⟨prefixProfile, tail, initialBatches, initialSummary,
      initialMass, continuous, tailActivityEq, scaled⟩ :=
    activityHistory.exists_decayPrefixAndTailProfiles_of_initial
      initialState (by simp [initialState.2]) root tailSteps
  exact
    ⟨finalLabels, occurrences, activityHistory,
      prefixProfile, tail, initialBatches, initialSummary,
      initialMass, continuous, tailActivityEq, scaled⟩

/--
Each root therefore supplies a concrete decay charge.  Its converted field is
the selected nonexempt-prefix population; the remaining global bridge is to
charge these populations to root conversion occurrences.
-/
theorem exists_rootDecayCharge
    {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (initialState : initial.Initial params)
    (trace : Trace params initial operations final)
    (root : RootId) (tailSteps : ℕ) :
    ∃ charge : RootDecayCharge (4 * params.valueBound),
      ∃ (finalLabels : RootLabels)
          (occurrences : List (ActivityOccurrence n))
          (_history :
            ActivityHistory params initial [] operations occurrences
              final finalLabels)
          (prefixProfile :
            FiberProfile params (FiberProfile.decaySteps params))
          (tail : FiberProfile params tailSteps),
        charge.convertedMass = prefixProfile.mass 0 ∧
          charge.tailActivity = tail.totalActivity := by
  obtain
    ⟨finalLabels, occurrences, history, prefixProfile, tail,
      initialBatches, initialSummary, initialMass,
      _continuous, _tailActivityEq, scaled⟩ :=
    trace.exists_decayPrefixAndTailProfiles
      initialState root tailSteps
  let charge : RootDecayCharge (4 * params.valueBound) :=
    { convertedMass := prefixProfile.mass 0
      tailActivity := tail.totalActivity
      scaled_tail_le := scaled }
  exact
    ⟨charge, finalLabels, occurrences, history, prefixProfile, tail,
      rfl, rfl⟩

end Trace

end Splay.Interface
