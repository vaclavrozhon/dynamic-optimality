import MultiSplay.InterfaceNeutralization

/-!
# A common split in the persistent strict interface

Two ordinary growing records at the removed pivot are retired, and each child
root is removed from its current singleton block and returned to value one.
The source singleton may already be shrinking after intervening splay work.
All historical records remain in storage with their original identifiers.
-/

namespace MultiSplay.InterfaceForest

open Splay.Interface

variable {n : Nat}

structure SplitBoundary (state : State n) where
  left : Element n
  right : Element n
  childrenNe : right ≠ left
  growingLeft : BlockId
  growingRight : BlockId
  sourceLeft : BlockId
  sourceRight : BlockId
  growingIdsNe : growingRight ≠ growingLeft
  sourceIdsNe : sourceRight ≠ sourceLeft
  growingLeftBlock : Block n
  growingRightBlock : Block n
  sourceLeftBlock : Block n
  sourceRightBlock : Block n
  growingLeftFound : state.block? growingLeft = some growingLeftBlock
  growingRightFound : state.block? growingRight = some growingRightBlock
  sourceLeftFound : state.block? sourceLeft = some sourceLeftBlock
  sourceRightFound : state.block? sourceRight = some sourceRightBlock
  growingLeftMode : growingLeftBlock.mode = .growing
  growingRightMode : growingRightBlock.mode = .growing
  sourceLeftSingleton : sourceLeftBlock.elements = [left]
  sourceRightSingleton : sourceRightBlock.elements = [right]
  sourceLeftRetired : sourceLeftBlock.mode = .shrinking ∨ sourceLeft = growingLeft ∨ sourceLeft = growingRight
  sourceRightRetired : sourceRightBlock.mode = .shrinking ∨ sourceRight = growingLeft ∨ sourceRight = growingRight
  leftValue : state.value left ≤ 3
  rightValue : state.value right ≤ 3

def retire (state : State n) (first second : BlockId) : State n := convert (convert state first) second

theorem convert_lookup (state : State n) (target id : BlockId) (block : Block n)
    (found : state.block? id = some block) :
    (convert state target).block? id = some (if target = id then {block with mode := .shrinking} else block) := by
  change (state.blocks.modify target (fun item => {item with mode := .shrinking}))[id]? = _
  rw [List.getElem?_modify]
  change (state.blocks[id]?).map (fun item => if target = id then {item with mode := .shrinking} else item) = _
  rw [show state.blocks[id]? = some block from found]
  rfl

theorem retire_lookup (state : State n) (first second id : BlockId) (block : Block n)
    (found : state.block? id = some block)
    (covered : block.mode = .shrinking ∨ id = first ∨ id = second) :
    (retire state first second).block? id = some {block with mode := .shrinking} := by
  have inner := convert_lookup state first id block found
  have outer := convert_lookup (convert state first) second id _ inner
  change (convert (convert state first) second).block? id = _
  rw [outer]
  rcases block with ⟨creator, passCount, mode, elements⟩
  cases mode <;> by_cases isFirst : first = id <;> by_cases isSecond : second = id <;>
    simp_all [eq_comm]

def SplitBoundary.retired {state : State n} (boundary : SplitBoundary state) : State n :=
  retire state boundary.growingLeft boundary.growingRight

def SplitBoundary.afterLeft {state : State n} (boundary : SplitBoundary state) : State n :=
  detachNeutral boundary.retired boundary.sourceLeft boundary.left

def SplitBoundary.final {state : State n} (boundary : SplitBoundary state) : State n :=
  detachNeutral boundary.afterLeft boundary.sourceRight boundary.right

def SplitBoundary.word {state : State n} (boundary : SplitBoundary state) : List (Operation n) :=
  [.convert boundary.growingLeft, .convert boundary.growingRight] ++
    detachNeutralWord state boundary.sourceLeft boundary.left ++
    detachNeutralWord state boundary.sourceRight boundary.right

theorem SplitBoundary.trace {params : Parameters} {state : State n} (boundary : SplitBoundary state)
    (valid : state.Valid params) : Trace params state boundary.word boundary.final := by
  have first := convert_step state boundary.growingLeft boundary.growingLeftBlock valid
    boundary.growingLeftFound boundary.growingLeftMode
  have secondFound : (convert state boundary.growingLeft).block? boundary.growingRight = some boundary.growingRightBlock := by
    simp [convert, modifyBlock, State.block?, List.getElem?_modify, boundary.growingIdsNe.symm,
      show state.blocks[boundary.growingRight]? = some boundary.growingRightBlock from boundary.growingRightFound]
  have second := convert_step _ boundary.growingRight boundary.growingRightBlock first.2.2 secondFound boundary.growingRightMode
  have leftFound := retire_lookup state boundary.growingLeft boundary.growingRight boundary.sourceLeft
    boundary.sourceLeftBlock boundary.sourceLeftFound boundary.sourceLeftRetired
  have leftRun := detachNeutral_trace boundary.retired boundary.sourceLeft {boundary.sourceLeftBlock with mode := .shrinking}
    boundary.left second.2.2 leftFound rfl (by simp [boundary.sourceLeftSingleton])
  have rightFound : boundary.afterLeft.block? boundary.sourceRight = some {boundary.sourceRightBlock with mode := .shrinking} := by
    have original := retire_lookup state boundary.growingLeft boundary.growingRight boundary.sourceRight
      boundary.sourceRightBlock boundary.sourceRightFound boundary.sourceRightRetired
    simp only [SplitBoundary.afterLeft, detachNeutral, setValue, delete, modifyBlock, State.block?,
      List.getElem?_modify, boundary.sourceIdsNe.symm, if_false, Option.map_id]
    change (boundary.retired.blocks[boundary.sourceRight]?).map id = _
    rw [Option.map_id]
    exact original
  have rightRun := detachNeutral_trace boundary.afterLeft boundary.sourceRight {boundary.sourceRightBlock with mode := .shrinking}
    boundary.right (trace_final_valid leftRun) rightFound rfl (by simp [boundary.sourceRightSingleton])
  have leftWord : detachNeutralWord boundary.retired boundary.sourceLeft boundary.left =
      detachNeutralWord state boundary.sourceLeft boundary.left := rfl
  have rightWord : detachNeutralWord boundary.afterLeft boundary.sourceRight boundary.right =
      detachNeutralWord state boundary.sourceRight boundary.right := by
    simp [detachNeutralWord, neutralizeWord, SplitBoundary.afterLeft, detachNeutral, setValue, delete,
      modifyBlock, SplitBoundary.retired, retire, convert, boundary.childrenNe]
  have rest := trace_append leftRun rightRun
  rw [leftWord, rightWord] at rest
  exact .cons first (.cons second rest)

theorem SplitBoundary.word_length {state : State n} (boundary : SplitBoundary state) : boundary.word.length ≤ 8 := by
  simp only [SplitBoundary.word, detachNeutralWord, neutralizeWord, List.length_append,
    List.length_cons, List.length_nil, List.length_replicate]
  have l := boundary.leftValue
  have r := boundary.rightValue
  omega

@[simp] theorem SplitBoundary.inserts {state : State n} (boundary : SplitBoundary state) :
    totalInserts boundary.word = 0 := by
  simp [SplitBoundary.word, detachNeutralWord, totalInserts, neutralizeWord, Operation.insertCount]

@[simp] theorem SplitBoundary.increases {state : State n} (boundary : SplitBoundary state) :
    totalIncreases boundary.word = 0 := by
  simp [SplitBoundary.word, detachNeutralWord, totalIncreases, neutralizeWord, Operation.increaseCount]

@[simp] theorem SplitBoundary.activity {state : State n} (boundary : SplitBoundary state) :
    totalActivity boundary.word = 0 := by
  simp [SplitBoundary.word, detachNeutralWord, totalActivity, neutralizeWord, Operation.activity]

theorem SplitBoundary.decreases {state : State n} (boundary : SplitBoundary state) :
    totalDecreases boundary.word ≤ 4 := by
  simp only [SplitBoundary.word, detachNeutralWord, totalDecreases_append]
  have l := neutralize_decreases state boundary.left
  have r := neutralize_decreases state boundary.right
  change 0 + (0 + totalDecreases (neutralizeWord state boundary.left)) +
    (0 + totalDecreases (neutralizeWord state boundary.right)) ≤ 4
  have leftCap := boundary.leftValue
  have rightCap := boundary.rightValue
  omega

@[simp] theorem SplitBoundary.final_blocks_length {state : State n} (boundary : SplitBoundary state) :
    boundary.final.blocks.length = state.blocks.length := by
  simp [SplitBoundary.final, SplitBoundary.afterLeft, SplitBoundary.retired, retire,
    detachNeutral, setValue, delete, convert, modifyBlock]

@[simp] theorem SplitBoundary.final_left_value {state : State n} (boundary : SplitBoundary state) :
    boundary.final.value boundary.left = 1 := by
  simp [SplitBoundary.final, SplitBoundary.afterLeft, detachNeutral, setValue, delete,
    modifyBlock, boundary.childrenNe.symm]

@[simp] theorem SplitBoundary.final_right_value {state : State n} (boundary : SplitBoundary state) :
    boundary.final.value boundary.right = 1 := by
  simp [SplitBoundary.final, detachNeutral, setValue]

theorem SplitBoundary.final_other_value {state : State n} (boundary : SplitBoundary state)
    (x : Element n) (left : x ≠ boundary.left) (right : x ≠ boundary.right) :
    boundary.final.value x = state.value x := by
  simp [SplitBoundary.final, SplitBoundary.afterLeft, SplitBoundary.retired, retire,
    detachNeutral, setValue, delete, convert, modifyBlock, left, right]

theorem SplitBoundary.retained_lookup {state : State n} (boundary : SplitBoundary state)
    (id : BlockId) (block : Block n) (found : state.block? id = some block)
    (notGrowingLeft : id ≠ boundary.growingLeft) (notGrowingRight : id ≠ boundary.growingRight)
    (notSourceLeft : id ≠ boundary.sourceLeft) (notSourceRight : id ≠ boundary.sourceRight) :
    boundary.final.block? id = some block := by
  simp only [SplitBoundary.final, SplitBoundary.afterLeft, SplitBoundary.retired, retire,
    detachNeutral, setValue, delete, convert, modifyBlock, State.block?, List.getElem?_modify,
    notGrowingLeft.symm, notGrowingRight.symm, notSourceLeft.symm, notSourceRight.symm,
    if_false]
  change ((((state.blocks[id]?).map _).map _).map _).map _ = _
  rw [show state.blocks[id]? = some block from found]
  rfl

end MultiSplay.InterfaceForest
