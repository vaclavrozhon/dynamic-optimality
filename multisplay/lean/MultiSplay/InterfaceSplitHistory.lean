import MultiSplay.InterfaceCommonSplit

/-! # Exact retained fields and removed root memberships after a common split -/

namespace MultiSplay.InterfaceForest

open Splay.Interface

variable {n : Nat}

theorem modify_lookup (state : State n) (target id : BlockId) (f : Block n → Block n) (block : Block n)
    (found : state.block? id = some block) :
    (modifyBlock state target f).block? id = some (if target = id then f block else block) := by
  change (state.blocks.modify target f)[id]? = _
  rw [List.getElem?_modify]
  change (state.blocks[id]?).map (fun b => if target = id then f b else b) = _
  rw [show state.blocks[id]? = some block from found]
  rfl

def SplitBoundary.record {state : State n} (boundary : SplitBoundary state) (id : BlockId) (block : Block n) : Block n :=
  let first := if boundary.growingLeft = id then {block with mode := .shrinking} else block
  let second := if boundary.growingRight = id then {first with mode := .shrinking} else first
  let third := if boundary.sourceLeft = id then {second with elements := second.elements.erase boundary.left} else second
  if boundary.sourceRight = id then {third with elements := third.elements.erase boundary.right} else third

theorem SplitBoundary.final_lookup {state : State n} (boundary : SplitBoundary state)
    (id : BlockId) (block : Block n) (found : state.block? id = some block) :
    boundary.final.block? id = some (boundary.record id block) := by
  have first := modify_lookup state boundary.growingLeft id (fun b => {b with mode := .shrinking}) block found
  have second := modify_lookup _ boundary.growingRight id (fun b => {b with mode := .shrinking}) _ first
  have third := modify_lookup _ boundary.sourceLeft id (fun b => {b with elements := b.elements.erase boundary.left}) _ second
  have fourth := modify_lookup _ boundary.sourceRight id (fun b => {b with elements := b.elements.erase boundary.right}) _ third
  exact fourth

@[simp] theorem SplitBoundary.record_creator {state : State n} (boundary : SplitBoundary state) (id : BlockId) (block : Block n) :
    (boundary.record id block).creator = block.creator := by
  unfold SplitBoundary.record
  split_ifs <;> rfl

@[simp] theorem SplitBoundary.record_passCount {state : State n} (boundary : SplitBoundary state) (id : BlockId) (block : Block n) :
    (boundary.record id block).passCount = block.passCount := by
  unfold SplitBoundary.record
  split_ifs <;> rfl

theorem SplitBoundary.record_growing {state : State n} (boundary : SplitBoundary state) (id : BlockId) (block : Block n)
    (growing : (boundary.record id block).mode = .growing) : block.mode = .growing := by
  by_cases gl : boundary.growingLeft = id <;> by_cases gr : boundary.growingRight = id <;>
    by_cases sl : boundary.sourceLeft = id <;> by_cases sr : boundary.sourceRight = id <;>
    simpa [SplitBoundary.record, gl, gr, sl, sr] using growing

theorem SplitBoundary.record_elements {state : State n} (boundary : SplitBoundary state) (id : BlockId) (block : Block n) :
    (boundary.record id block).elements.Sublist block.elements := by
  by_cases gl : boundary.growingLeft = id <;> by_cases gr : boundary.growingRight = id <;>
    by_cases sl : boundary.sourceLeft = id <;> by_cases sr : boundary.sourceRight = id <;>
    simp only [SplitBoundary.record, gl, gr, sl, sr, if_pos, if_false] <;>
    first | exact List.Sublist.refl _ | exact List.erase_sublist | exact List.erase_sublist.trans List.erase_sublist

theorem SplitBoundary.record_left_empty {state : State n} (boundary : SplitBoundary state) :
    (boundary.record boundary.sourceLeft boundary.sourceLeftBlock).elements = [] := by
  unfold SplitBoundary.record
  split_ifs <;> simp_all [boundary.sourceIdsNe, boundary.sourceLeftSingleton]

theorem SplitBoundary.record_right_empty {state : State n} (boundary : SplitBoundary state) :
    (boundary.record boundary.sourceRight boundary.sourceRightBlock).elements = [] := by
  unfold SplitBoundary.record
  split_ifs <;> simp_all [boundary.sourceIdsNe.symm, boundary.sourceRightSingleton]

theorem SplitBoundary.roots_unassigned {params : Parameters} {state : State n}
    (boundary : SplitBoundary state) (valid : state.Valid params) :
    boundary.left ∉ boundary.final.allElements ∧ boundary.right ∉ boundary.final.allElements := by
  have absent : ∀ child sourceId sourceBlock,
      state.block? sourceId = some sourceBlock → child ∈ sourceBlock.elements →
      (boundary.record sourceId sourceBlock).elements = [] → child ∉ boundary.final.allElements := by
    intro child sourceId sourceBlock found present empty member
    obtain ⟨afterBlock, afterMem, afterPresent⟩ := List.mem_flatMap.mp member
    obtain ⟨afterId, afterEq⟩ := List.mem_iff_get.mp afterMem
    let oldId : Fin state.blocks.length := ⟨afterId.val, by simpa using afterId.isLt⟩
    have oldFound : state.block? oldId.val = some (state.blocks.get oldId) := by simp [State.block?, List.get_eq_getElem]
    have afterFound : boundary.final.block? oldId.val = some afterBlock := by
      simpa only [State.block?, oldId, List.getElem?_eq_getElem afterId.isLt, List.get_eq_getElem] using congrArg some afterEq
    have recordEq : boundary.record oldId.val (state.blocks.get oldId) = afterBlock :=
      Option.some.inj ((boundary.final_lookup oldId.val _ oldFound).symm.trans afterFound)
    have oldPresent : child ∈ (state.blocks.get oldId).elements :=
      (boundary.record_elements oldId.val _).subset (recordEq.symm ▸ afterPresent)
    have sameId := valid.blockId_eq_of_element_mem oldFound oldPresent found present
    have blockEq : state.blocks.get oldId = sourceBlock := Option.some.inj (oldFound.symm.trans (sameId ▸ found))
    rw [← recordEq, sameId, blockEq, empty] at afterPresent
    exact List.not_mem_nil afterPresent
  exact ⟨absent _ _ _ boundary.sourceLeftFound (by simp [boundary.sourceLeftSingleton]) boundary.record_left_empty,
    absent _ _ _ boundary.sourceRightFound (by simp [boundary.sourceRightSingleton]) boundary.record_right_empty⟩

end MultiSplay.InterfaceForest
