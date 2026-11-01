import MultiSplay.InterfaceRootOperations

/-!
# Retiring root singletons without resetting their child histories

The block identifiers below are arbitrary existing identifiers. This permits
arbitrary interleaved work since the corresponding join. Empty retired blocks
remain in the history with their old creators and pass counters.
-/

namespace MultiSplay.InterfaceForest

open Splay.Interface

variable {n : Nat}

def modifyBlock (state : State n) (id : BlockId) (f : Block n → Block n) : State n :=
  ⟨state.blocks.modify id f, state.value⟩

private theorem elements_modify_sublist (blocks : List (Block n)) (id : Nat) (f : Block n → Block n)
    (keeps : ∀ block, (f block).elements.Sublist block.elements) :
    ((blocks.modify id f).flatMap Block.elements).Sublist (blocks.flatMap Block.elements) := by
  induction blocks generalizing id with
  | nil => simp
  | cons block rest ih =>
      cases id with
      | zero => simpa using (keeps block).append_right (rest.flatMap Block.elements)
      | succ id => simpa using (ih id).append_left block.elements

private theorem filter_modify_length_le {α : Type*} (blocks : List α) (id : Nat)
    (f : α → α) (p : α → Bool) (keeps : ∀ block, p (f block) = true → p block = true) :
    ((blocks.modify id f).filter p).length ≤ (blocks.filter p).length := by
  induction blocks generalizing id with
  | nil => simp
  | cons block rest ih =>
      cases id with
      | zero =>
          by_cases before : p block = true
          · by_cases after : p (f block) = true <;> simp [before, after]
          · have after : ¬p (f block) = true := fun h => before (keeps block h)
            simp [before, after]
      | succ id =>
          have bound := ih id
          by_cases selected : p block = true <;> simpa [selected] using bound

theorem modifyBlock_valid {params : Parameters} (state : State n) (id : BlockId)
    (f : Block n → Block n) (valid : state.Valid params)
    (elementsKeep : ∀ block, (f block).elements.Sublist block.elements)
    (growingKeep : ∀ block creator,
      (f block).mode = .growing ∧ (f block).creator = creator →
      block.mode = .growing ∧ block.creator = creator) :
    (modifyBlock state id f).Valid params := by
  refine ⟨?_, valid.2.1, ?_⟩
  · exact valid.1.sublist (elements_modify_sublist state.blocks id f elementsKeep)
  · intro creator
    apply le_trans (filter_modify_length_le state.blocks id f
      (fun block => decide (block.mode = .growing ∧ block.creator = creator)) ?_) (valid.2.2 creator)
    intro block h
    simpa only [decide_eq_true_eq] using growingKeep block creator (of_decide_eq_true h)

def convert (state : State n) (id : BlockId) : State n :=
  modifyBlock state id (fun block => { block with mode := .shrinking })

def delete (state : State n) (id : BlockId) (element : Element n) : State n :=
  modifyBlock state id (fun block => { block with elements := block.elements.erase element })

theorem convert_step {params : Parameters} (state : State n) (id : BlockId) (block : Block n)
    (valid : state.Valid params) (found : state.block? id = some block) (growing : block.mode = .growing) :
    Step params state (.convert id) (convert state id) := by
  refine ⟨valid, .convert found growing rfl rfl, ?_⟩
  apply modifyBlock_valid state id (fun block => { block with mode := .shrinking })
    valid (fun _ => List.Sublist.refl _) ?_
  intro block creator h
  cases h.1

theorem delete_step {params : Parameters} (state : State n) (id : BlockId) (block : Block n)
    (element : Element n) (valid : state.Valid params) (found : state.block? id = some block)
    (shrinking : block.mode = .shrinking) (present : element ∈ block.elements) :
    Step params state (.delete id element) (delete state id element) := by
  refine ⟨valid, .delete found shrinking present rfl rfl, ?_⟩
  apply modifyBlock_valid state id _ valid (fun block => List.erase_sublist) ?_
  intro block creator h
  exact h

/-- A growing root singleton is converted, deleted, and then its child is
lowered from value two to one by a genuine paid `ValueChange`. -/
def detachGrowing (state : State n) (id : BlockId) (child : Element n) : State n :=
  setValue (delete (convert state id) id child) child 1

def detachGrowingWord (id : BlockId) (child : Element n) : List (Operation n) :=
  [.convert id, .delete id child, .valueChange child .decrease]

theorem detachGrowing_trace {params : Parameters} (state : State n) (id : BlockId)
    (block : Block n) (child : Element n) (valid : state.Valid params)
    (found : state.block? id = some block) (growing : block.mode = .growing)
    (singleton : block.elements = [child]) (childTwo : state.value child = 2) :
    Trace params state (detachGrowingWord id child) (detachGrowing state id child) := by
  have first := convert_step state id block valid found growing
  have newFound : (convert state id).block? id = some { block with mode := .shrinking } := by
    simp [convert, modifyBlock, State.block?, show state.blocks[id]? = some block from found]
  have second := delete_step (convert state id) id { block with mode := .shrinking }
    child first.2.2 newFound rfl (by simp [singleton])
  have valueEq : (delete (convert state id) id child).value child = 2 := childTwo
  have third : Step params (delete (convert state id) id child) (.valueChange child .decrease)
      (detachGrowing state id child) := by
    simpa only [detachGrowing, valueEq, Nat.reduceSub] using
      decrease_step (delete (convert state id) id child) child second.2.2 (by omega)
  exact .cons first (.cons second (.cons third (.nil third.2.2)))

/-- Deleting a previously converted singleton preserves its current value and
does not recreate, renumber, or otherwise alter any child record. -/
theorem detachShrinking_trace {params : Parameters} (state : State n) (id : BlockId)
    (block : Block n) (child : Element n) (valid : state.Valid params)
    (found : state.block? id = some block) (shrinking : block.mode = .shrinking)
    (singleton : block.elements = [child]) :
    Trace params state [.delete id child] (delete state id child) := by
  have step := delete_step state id block child valid found shrinking (by simp [singleton])
  exact .cons step (.nil step.2.2)

@[simp] theorem detachGrowingWord_inserts (id : BlockId) (child : Element n) :
    totalInserts (detachGrowingWord id child) = 0 := rfl

@[simp] theorem detachGrowingWord_increases (id : BlockId) (child : Element n) :
    totalIncreases (detachGrowingWord id child) = 0 := rfl

@[simp] theorem detachGrowingWord_activity (id : BlockId) (child : Element n) :
    totalActivity (detachGrowingWord id child) = 0 := rfl

theorem detachGrowing_old_block (state : State n) (id : BlockId) (child : Element n)
    (other : BlockId) (different : other ≠ id) :
    (detachGrowing state id child).block? other = state.block? other := by
  simp [detachGrowing, setValue, delete, convert, modifyBlock, State.block?,
    List.getElem?_modify, different, Ne.symm different]

end MultiSplay.InterfaceForest
