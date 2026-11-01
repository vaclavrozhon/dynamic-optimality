import VirtualNumericInsertion

/-! Actual conversion and capacity-restoration wrapper. Freezing one old
prefix and recreating its empty growing replacement adds one persistent
object. An intervening birth program may reuse the freed slot arbitrarily
many times provided its endpoint growing counts are unchanged. -/

namespace Splay.Research.VirtualGrowingSlot

open Splay.Interface Splay.Research.VirtualInterfaceAdmin

def convertState {n : ℕ} (before : State n) (id : ℕ) : State n :=
  ⟨before.blocks.modify id (fun block => { block with mode := .shrinking }), before.value⟩

theorem mode_modify_allElements {n : ℕ} (blocks : List (Block n)) (id : ℕ) :
    ((blocks.modify id fun block => { block with mode := .shrinking }).flatMap Block.elements) =
      blocks.flatMap Block.elements := by
  induction blocks generalizing id with
  | nil => simp
  | cons block blocks ih =>
      cases id with
      | zero => simp
      | succ id => simpa using congrArg (block.elements ++ ·) (ih id)

theorem convert_count_balance {n : ℕ} (blocks : List (Block n)) (id : ℕ)
    (source : Block n) (found : blocks[id]? = some source)
    (growing : source.mode = .growing) (creator : Element n) :
    ((blocks.modify id fun block => { block with mode := .shrinking }).filter
      (fun block => decide (block.mode = .growing ∧ block.creator = creator))).length +
      (if source.creator = creator then 1 else 0) =
    (blocks.filter (fun block => decide (block.mode = .growing ∧ block.creator = creator))).length := by
  induction blocks generalizing id with
  | nil => simp at found
  | cons block blocks ih =>
      cases id with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst block
          by_cases same : source.creator = creator <;> simp [growing, same]
      | succ id =>
          simp only [List.getElem?_cons_succ] at found
          have tail := ih id found
          by_cases selected : block.mode = .growing ∧ block.creator = creator <;>
            simp [selected] at tail ⊢ <;> omega

theorem convert_valid {n : ℕ} {params : Parameters} (before : State n)
    (id : ℕ) (source : Block n) (valid : before.Valid params)
    (found : before.blocks[id]? = some source) (growing : source.mode = .growing) :
    (convertState before id).Valid params := by
  refine ⟨?_, valid.2.1, ?_⟩
  · simpa only [convertState, State.allElements, mode_modify_allElements] using valid.1
  · intro creator
    have balance : (convertState before id).growingCount creator +
        (if source.creator = creator then 1 else 0) = before.growingCount creator :=
      convert_count_balance before.blocks id source found growing creator
    have oldBound := valid.2.2 creator
    omega

theorem convert_step {n : ℕ} {params : Parameters} (before : State n)
    (id : ℕ) (source : Block n) (valid : before.Valid params)
    (found : before.blocks[id]? = some source) (growing : source.mode = .growing) :
    Step params before (.convert id) (convertState before id) :=
  ⟨valid, .convert found growing rfl rfl, convert_valid before id source valid found growing⟩

theorem convert_room {n : ℕ} {params : Parameters} (before : State n)
    (id : ℕ) (source : Block n) (valid : before.Valid params)
    (found : before.blocks[id]? = some source) (growing : source.mode = .growing) :
    (convertState before id).growingCount source.creator < params.growingLimit := by
  have balance : (convertState before id).growingCount source.creator + 1 =
      before.growingCount source.creator := by
    simpa only [convertState, State.growingCount, eq_self_iff_true, ite_true] using
      convert_count_balance before.blocks id source found growing source.creator
  have oldBound := valid.2.2 source.creator
  omega

theorem growing_exists {n : ℕ} (state : State n) (creator : Element n)
    (positive : 0 < state.growingCount creator) :
    ∃ (id : ℕ) (source : Block n), state.blocks[id]? = some source ∧
      source.mode = .growing ∧ source.creator = creator := by
  obtain ⟨source, member, selected⟩ := List.length_filter_pos_iff.mp positive
  obtain ⟨id, found⟩ := List.mem_iff_getElem?.mp member
  exact ⟨id, source, found, by simpa using selected⟩

theorem trace_valid_after {n : ℕ} {params : Parameters} {before after : State n}
    {operations : List (Operation n)} (trace : Trace params before operations after) :
    after.Valid params := by
  induction trace with
  | nil valid => exact valid
  | cons step tail ih => exact ih

/-- One real frozen prefix supplies capacity for any completed birth
program. The final empty prefix is appended at the exact current length. -/
theorem freeze_run_restore {n : ℕ} {params : Parameters} (before middle : State n)
    (id : ℕ) (source : Block n) (operations : List (Operation n))
    (valid : before.Valid params) (found : before.blocks[id]? = some source)
    (growing : source.mode = .growing)
    (run : Trace params (convertState before id) operations middle)
    (counts : ∀ creator, middle.growingCount creator = (convertState before id).growingCount creator) :
    Trace params before (.convert id :: (operations ++ [.create source.creator]))
      (appendBlock middle (freshBlock source.creator .growing [])) := by
  have convert := convert_step before id source valid found growing
  have room : middle.growingCount source.creator < params.growingLimit := by
    rw [counts]
    exact convert_room before id source valid found growing
  have middleValid := trace_valid_after run
  have finalValid := append_growing_valid middle source.creator [] middleValid
    (by simpa using middleValid.1) room
  have create : Step params middle (.create source.creator)
      (appendBlock middle (freshBlock source.creator .growing [])) :=
    ⟨middleValid, .create room rfl rfl, finalValid⟩
  exact .cons convert (VirtualNumericInsertion.trace_append run (.cons create (.nil finalValid)))

theorem freeze_restore_counts {n : ℕ} (before middle : State n)
    (id : ℕ) (source : Block n) (found : before.blocks[id]? = some source)
    (growing : source.mode = .growing)
    (counts : ∀ creator, middle.growingCount creator = (convertState before id).growingCount creator)
    (creator : Element n) :
    (appendBlock middle (freshBlock source.creator .growing [])).growingCount creator =
      before.growingCount creator := by
  have balance : (convertState before id).growingCount creator +
      (if source.creator = creator then 1 else 0) = before.growingCount creator :=
    convert_count_balance before.blocks id source found growing creator
  have appended : (appendBlock middle (freshBlock source.creator .growing [])).growingCount creator =
      middle.growingCount creator + (if source.creator = creator then 1 else 0) := by
    by_cases same : source.creator = creator <;>
      simp [appendBlock, freshBlock, State.growingCount, same]
  rw [appended, counts]
  exact balance

theorem freeze_restore_growth {n : ℕ} (id : ℕ) (creator : Element n)
    (operations : List (Operation n)) :
    totalBlockGrowth (.convert id :: (operations ++ [.create creator])) =
      totalBlockGrowth operations+1 := by
  simp [totalBlockGrowth, Operation.blockGrowth]

theorem freeze_restore_increases {n : ℕ} (id : ℕ) (creator : Element n)
    (operations : List (Operation n)) :
    totalIncreases (.convert id :: (operations ++ [.create creator])) = totalIncreases operations := by
  simp [totalIncreases, Operation.increaseCount]

end Splay.Research.VirtualGrowingSlot

#print axioms Splay.Research.VirtualGrowingSlot.freeze_run_restore
#print axioms Splay.Research.VirtualGrowingSlot.freeze_restore_counts
