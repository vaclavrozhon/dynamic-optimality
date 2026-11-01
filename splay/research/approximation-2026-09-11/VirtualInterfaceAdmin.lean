import Splay.Interface.ConversionAccounting
import Splay.Interface.BlockCount

/-! Constructive abstract-interface Split and fresh singleton traces.
These retain the exact appended object identities. Insert's numeric order
is an explicit premise, to be discharged by the numerical realization. -/

namespace Splay.Research.VirtualInterfaceAdmin

open Splay.Interface

theorem modify_append_singleton {α : Type*} (items : List α) (last : α) (update : α → α) :
    (items ++ [last]).modify items.length update = items ++ [update last] := by
  induction items with
  | nil => simp
  | cons head items ih => simpa using congrArg (head :: ·) ih

theorem emptied_flatMap_append_perm {n : ℕ} (blocks : List (Block n))
    (id : BlockId) (source : Block n) (found : blocks[id]? = some source) :
    ((blocks.modify id fun block => { block with elements := [] }).flatMap Block.elements ++
      source.elements).Perm (blocks.flatMap Block.elements) := by
  induction blocks generalizing id with
  | nil => simp at found
  | cons head blocks ih =>
      cases id with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst head
          simpa using (List.perm_append_comm :
            (blocks.flatMap Block.elements ++ source.elements).Perm
              (source.elements ++ blocks.flatMap Block.elements))
      | succ id =>
          simp only [List.getElem?_cons_succ] at found
          simpa only [List.modify_succ_cons, List.flatMap_cons, List.append_assoc] using
            (ih id found).append_left head.elements

theorem split_allElements_perm {n : ℕ} (blocks : List (Block n))
    (id : BlockId) (source : Block n) (cut : ℕ) (found : blocks[id]? = some source) :
    ((splitBlocks blocks id source cut).flatMap Block.elements).Perm
      (blocks.flatMap Block.elements) := by
  simpa [splitBlocks, List.flatMap_append, List.take_append_drop, List.append_assoc] using
    emptied_flatMap_append_perm blocks id source found

theorem growingCount_modify_elements {n : ℕ} (blocks : List (Block n))
    (id : BlockId) (elements : List (Element n)) (creator : Element n) :
    ((blocks.modify id fun block => { block with elements := elements }).filter
      (fun block => decide (block.mode = .growing ∧ block.creator = creator))).length =
    (blocks.filter (fun block => decide (block.mode = .growing ∧ block.creator = creator))).length := by
  induction blocks generalizing id with
  | nil => simp
  | cons head blocks ih =>
      cases id with
      | zero =>
          simp only [List.modify_zero_cons, List.filter_cons]
          split <;> rfl
      | succ id =>
          simp only [List.modify_succ_cons, List.filter_cons]
          split <;> simp_all

def splitState {n : ℕ} (before : State n) (id : BlockId) (source : Block n) (cut : ℕ) : State n :=
  ⟨splitBlocks before.blocks id source cut, before.value⟩

theorem splitState_growingCount_eq {n : ℕ} (before : State n)
    (id : BlockId) (source : Block n) (cut : ℕ)
    (shrinking : source.mode = .shrinking) (creator : Element n) :
    (splitState before id source cut).growingCount creator = before.growingCount creator := by
  simpa [splitState, State.growingCount, splitBlocks, shrinking] using
    growingCount_modify_elements before.blocks id [] creator

theorem splitState_valid {n : ℕ} {params : Parameters} (before : State n)
    (id : BlockId) (source : Block n) (cut : ℕ)
    (valid : before.Valid params) (found : before.blocks[id]? = some source)
    (shrinking : source.mode = .shrinking) :
    (splitState before id source cut).Valid params := by
  refine ⟨?_, valid.2.1, ?_⟩
  · exact (split_allElements_perm before.blocks id source cut found).nodup_iff.mpr valid.1
  · intro creator
    have counts := growingCount_modify_elements before.blocks id [] creator
    simpa [splitState, State.growingCount, splitBlocks, shrinking] using
      counts.le.trans (valid.2.2 creator)

theorem splitState_step {n : ℕ} {params : Parameters} (before : State n)
    (id : BlockId) (source : Block n) (cut : ℕ)
    (valid : before.Valid params) (found : before.blocks[id]? = some source)
    (shrinking : source.mode = .shrinking) (cutLe : cut ≤ source.elements.length) :
    Step params before (.split id cut) (splitState before id source cut) :=
  ⟨valid, .split found shrinking cutLe rfl rfl,
    splitState_valid before id source cut valid found shrinking⟩

def freshBlock {n : ℕ} (creator : Element n) (mode : Mode) (elements : List (Element n)) : Block n :=
  ⟨creator, 0, mode, elements⟩

def appendBlock {n : ℕ} (before : State n) (block : Block n) : State n :=
  ⟨before.blocks ++ [block], before.value⟩

theorem append_growing_valid {n : ℕ} {params : Parameters} (before : State n)
    (creator : Element n) (elements : List (Element n))
    (valid : before.Valid params) (assigned : (before.allElements ++ elements).Nodup)
    (room : before.growingCount creator < params.growingLimit) :
    (appendBlock before (freshBlock creator .growing elements)).Valid params := by
  refine ⟨?_, valid.2.1, ?_⟩
  · simpa [appendBlock, freshBlock, State.allElements] using assigned
  · intro queried
    by_cases same : creator = queried
    · subst queried
      simpa [appendBlock, freshBlock, State.growingCount] using room
    · simpa [appendBlock, freshBlock, State.growingCount, same] using valid.2.2 queried

theorem append_shrinking_valid {n : ℕ} {params : Parameters} (before : State n)
    (creator : Element n) (elements : List (Element n))
    (valid : before.Valid params) (assigned : (before.allElements ++ elements).Nodup) :
    (appendBlock before (freshBlock creator .shrinking elements)).Valid params := by
  refine ⟨?_, valid.2.1, ?_⟩
  · simpa [appendBlock, freshBlock, State.allElements] using assigned
  · intro queried
    simpa [appendBlock, freshBlock, State.growingCount] using valid.2.2 queried

/-- Create, insert, and immediately convert one fresh singleton at exactly
the old storage length. No existing object ID or payload is replaced. -/
theorem append_singleton_trace {n : ℕ} {params : Parameters} (before : State n)
    (creator element : Element n) (valid : before.Valid params)
    (fresh : element ∉ before.allElements)
    (room : before.growingCount creator < params.growingLimit)
    (order : before.value creator+1 ≤ before.value element) :
    Trace params before
      [.create creator, .insert before.blocks.length element, .convert before.blocks.length]
      (appendBlock before (freshBlock creator .shrinking [element])) := by
  let empty := appendBlock before (freshBlock creator .growing [])
  let inserted := appendBlock before (freshBlock creator .growing [element])
  let final := appendBlock before (freshBlock creator .shrinking [element])
  have emptyValid := append_growing_valid before creator [] valid (by simpa using valid.1) room
  have singletonAssigned : (before.allElements ++ [element]).Nodup := by
    refine List.nodup_append.mpr ⟨valid.1, by simp, ?_⟩
    intro other member selected singleton equal
    have selectedEq : selected = element := by simpa using singleton
    exact fresh ((equal.trans selectedEq) ▸ member)
  have insertedValid := append_growing_valid before creator [element] valid singletonAssigned room
  have finalValid := append_shrinking_valid before creator [element] valid singletonAssigned
  have emptyFound : empty.blocks[before.blocks.length]? = some (freshBlock creator .growing []) := by
    simp [empty, appendBlock]
  have insertedFound : inserted.blocks[before.blocks.length]? = some (freshBlock creator .growing [element]) := by
    simp [inserted, appendBlock]
  have createStep : Step params before (.create creator) empty :=
    ⟨valid, .create room rfl rfl, emptyValid⟩
  have insertStep : Step params empty (.insert before.blocks.length element) inserted := by
    refine ⟨emptyValid, .insert emptyFound rfl ?_ order ?_ rfl, insertedValid⟩
    · simpa [empty, appendBlock, freshBlock, State.allElements] using fresh
    · simpa [empty, inserted, appendBlock, freshBlock] using
        (modify_append_singleton before.blocks (freshBlock creator .growing [])
          (fun block => { block with elements := element :: block.elements })).symm
  have convertStep : Step params inserted (.convert before.blocks.length) final := by
    refine ⟨insertedValid, .convert insertedFound rfl ?_ rfl, finalValid⟩
    simpa [inserted, final, appendBlock, freshBlock] using
      (modify_append_singleton before.blocks (freshBlock creator .growing [element])
        (fun block => { block with mode := .shrinking })).symm
  exact .cons createStep (.cons insertStep (.cons convertStep (.nil finalValid)))

end Splay.Research.VirtualInterfaceAdmin

#print axioms Splay.Research.VirtualInterfaceAdmin.splitState_step
#print axioms Splay.Research.VirtualInterfaceAdmin.append_singleton_trace
