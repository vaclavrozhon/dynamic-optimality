import MultiSplay.InterfaceEmbedding

/-!
# Local proxies for retired creator identities

A shrinking block never uses its creator in an operation precondition. Its
creator can therefore be represented by a local proxy while the actual global
history keeps the immutable original identity. `Equivalent` retains element
order, pass counts, modes, values, and every growing creator. The transport
theorem constructs an exact legal history from the original state; it does not
add an operation that changes a creator.
-/

namespace MultiSplay.InterfaceHistory

open Splay.Interface

variable {n : Nat}

def observable (block : Block n) : Block n :=
  { block with creator := if block.mode = .growing then block.creator else 0 }

def Equivalent (a b : State n) : Prop :=
  a.blocks.map observable = b.blocks.map observable ∧ a.value = b.value

theorem observable_eq {a b : Block n} : observable a = observable b ↔
    a.passCount = b.passCount ∧ a.mode = b.mode ∧ a.elements = b.elements ∧
      (a.mode = .growing → a.creator = b.creator) := by
  rcases a with ⟨ac, ap, am, ae⟩
  rcases b with ⟨bc, bp, bm, be⟩
  cases am <;> cases bm <;> simp [observable, Block.mk.injEq] <;> tauto

theorem Equivalent.symm {a b : State n} (same : Equivalent a b) : Equivalent b a := ⟨same.1.symm, same.2.symm⟩

theorem Equivalent.allElements {a b : State n} (same : Equivalent a b) : a.allElements = b.allElements := by
  have eq := congrArg (fun blocks : List (Block n) => blocks.flatMap Block.elements) same.1
  simpa [List.flatMap_map, observable, State.allElements] using eq

theorem growing_observable (blocks : List (Block n)) (creator : Element n) :
    ((blocks.map observable).filter (fun block => decide (block.mode = .growing ∧ block.creator = creator))).length =
      (blocks.filter (fun block => decide (block.mode = .growing ∧ block.creator = creator))).length := by
  induction blocks with
  | nil => rfl
  | cons head tail ih =>
      cases modeEq : head.mode <;> by_cases sameCreator : head.creator = creator <;>
        simp_all [observable, List.filter_cons]

theorem Equivalent.growingCount {a b : State n} (same : Equivalent a b) (creator : Element n) :
    a.growingCount creator = b.growingCount creator := by
  unfold State.growingCount
  rw [← growing_observable a.blocks creator, same.1, growing_observable]

theorem Equivalent.valid {a b : State n} (same : Equivalent a b) {params : Parameters}
    (valid : a.Valid params) : b.Valid params := by
  refine ⟨same.allElements ▸ valid.1, ?_, ?_⟩
  · simpa only [same.2] using valid.2.1
  · intro creator
    rw [← same.growingCount]
    exact valid.2.2 creator

theorem Equivalent.lookup {a b : State n} (same : Equivalent a b) {id : BlockId} {block : Block n}
    (found : a.block? id = some block) :
    ∃ other, b.block? id = some other ∧ observable block = observable other := by
  have eq := congrArg (fun blocks : List (Block n) => blocks[id]?) same.1
  simp only [List.getElem?_map] at eq
  change (a.block? id).map observable = (b.block? id).map observable at eq
  rw [found, Option.map_some] at eq
  obtain ⟨other, lookup, obsEq⟩ := Option.map_eq_some_iff.mp eq.symm
  exact ⟨other, lookup, obsEq.symm⟩

private theorem map_modify {α β : Type*} (map : α → β) (update : α → α) (newUpdate : β → β)
    (commutes : ∀ x, map (update x) = newUpdate (map x)) (values : List α) (id : Nat) :
    (values.modify id update).map map = (values.map map).modify id newUpdate := by
  induction values generalizing id with
  | nil => cases id <;> rfl
  | cons head tail ih => cases id <;> simp [commutes, ih]

theorem observable_elements (block : Block n) (elements : List (Element n)) :
    observable {block with elements := elements} = {observable block with elements := elements} := rfl

theorem observable_convert (block : Block n) :
    observable {block with mode := .shrinking} = observable {observable block with mode := .shrinking} := by
  simp [observable]

theorem convert_blocks (blocks : List (Block n)) (id : Nat) :
    (blocks.modify id (fun block => {block with mode := .shrinking})).map observable =
      (blocks.map observable).modify id (fun block => observable {block with mode := .shrinking}) :=
  map_modify observable _ _ observable_convert blocks id

theorem elements_blocks (blocks : List (Block n)) (id : Nat) (update : List (Element n) → List (Element n)) :
    (blocks.modify id (fun block => {block with elements := update block.elements})).map observable =
      (blocks.map observable).modify id (fun block => {block with elements := update block.elements}) :=
  map_modify observable (fun block => {block with elements := update block.elements})
    (fun block => {block with elements := update block.elements}) (fun _ => rfl) blocks id

theorem destinations_blocks (blocks : List (Block n)) (pairs : List (Pairing n)) :
    (insertAtDestinations blocks pairs).map observable = insertAtDestinations (blocks.map observable) pairs := by
  induction pairs generalizing blocks with
  | nil => rfl
  | cons head tail ih =>
      simp only [insertAtDestinations, List.foldl_cons]
      simp only [insertAtDestinations] at ih
      rw [ih, elements_blocks]

theorem pass_blocks (blocks : List (Block n)) (id : Nat) (source : Block n) (pairs : List (Pairing n)) :
    (passBlocks blocks id source pairs).map observable = passBlocks (blocks.map observable) id (observable source) pairs := by
  unfold passBlocks
  rw [destinations_blocks, map_modify observable
    (fun _ => {source with passCount := source.passCount + 1, elements := removeLosers source.elements pairs})
    (fun _ => {observable source with passCount := source.passCount + 1, elements := removeLosers source.elements pairs})
    (fun _ => rfl)]
  rfl

theorem split_blocks (blocks : List (Block n)) (id : Nat) (source : Block n) (count : Nat) :
    (splitBlocks blocks id source count).map observable = splitBlocks (blocks.map observable) id (observable source) count := by
  unfold splitBlocks
  rw [List.map_append, elements_blocks blocks id (fun _ => [])]
  rfl

theorem pairing_valid {a b : State n} (same : Equivalent a b) {id : BlockId} {source other : Block n}
    (sourceEq : observable source = observable other) {pair : Pairing n}
    (valid : PairingValid a id source pair) : PairingValid b id other pair := by
  have fields := observable_eq.mp sourceEq
  obtain ⟨adjacent, order, different, destination, lookup, growing, creator⟩ := valid
  obtain ⟨target, found, targetEq⟩ := same.lookup lookup
  have targetFields := observable_eq.mp targetEq
  exact ⟨fields.2.2.1 ▸ adjacent, same.2 ▸ order, different, target, found,
    targetFields.2.1 ▸ growing, (targetFields.2.2.2 growing).symm.trans creator⟩

theorem matching_valid {a b : State n} (same : Equivalent a b) {params : Parameters} {id : BlockId}
    {source other : Block n} (sourceEq : observable source = observable other) {pairs : List (Pairing n)}
    (valid : MatchingValid params a id source pairs) : MatchingValid params b id other pairs := by
  have fields := observable_eq.mp sourceEq
  exact ⟨fields.2.1 ▸ valid.1, valid.2.1, valid.2.2.1,
    fun pair member => pairing_valid same sourceEq (valid.2.2.2.1 pair member), by
      simpa only [← fields.1, ← fields.2.2.1] using valid.2.2.2.2⟩

/-- One actual operation, with the same stable block IDs, can be performed
from any equivalent historical state. Its immutable creators remain intact. -/
theorem effect {params : Parameters} {a a' b : State n} {op : Operation n}
    (same : Equivalent a b) (execution : Effect params a op a') :
    ∃ b', Effect params b op b' ∧ Equivalent a' b' := by
  cases execution with
  | convert found growing blocksEq valuesEq =>
      obtain ⟨other, lookup, obsEq⟩ := same.lookup found
      have fields := observable_eq.mp obsEq
      refine ⟨⟨b.blocks.modify _ (fun block => {block with mode := .shrinking}), b.value⟩,
        .convert lookup (fields.2.1 ▸ growing) rfl rfl, ?_, valuesEq.trans same.2⟩
      simp only [blocksEq, convert_blocks, same.1]
  | create room blocksEq valuesEq =>
      refine ⟨⟨b.blocks ++ [⟨_, 0, .growing, []⟩], b.value⟩,
        .create (by simpa only [← same.growingCount] using room) rfl rfl, ?_, valuesEq.trans same.2⟩
      simp only [blocksEq, List.map_append, same.1]
  | insert found growing unassigned ordered blocksEq valuesEq =>
      obtain ⟨other, lookup, obsEq⟩ := same.lookup found
      have fields := observable_eq.mp obsEq
      refine ⟨⟨b.blocks.modify _ (fun block => {block with elements := _ :: block.elements}), b.value⟩,
        .insert lookup (fields.2.1 ▸ growing) (same.allElements ▸ unassigned)
          (by simpa only [← same.2, ← fields.2.2.2 growing] using ordered) rfl rfl, ?_, valuesEq.trans same.2⟩
      simp only [blocksEq, elements_blocks, same.1]
  | delete found shrinking present blocksEq valuesEq =>
      rename_i id source element
      obtain ⟨other, lookup, obsEq⟩ := same.lookup found
      have fields := observable_eq.mp obsEq
      refine ⟨⟨b.blocks.modify _ (fun block => {block with elements := block.elements.erase _}), b.value⟩,
        .delete lookup (fields.2.1 ▸ shrinking) (fields.2.2.1 ▸ present) rfl rfl, ?_, valuesEq.trans same.2⟩
      simp only [blocksEq, elements_blocks a.blocks id (fun elements => elements.erase element),
        elements_blocks b.blocks id (fun elements => elements.erase element), same.1]
  | pass found matching blocksEq valuesEq =>
      obtain ⟨other, lookup, obsEq⟩ := same.lookup found
      refine ⟨⟨passBlocks b.blocks _ other _, b.value⟩,
        .pass lookup (matching_valid same obsEq matching) rfl rfl, ?_, valuesEq.trans same.2⟩
      simp only [blocksEq, pass_blocks, same.1, obsEq]
  | split found shrinking prefixLe blocksEq valuesEq =>
      obtain ⟨other, lookup, obsEq⟩ := same.lookup found
      have fields := observable_eq.mp obsEq
      refine ⟨⟨splitBlocks b.blocks _ other _, b.value⟩,
        .split lookup (fields.2.1 ▸ shrinking) (by simpa only [← fields.2.2.1] using prefixLe) rfl rfl,
        ?_, valuesEq.trans same.2⟩
      simp only [blocksEq, split_blocks, same.1, obsEq]
  | decrease allowed blocksEq valuesEq =>
      refine ⟨⟨b.blocks, Function.update b.value _ (b.value _ - 1)⟩,
        .decrease (same.2 ▸ allowed) rfl rfl, blocksEq ▸ same.1, ?_⟩
      simp only [valuesEq, same.2]
  | increase allowed blocksEq valuesEq =>
      refine ⟨⟨b.blocks, Function.update b.value _ (b.value _ + 1)⟩,
        .increase (same.2 ▸ allowed) rfl rfl, blocksEq ▸ same.1, ?_⟩
      simp only [valuesEq, same.2]

theorem step {params : Parameters} {a a' b : State n} {op : Operation n}
    (same : Equivalent a b) (execution : Step params a op a') :
    ∃ b', Step params b op b' ∧ Equivalent a' b' := by
  obtain ⟨b', effect, after⟩ := effect same execution.2.1
  exact ⟨b', ⟨same.valid execution.1, effect, after.valid execution.2.2⟩, after⟩

/-- Transport the complete operation word; hence every activity, insertion,
and value-change charge is identical, and every pass count survives. -/
theorem trace {params : Parameters} {a a' b : State n} {operations : List (Operation n)}
    (same : Equivalent a b) (execution : Trace params a operations a') :
    ∃ b', Trace params b operations b' ∧ Equivalent a' b' := by
  induction execution generalizing b with
  | nil valid => exact ⟨b, .nil (same.valid valid), same⟩
  | cons head tail ih =>
      obtain ⟨middle, first, middleEq⟩ := step same head
      obtain ⟨final, rest, finalEq⟩ := ih middleEq
      exact ⟨final, .cons first rest, finalEq⟩

end MultiSplay.InterfaceHistory
