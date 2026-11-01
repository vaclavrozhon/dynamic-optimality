import Splay.Interface.Decay

namespace Splay.Interface

private theorem map_modify_preserved {α β : Type*} (f : α → β) (blocks : List α)
    (index : ℕ) (update : α → α)
    (preserves : ∀ block, blocks[index]? = some block → f (update block) = f block) :
    (blocks.modify index update).map f = blocks.map f := by
  induction blocks generalizing index with
  | nil => simp
  | cons head tail ih =>
      cases index with
      | zero => simp [preserves head (by simp)]
      | succ index =>
          change f head :: (tail.modify index update).map f = f head :: tail.map f
          congr 1
          apply ih
          intro block found
          exact preserves block (by simpa using found)

private theorem insertAtDestinations_creators {n : ℕ} (blocks : List (Block n))
    (matching : List (Pairing n)) :
    (insertAtDestinations blocks matching).map Block.creator = blocks.map Block.creator := by
  induction matching generalizing blocks with
  | nil => rfl
  | cons pairing matching ih =>
      change (insertAtDestinations (blocks.modify pairing.destination
        fun block => { block with elements := pairing.loser :: block.elements }) matching).map Block.creator = _
      rw [ih]
      exact map_modify_preserved _ _ _ _ (by intros; rfl)

/-- Persistent IDs never change their creator; creation and splitting only
append fresh creator entries. -/
theorem Effect.creators_append {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    (effect : Effect params before operation after) :
    ∃ extra, after.blocks.map Block.creator = before.blocks.map Block.creator ++ extra := by
  cases effect with
  | convert found growing blocksEq valuesEq =>
      refine ⟨[], ?_⟩
      rw [blocksEq, List.append_nil]
      exact map_modify_preserved _ _ _ _ (by intros; rfl)
  | @create after creator room blocksEq valuesEq =>
      refine ⟨[creator], ?_⟩
      simp [blocksEq]
  | insert found growing unassigned order blocksEq valuesEq =>
      refine ⟨[], ?_⟩
      rw [blocksEq, List.append_nil]
      exact map_modify_preserved _ _ _ _ (by intros; rfl)
  | delete found shrinking member blocksEq valuesEq =>
      refine ⟨[], ?_⟩
      rw [blocksEq, List.append_nil]
      exact map_modify_preserved _ _ _ _ (by intros; rfl)
  | @pass after sourceId source matching found matchingValid blocksEq valuesEq =>
      refine ⟨[], ?_⟩
      rw [blocksEq, List.append_nil, passBlocks, insertAtDestinations_creators]
      apply map_modify_preserved
      intro block selected
      have equal : source = block := Option.some.inj (found.symm.trans selected)
      change source.creator = block.creator
      exact congrArg Block.creator equal
  | @split after sourceId source count found shrinking countLe blocksEq valuesEq =>
      refine ⟨[source.creator, source.creator], ?_⟩
      rw [blocksEq, splitBlocks, List.map_append]
      congr 1
      exact map_modify_preserved _ _ _ _ (by intros; rfl)
  | decrease canDecrease blocksEq valuesEq => exact ⟨[], by simp [blocksEq]⟩
  | increase canIncrease blocksEq valuesEq => exact ⟨[], by simp [blocksEq]⟩

/-- The same old ID still exists after every operation and retains its creator. -/
theorem Effect.creatorFound {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    (effect : Effect params before operation after)
    {id : BlockId} {block : Block n} (found : before.block? id = some block) :
    ∃ current : Block n, after.block? id = some current ∧ current.creator = block.creator := by
  obtain ⟨extra, creators⟩ := effect.creators_append
  have bounded : id < before.blocks.length := (List.getElem?_eq_some_iff.mp found).1
  have lookup : (after.blocks.map Block.creator)[id]? = some block.creator := by
    rw [creators, List.getElem?_append_left (by simpa using bounded), List.getElem?_map]
    change Option.map Block.creator (before.block? id) = _
    rw [found]
    rfl
  rw [List.getElem?_map] at lookup
  exact Option.map_eq_some_iff.mp lookup

end Splay.Interface
