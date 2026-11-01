import Splay.Interface.Decay
import Mathlib.Tactic

namespace Splay.Interface

/-- An element's current residence is in a shrinking block. Splits may
change its ID, but cannot turn that residence back into a growing one. -/
def State.HasShrinkingElement {n : ℕ} (state : State n) (element : Element n) : Prop :=
  ∃ block ∈ state.blocks, block.mode = .shrinking ∧ element ∈ block.elements

/-- This operation does not end the element's current block residence. -/
def Operation.Retains {n : ℕ} (operation : Operation n) (element : Element n) : Prop :=
  match operation with
  | .delete _ deleted => element ≠ deleted
  | .pass _ matching => element ∉ pairingLosers matching
  | _ => True

private theorem exists_mem_modify_preserved {α : Type*} {blocks : List α}
    {P : α → Prop} (present : ∃ block ∈ blocks, P block)
    (index : ℕ) (update : α → α)
    (preserves : ∀ block, blocks[index]? = some block → P block → P (update block)) :
    ∃ block ∈ blocks.modify index update, P block := by
  induction blocks generalizing index with
  | nil => simpa using present
  | cons head tail ih =>
      obtain ⟨block, member, property⟩ := present
      cases index with
      | zero =>
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨update block, by simp, preserves block (by simp) property⟩
          · exact ⟨block, by simp [member], property⟩
      | succ index =>
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨block, by simp, property⟩
          · obtain ⟨updated, updatedMember, updatedProperty⟩ := ih ⟨block, member, property⟩ index
              (by intro block found property; exact preserves block (by simpa using found) property)
            exact ⟨updated, by simp [updatedMember], updatedProperty⟩

private theorem shrinking_insertAtDestinations {n : ℕ} {blocks : List (Block n)}
    {element : Element n}
    (present : ∃ block ∈ blocks, block.mode = .shrinking ∧ element ∈ block.elements)
    (matching : List (Pairing n)) :
    ∃ block ∈ insertAtDestinations blocks matching,
      block.mode = .shrinking ∧ element ∈ block.elements := by
  induction matching generalizing blocks with
  | nil => exact present
  | cons pairing matching ih =>
      apply ih
      apply exists_mem_modify_preserved present
      intro block found property
      exact ⟨property.1, List.mem_cons_of_mem _ property.2⟩

private theorem mem_removeLosers_of_retained {n : ℕ} {elements : List (Element n)}
    {element : Element n} {matching : List (Pairing n)}
    (member : element ∈ elements) (retained : element ∉ pairingLosers matching) :
    element ∈ removeLosers elements matching := by
  induction matching generalizing elements with
  | nil => exact member
  | cons pairing matching ih =>
      have different : element ≠ pairing.loser := by
        intro equal
        apply retained
        exact List.mem_map.mpr ⟨pairing, by simp, equal.symm⟩
      apply ih ((List.mem_erase_of_ne different).mpr member)
      intro inside
      apply retained
      exact List.mem_cons_of_mem _ inside

/-- An actual interface effect preserves shrinking residence unless the
operation deletes this element or passes it as a loser. -/
theorem Effect.hasShrinkingElement_of_retains {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n} {element : Element n}
    (effect : Effect params before operation after)
    (present : before.HasShrinkingElement element) (retains : operation.Retains element) :
    after.HasShrinkingElement element := by
  cases effect with
  | convert found growing blocksEq valuesEq =>
      rw [State.HasShrinkingElement, blocksEq]
      apply exists_mem_modify_preserved present
      intro block found property
      exact ⟨rfl, property.2⟩
  | create room blocksEq valuesEq =>
      obtain ⟨block, member, property⟩ := present
      exact ⟨block, by rw [blocksEq]; exact List.mem_append_left _ member, property⟩
  | insert found growing unassigned valueOrder blocksEq valuesEq =>
      rw [State.HasShrinkingElement, blocksEq]
      apply exists_mem_modify_preserved present
      intro block found property
      exact ⟨property.1, List.mem_cons_of_mem _ property.2⟩
  | delete found shrinking member blocksEq valuesEq =>
      rw [State.HasShrinkingElement, blocksEq]
      apply exists_mem_modify_preserved present
      intro block found property
      exact ⟨property.1, (List.mem_erase_of_ne retains).mpr property.2⟩
  | @pass after sourceId source matching found matchingValid blocksEq valuesEq =>
      rw [State.HasShrinkingElement, blocksEq, passBlocks]
      apply shrinking_insertAtDestinations
      apply exists_mem_modify_preserved present
      intro block selected property
      have equal : source = block := Option.some.inj (found.symm.trans selected)
      subst block
      exact ⟨property.1, mem_removeLosers_of_retained property.2 retains⟩
  | @split after sourceId source count found shrinking countLe blocksEq valuesEq =>
      rw [State.HasShrinkingElement, blocksEq, splitBlocks]
      by_cases inSource : element ∈ source.elements
      · have inParts : element ∈ source.elements.take count ++ source.elements.drop count := by
          simpa using inSource
        rcases List.mem_append.mp inParts with inPrefix | inSuffix
        · exact ⟨{ source with elements := source.elements.take count }, by simp, shrinking, inPrefix⟩
        · exact ⟨{ source with elements := source.elements.drop count }, by simp, shrinking, inSuffix⟩
      · obtain ⟨block, member, property⟩ := exists_mem_modify_preserved present sourceId
          (fun current => { current with elements := [] }) (by
            intro block selected property
            have equal : source = block := Option.some.inj (found.symm.trans selected)
            exact False.elim (inSource (equal ▸ property.2)))
        exact ⟨block, List.mem_append_left _ member, property⟩
  | decrease canDecrease blocksEq valuesEq =>
      simpa only [State.HasShrinkingElement, blocksEq] using present
  | increase canIncrease blocksEq valuesEq =>
      simpa only [State.HasShrinkingElement, blocksEq] using present

/-- Shrinking residence survives an entire actual operation prefix with no
prior leave of this element, including any number of splits. -/
theorem Trace.hasShrinkingElement_of_retains {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)} {element : Element n}
    (trace : Trace params initial operations final)
    (present : initial.HasShrinkingElement element)
    (retains : ∀ operation ∈ operations, operation.Retains element) :
    final.HasShrinkingElement element := by
  induction trace with
  | nil valid => exact present
  | @cons before middle after operation operations head tail ih =>
      apply ih (head.2.1.hasShrinkingElement_of_retains present (retains operation (by simp)))
      intro operation member
      exact retains operation (by simp [member])

end Splay.Interface
