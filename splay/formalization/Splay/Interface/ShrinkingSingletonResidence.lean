import Splay.Interface.ShrinkingResidence

namespace Splay.Interface

/-- An isolated shrinking element. The block ID may change through splits. -/
def State.HasShrinkingSingleton {n : ℕ} (state : State n) (element : Element n) : Prop :=
  ∃ (id : BlockId) (block : Block n), state.blocks[id]? = some block ∧
    block.mode = .shrinking ∧ block.elements = [element]

private theorem insertAtDestinations_get_unchanged {n : ℕ} (blocks : List (Block n))
    (matching : List (Pairing n)) (id : BlockId)
    (outside : ∀ pairing ∈ matching, pairing.destination ≠ id) :
    (insertAtDestinations blocks matching)[id]? = blocks[id]? := by
  induction matching generalizing blocks with
  | nil => rfl
  | cons pairing matching ih =>
      change (insertAtDestinations (blocks.modify pairing.destination fun destination =>
        { destination with elements := pairing.loser :: destination.elements }) matching)[id]? = blocks[id]?
      rw [ih _ (fun p member => outside p (List.mem_cons_of_mem _ member)), List.getElem?_modify]
      simp [outside pairing (by simp)]

private theorem removeLosers_singleton {n : ℕ} (element : Element n)
    (matching : List (Pairing n)) (retained : element ∉ pairingLosers matching) :
    removeLosers [element] matching = [element] := by
  induction matching with
  | nil => rfl
  | cons pairing matching ih =>
      have different : element ≠ pairing.loser := by
        intro equal
        exact retained (List.mem_map.mpr ⟨pairing, by simp, equal.symm⟩)
      change removeLosers ([element].erase pairing.loser) matching = [element]
      rw [show [element].erase pairing.loser = [element] by simp [different]]
      exact ih (by intro member; exact retained (List.mem_cons_of_mem _ member))

/-- Actual effects cannot enlarge an isolated shrinking block. If its element
never leaves, the unique nonempty split descendant stays a singleton. -/
theorem Effect.hasShrinkingSingleton_of_retains {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n} {element : Element n}
    (effect : Effect params before operation after)
    (present : before.HasShrinkingSingleton element) (retains : operation.Retains element) :
    after.HasShrinkingSingleton element := by
  obtain ⟨id, block, blockFound, blockShrinking, singleton⟩ := present
  cases effect with
  | @convert after selected selectedBlock found growing blocksEq valuesEq =>
      have outside : selected ≠ id := by
        intro equal
        change before.blocks[selected]? = some selectedBlock at found
        rw [equal, blockFound] at found
        have blockEq := Option.some.inj found
        rw [← blockEq, blockShrinking] at growing
        contradiction
      refine ⟨id, block, ?_, blockShrinking, singleton⟩
      rw [blocksEq, List.getElem?_modify]
      simp [outside, blockFound]
  | create room blocksEq valuesEq =>
      refine ⟨id, block, ?_, blockShrinking, singleton⟩
      rw [blocksEq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp blockFound).1]
      exact blockFound
  | @insert after selected selectedBlock inserted found growing unassigned valueOrder blocksEq valuesEq =>
      have outside : selected ≠ id := by
        intro equal
        change before.blocks[selected]? = some selectedBlock at found
        rw [equal, blockFound] at found
        have blockEq := Option.some.inj found
        rw [← blockEq, blockShrinking] at growing
        contradiction
      refine ⟨id, block, ?_, blockShrinking, singleton⟩
      rw [blocksEq, List.getElem?_modify]
      simp [outside, blockFound]
  | @delete after selected selectedBlock deleted found shrinking inside blocksEq valuesEq =>
      by_cases selectedId : selected = id
      · refine ⟨id, { block with elements := block.elements.erase deleted }, ?_, blockShrinking, ?_⟩
        · rw [blocksEq, List.getElem?_modify]
          simp [selectedId, blockFound]
        · rw [singleton]
          simp [show element ≠ deleted from retains]
      · refine ⟨id, block, ?_, blockShrinking, singleton⟩
        rw [blocksEq, List.getElem?_modify]
        simp [selectedId, blockFound]
  | @pass after sourceId source matching found matchingValid blocksEq valuesEq =>
      have outside : ∀ pairing ∈ matching, pairing.destination ≠ id := by
        intro pairing member equal
        obtain ⟨destination, destinationFound, destinationGrowing, creatorEq⟩ :=
          (matchingValid.2.2.2.1 pairing member).2.2.2
        change before.blocks[pairing.destination]? = some destination at destinationFound
        rw [equal, blockFound] at destinationFound
        have blockEq := Option.some.inj destinationFound
        rw [← blockEq, blockShrinking] at destinationGrowing
        contradiction
      by_cases same : sourceId = id
      · have blockEq : source = block := by
          change before.blocks[sourceId]? = some source at found
          rw [same, blockFound] at found
          exact Option.some.inj found.symm
        refine ⟨id, { source with passCount := source.passCount + 1, elements := removeLosers source.elements matching }, ?_, ?_, ?_⟩
        · rw [blocksEq, passBlocks, insertAtDestinations_get_unchanged _ _ _ outside, List.getElem?_modify]
          simp [same, blockFound]
        · simpa [blockEq] using blockShrinking
        · rw [blockEq, singleton]
          exact removeLosers_singleton element matching retains
      · refine ⟨id, block, ?_, blockShrinking, singleton⟩
        rw [blocksEq, passBlocks, insertAtDestinations_get_unchanged _ _ _ outside, List.getElem?_modify]
        simp [same, blockFound]
  | @split after sourceId source count found shrinking countLe blocksEq valuesEq =>
      by_cases same : sourceId = id
      · have blockEq : source = block := by
          change before.blocks[sourceId]? = some source at found
          rw [same, blockFound] at found
          exact Option.some.inj found.symm
        have sourceSingleton : source.elements = [element] := by simpa [blockEq] using singleton
        have countBound : count ≤ 1 := by simpa [sourceSingleton] using countLe
        have witness : ∃ block ∈ after.blocks, block.mode = .shrinking ∧ block.elements = [element] := by
          rw [blocksEq, splitBlocks]
          cases count with
          | zero =>
              exact ⟨{ source with elements := source.elements.drop 0 }, by simp,
                shrinking, by simpa using sourceSingleton⟩
          | succ count =>
              have zeroCount : count = 0 := by omega
              subst count
              exact ⟨{ source with elements := source.elements.take 1 }, by simp,
                shrinking, by simp [sourceSingleton]⟩
        obtain ⟨current, member, currentShrinking, currentSingleton⟩ := witness
        obtain ⟨currentId, currentFound⟩ := List.mem_iff_getElem?.mp member
        exact ⟨currentId, current, currentFound, currentShrinking, currentSingleton⟩
      · refine ⟨id, block, ?_, blockShrinking, singleton⟩
        rw [blocksEq, splitBlocks, List.getElem?_append_left (by
          simpa using (List.getElem?_eq_some_iff.mp blockFound).1), List.getElem?_modify]
        simp [same, blockFound]
  | decrease canDecrease blocksEq valuesEq =>
      exact ⟨id, block, by rw [blocksEq]; exact blockFound, blockShrinking, singleton⟩
  | increase canIncrease blocksEq valuesEq =>
      exact ⟨id, block, by rw [blocksEq]; exact blockFound, blockShrinking, singleton⟩

/-- Isolation survives every concrete trace prefix without a leave, including
arbitrary administrative splits and changes of block ID. -/
theorem Trace.hasShrinkingSingleton_of_retains {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)} {element : Element n}
    (trace : Trace params initial operations final)
    (present : initial.HasShrinkingSingleton element)
    (retains : ∀ operation ∈ operations, operation.Retains element) :
    final.HasShrinkingSingleton element := by
  induction trace with
  | nil valid => exact present
  | @cons before middle after operation operations head tail ih =>
      apply ih (head.2.1.hasShrinkingSingleton_of_retains present (retains operation (by simp)))
      intro operation member
      exact retains operation (by simp [member])

end Splay.Interface
