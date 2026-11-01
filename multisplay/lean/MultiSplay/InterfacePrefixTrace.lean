import MultiSplay.InterfacePrefix

/-! # Chronological component execution with a persistent passive frame -/

namespace MultiSplay.InterfacePrefix

open Splay.Interface
open InterfaceEmbedding (block)
open InterfaceBlockIds (modify_prefix pass_prefix split_prefix)

variable {n m : Nat}

theorem effect (embedding : Element n → Element m) (injective : Function.Injective embedding)
    (frame : State m) (passive : Passive embedding frame)
    {params : Parameters} {before after : State n} {op : Operation n}
    (execution : Effect params before op after) :
    Effect params (state embedding frame before) (operation embedding frame op) (state embedding frame after) := by
  cases execution with
  | convert lookup growing blocksEq valuesEq =>
      rename_i id oldBlock
      refine .convert (block := block embedding oldBlock) (by simp only [found, lookup, Option.map_some]) growing ?_ ?_
      · change frame.blocks ++ after.blocks.map (block embedding) = _
        rw [blocksEq, map_modify (block embedding) _ (fun old => {old with mode := .shrinking}) (fun _ => rfl)]
        exact (modify_prefix _ _ _ _).symm
      · simp only [state, valuesEq]
  | create room blocksEq valuesEq =>
      refine .create ?_ ?_ ?_
      · simpa only [growing_image embedding injective frame passive] using room
      · simp only [state, blocksEq, List.map_append, List.map_cons, List.map_nil, block, List.append_assoc]
      · simp only [state, valuesEq]
  | insert lookup growing unassigned ordered blocksEq valuesEq =>
      rename_i id oldBlock element
      refine .insert (block := block embedding oldBlock) (by simp only [found, lookup, Option.map_some]) growing ?_ ?_ ?_ ?_
      · rw [allElements]
        intro member
        rcases List.mem_append.mp member with foreign | own
        · exact passive.elements _ foreign element rfl
        · obtain ⟨old, oldMem, same⟩ := List.mem_map.mp own
          exact unassigned (injective same ▸ oldMem)
      · simpa only [block, value_image embedding injective] using ordered
      · change frame.blocks ++ after.blocks.map (block embedding) = _
        rw [blocksEq, map_modify (block embedding) _ (fun old => {old with elements := embedding element :: old.elements}) (fun _ => rfl)]
        exact (modify_prefix _ _ _ _).symm
      · simp only [state, valuesEq]
  | delete lookup shrinking present blocksEq valuesEq =>
      rename_i id oldBlock element
      refine .delete (block := block embedding oldBlock) (by simp only [found, lookup, Option.map_some]) shrinking ?_ ?_ ?_
      · exact List.mem_map.mpr ⟨_, present, rfl⟩
      · change frame.blocks ++ after.blocks.map (block embedding) = _
        rw [blocksEq, map_modify (block embedding) _ (fun old => {old with elements := old.elements.erase (embedding element)})
          (fun old => by simp [block, List.map_erase injective])]
        exact (modify_prefix _ _ _ _).symm
      · simp only [state, valuesEq]
  | pass lookup matching blocksEq valuesEq =>
      refine .pass (by simp only [found, lookup, Option.map_some])
        (matching_valid embedding injective frame _ _ _ _ _ matching) ?_ ?_
      · change frame.blocks ++ after.blocks.map (block embedding) = _
        rw [blocksEq, InterfaceEmbedding.passBlocks_map embedding injective]
        exact (pass_prefix _ _ _ _ _).symm
      · simp only [state, valuesEq]
  | split lookup shrinking prefixLe blocksEq valuesEq =>
      rename_i id oldBlock count
      refine .split (source := block embedding oldBlock) (by simp only [found, lookup, Option.map_some]) shrinking ?_ ?_ ?_
      · simpa [block] using prefixLe
      · change frame.blocks ++ after.blocks.map (block embedding) = _
        rw [blocksEq, InterfaceEmbedding.splitBlocks_map]
        exact (split_prefix _ _ _ _ _).symm
      · simp only [state, valuesEq]
  | decrease allowed blocksEq valuesEq =>
      refine .decrease ?_ ?_ ?_
      · simpa only [value_image embedding injective] using allowed
      · simp only [state, blocksEq]
      · simp only [state, valuesEq, update_value embedding injective, injective.extend_apply]
  | increase allowed blocksEq valuesEq =>
      refine .increase ?_ ?_ ?_
      · simpa only [value_image embedding injective] using allowed
      · simp only [state, blocksEq]
      · simp only [state, valuesEq, update_value embedding injective, injective.extend_apply]

theorem step (embedding : Element n → Element m) (injective : Function.Injective embedding)
    (frame : State m) (passive : Passive embedding frame) {params : Parameters} (frameValid : frame.Valid params)
    {before after : State n} {op : Operation n} (execution : Step params before op after) :
    Step params (state embedding frame before) (operation embedding frame op) (state embedding frame after) :=
  ⟨valid embedding injective frame passive frameValid execution.1,
    effect embedding injective frame passive execution.2.1,
    valid embedding injective frame passive frameValid execution.2.2⟩

theorem trace (embedding : Element n → Element m) (injective : Function.Injective embedding)
    (frame : State m) (passive : Passive embedding frame) {params : Parameters} (frameValid : frame.Valid params)
    {before after : State n} {word : List (Operation n)} (execution : Trace params before word after) :
    Trace params (state embedding frame before) (word.map (operation embedding frame)) (state embedding frame after) := by
  induction execution with
  | nil bounded => exact .nil (valid embedding injective frame passive frameValid bounded)
  | cons head tail ih => exact .cons (step embedding injective frame passive frameValid head) ih

@[simp] theorem activity (embedding : Element n → Element m) (frame : State m) (word : List (Operation n)) :
    totalActivity (word.map (operation embedding frame)) = totalActivity word := by
  change totalActivity (word.map (InterfaceBlockIds.operation (frame.blocks.length + ·) ∘ InterfaceEmbedding.operation embedding)) = _
  rw [← List.map_map, InterfaceBlockIds.activity, InterfaceEmbedding.activity]

@[simp] theorem inserts (embedding : Element n → Element m) (frame : State m) (word : List (Operation n)) :
    totalInserts (word.map (operation embedding frame)) = totalInserts word := by
  change totalInserts (word.map (InterfaceBlockIds.operation (frame.blocks.length + ·) ∘ InterfaceEmbedding.operation embedding)) = _
  rw [← List.map_map, InterfaceBlockIds.inserts, InterfaceEmbedding.inserts]

@[simp] theorem increases (embedding : Element n → Element m) (frame : State m) (word : List (Operation n)) :
    totalIncreases (word.map (operation embedding frame)) = totalIncreases word := by
  change totalIncreases (word.map (InterfaceBlockIds.operation (frame.blocks.length + ·) ∘ InterfaceEmbedding.operation embedding)) = _
  rw [← List.map_map, InterfaceBlockIds.increases, InterfaceEmbedding.increases]

@[simp] theorem decreases (embedding : Element n → Element m) (frame : State m) (word : List (Operation n)) :
    totalDecreases (word.map (operation embedding frame)) = totalDecreases word := by
  change totalDecreases (word.map (InterfaceBlockIds.operation (frame.blocks.length + ·) ∘ InterfaceEmbedding.operation embedding)) = _
  rw [← List.map_map, InterfaceBlockIds.decreases, InterfaceEmbedding.decreases]

end MultiSplay.InterfacePrefix
