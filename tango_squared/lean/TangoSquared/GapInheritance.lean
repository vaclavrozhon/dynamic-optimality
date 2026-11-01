import TangoSquared.ChunkRetention
import TangoSquared.GapChunks

/-! Actual interval and cyclic-boundary inheritance for query chunks. -/

namespace TangoSquared.GapInheritance

open CyclicRuns GapChunks

variable {α C : Type*} [LinearOrder α] [LinearOrder C]

omit [LinearOrder α] [LinearOrder C] in
theorem returnWord_infix (coarse : α → C) (before word after : List α)
    (h : ReturnWord coarse (before ++ word ++ after)) : ReturnWord coarse word := by
  intro pre a away b post he hc hn ha
  apply h (before ++ pre) a away b (post ++ after) _ hc hn ha
  simp only [he, List.append_assoc, List.cons_append]

omit [LinearOrder α] [LinearOrder C] in
theorem adjacent_iff_isChain (coarse : α → C) (blocks : List (Block α)) :
    AdjacentDistinct coarse blocks ↔
      List.IsChain (fun b c => coarse b.first ≠ coarse c.first) blocks := by
  induction blocks with
  | nil => simp [AdjacentDistinct]
  | cons b bs ih =>
    cases bs with
    | nil => simp [AdjacentDistinct]
    | cons c cs =>
      change (coarse b.first ≠ coarse c.first ∧ AdjacentDistinct coarse (c :: cs)) ↔ _
      rw [List.isChain_cons_cons]
      exact and_congr Iff.rfl ih

omit [LinearOrder α] [LinearOrder C] in
theorem adjacent_infix (coarse : α → C) (before blocks after : List (Block α))
    (h : AdjacentDistinct coarse (before ++ blocks ++ after)) : AdjacentDistinct coarse blocks := by
  apply (adjacent_iff_isChain coarse blocks).mpr
  exact ((adjacent_iff_isChain coarse _).mp h).infix ⟨before, after, rfl⟩

private theorem chain_triple_of_cycle {β : Type*} (R : β → β → Prop)
    (b : β) (bs : List β) (h : List.IsChain R ((b :: bs) ++ [b])) :
    List.IsChain R ((b :: bs) ++ (b :: bs) ++ (b :: bs)) := by
  obtain ⟨hc, _, hw⟩ := List.isChain_append.mp h
  have hd : List.IsChain R ((b :: bs) ++ (b :: bs)) :=
    List.isChain_append.mpr ⟨hc, hc, by simpa using hw⟩
  apply List.isChain_append.mpr
  refine ⟨hd, hc, ?_⟩
  simpa only [List.getLast?_append, List.getLast?_cons, Option.or_some,
    List.head?_cons, List.getLast?_singleton, Option.getD_some] using hw

omit [LinearOrder α] [LinearOrder C] in
/-- Any cut of a cyclic coarse-run word inherits its genuine coarse boundaries,
including the doubled rotated word used to extract occurrence gaps. -/
theorem rotated_double_adjacent (coarse : α → C) (b : Block α) (bs : List (Block α))
    (before after : List (Block α)) (split : b :: bs = before ++ after)
    (boundary : DistinctBoundaries (coarse b.first)
      ((b :: bs).map (Block.coarseSingleton coarse))) :
    AdjacentDistinct coarse ((after ++ before) ++ (after ++ before)) := by
  have hc := (adjacent_iff_isChain coarse _).mp
    ((adjacent_append_singleton coarse _ b).mpr boundary)
  have ht := chain_triple_of_cycle _ b bs hc
  rw [split] at ht
  apply (adjacent_iff_isChain coarse _).mpr
  apply ht.infix
  refine ⟨before, after, ?_⟩
  simp only [List.append_assoc]

omit [LinearOrder α] [LinearOrder C] in
/-- A block chunk is an actual contiguous fragment of the flattened block word.
Fine-label returns and homogeneity are inherited by the same fragment. -/
theorem returnWord_blocks_infix (coarse : α → C)
    (before blocks after : List (Block α))
    (h : ReturnWord coarse (((before ++ blocks ++ after).map Block.word).flatten)) :
    ReturnWord coarse ((blocks.map Block.word).flatten) := by
  apply returnWord_infix coarse (before.map Block.word).flatten _ (after.map Block.word).flatten
  simpa only [List.map_append, List.flatten_append] using h

end TangoSquared.GapInheritance
