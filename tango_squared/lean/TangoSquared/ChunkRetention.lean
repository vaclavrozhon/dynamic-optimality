import TangoSquared.BlockReturnMatching
import TangoSquared.RunOccurrences

/-!
# Retained fine labels across actual coarse-run chunks

The middle of a demand gap may contain many other coarse cells and any number
of trivial returns to the selected cell. Literal normalized returns force all
such retained visits to use the old run's final fine label.
-/

namespace TangoSquared.ChunkRetention

open CyclicRuns RunOccurrences

variable {α C : Type*} [LinearOrder α] [LinearOrder C]

omit [LinearOrder α] [LinearOrder C] in
private theorem adjacent_isChain (coarse : α → C) (blocks : List (Block α))
    (h : AdjacentDistinct coarse blocks) :
    List.IsChain (fun b c => coarse b.first ≠ coarse c.first) blocks := by
  induction blocks with
  | nil => simp
  | cons b bs ih =>
    cases bs with
    | nil => simp
    | cons c cs => exact List.isChain_cons_cons.mpr ⟨h.1, ih h.2⟩

omit [LinearOrder α] in
/-- A retained endpoint chain, with its source and next nontrivial run explicit. -/
theorem endpoint_chain_iff_follows (a b : Block α) (middle : List (Block α)) :
    List.IsChain (fun p q : Block α => p.last = q.first) (a :: (middle ++ [b])) ↔
      Follows a.last b.first middle := by
  induction middle generalizing a with
  | nil => simp [Follows, List.isChain_cons_cons]
  | cons c cs ih =>
    change List.IsChain (fun p q : Block α => p.last = q.first) (a :: c :: (cs ++ [b])) ↔
      a.last = c.first ∧ Follows c.last b.first cs
    rw [List.isChain_cons_cons, ih]

/-- Between successive nontrivial runs of one cell, every retained visit in the
actual intervening word repeats the source run's final fine label. -/
theorem retained_between_runs (coarse : α → C) (cell : C)
    (a b : Block α) (middle : List (Block α))
    (ha : coarse a.first = cell) (hb : coarse b.first = cell)
    (homogeneous : ∀ c ∈ a :: (middle ++ [b]), c.Homogeneous coarse)
    (adjacent : AdjacentDistinct coarse (a :: (middle ++ [b])))
    (trivial : ∀ c ∈ middle, coarse c.first = cell → c.micro = [])
    (returns : ReturnWord coarse ((a :: (middle ++ [b])).map Block.word).flatten) :
    a.last = b.first ∧
      ∀ z ∈ cellWord coarse (middle.map Block.word).flatten cell, z = a.last := by
  have hchain := returnWord_filtered_blocks coarse (a :: (middle ++ [b])) homogeneous
    (adjacent_isChain coarse _ adjacent) returns cell
  have hfilter : cellBlocks coarse (a :: (middle ++ [b])) cell =
      a :: (cellBlocks coarse middle cell ++ [b]) := by
    simp [cellBlocks, ha, hb]
  rw [hfilter] at hchain
  have hlinks := (endpoint_chain_iff_follows a b (cellBlocks coarse middle cell)).mp hchain
  have htrivial : ∀ c ∈ cellBlocks coarse middle cell, c.micro = [] := by
    intro c hc
    obtain ⟨hcmem, hccell⟩ := List.mem_filter.mp hc
    exact trivial c hcmem (of_decide_eq_true hccell)
  have hretained := follows_trivial_constant a.last b.first (cellBlocks coarse middle cell) hlinks htrivial
  have hmiddle : ∀ c ∈ middle, c.Homogeneous coarse := by
    intro c hc
    exact homogeneous c (by simp [hc])
  rw [cellWord_blocks coarse middle cell hmiddle]
  exact hretained

/-- Add the source run's constant suffix and next run's constant prefix, retaining
all their actual query occurrences. This is the entire lifetime of the record. -/
theorem retained_source_tail_gap_target_prefix (coarse : α → C) (cell : C)
    (a b : Block α) (middle : List (Block α)) (sourceTail targetPrefix : List α) (p : α)
    (ha : coarse a.first = cell) (hb : coarse b.first = cell)
    (homogeneous : ∀ c ∈ a :: (middle ++ [b]), c.Homogeneous coarse)
    (adjacent : AdjacentDistinct coarse (a :: (middle ++ [b])))
    (trivial : ∀ c ∈ middle, coarse c.first = cell → c.micro = [])
    (returns : ReturnWord coarse ((a :: (middle ++ [b])).map Block.word).flatten)
    (last_source : a.last = p)
    (source_constant : ∀ z ∈ sourceTail, z = p)
    (target_constant : ∀ z ∈ targetPrefix, z = b.first) :
    b.first = p ∧
      ∀ z ∈ sourceTail ++ (middle.map Block.word).flatten ++ targetPrefix,
        coarse z = cell → z = p := by
  obtain ⟨hend, hmiddle⟩ := retained_between_runs coarse cell a b middle ha hb
    homogeneous adjacent trivial returns
  have htarget : b.first = p := hend.symm.trans last_source
  refine ⟨htarget, ?_⟩
  intro z hz hzcell
  simp only [List.mem_append] at hz
  rcases hz with (hz | hz) | hz
  · exact source_constant z hz
  · exact (hmiddle z (List.mem_filter.mpr ⟨hz, by simpa using hzcell⟩)).trans last_source
  · exact (target_constant z hz).trans htarget

end TangoSquared.ChunkRetention
