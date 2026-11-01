import TangoSquared.GapChronology
import TangoSquared.ProjectedGapGeometry
import TangoSquared.CyclicGapAccounting

/-!
# Concrete last-micro sources and earliest delayed triggers

The source is the final unequal adjacent pair in a literal run word. Its prefix
length is an occurrence coordinate, and the resulting trigger decomposition
retains the entire chronological source prefix.
-/

namespace TangoSquared.GapSourceData

open CyclicRuns RunOccurrences ProjectedGapGeometry

variable {α C : Type*} [LinearOrder α] [LinearOrder C]

structure LastMicro (b : Block α) where
  before : List α
  source : α
  next : α
  tail : List α
  split : b.word = before ++ source :: next :: tail
  change : source ≠ next
  constant : ∀ z ∈ tail, z = next

/-- Every nontrivial run has a final fine change with a constant suffix. -/
theorem lastMicro_exists (b : Block α) (h : b.micro ≠ []) : Nonempty (LastMicro b) := by
  obtain ⟨before, y, p, tail, hs, hn, hc⟩ := exists_last_micro b.first b.rest h
  exact ⟨⟨before, y, p, tail, hs, hn, hc⟩⟩

omit [LinearOrder α] [LinearOrder C] in
theorem LastMicro.source_mem {b : Block α} (m : LastMicro b) : m.source ∈ b.word := by
  rw [m.split]
  simp

omit [LinearOrder α] [LinearOrder C] in
theorem LastMicro.next_mem {b : Block α} (m : LastMicro b) : m.next ∈ b.word := by
  rw [m.split]
  simp

omit [LinearOrder α] [LinearOrder C] in
theorem LastMicro.valid {b : Block α} (m : LastMicro b) : m.before.length < b.word.length := by
  rw [m.split]
  simp only [List.length_append, List.length_cons]
  omega

omit [LinearOrder α] [LinearOrder C] in
theorem LastMicro.final_label {b : Block α} (m : LastMicro b) : b.last = m.next :=
  last_label_of_last_micro b m.before m.source m.next m.tail m.split m.constant

omit [LinearOrder C] in
theorem LastMicro.direction {b : Block α} (m : LastMicro b) :
    b.micro.getLastD false = decide (m.source < m.next) :=
  last_micro_direction b m.before m.source m.next m.tail m.split m.change m.constant false

/-- Select the first opposite query following an actual run's final micro
change, preserving its complete source prefix in the larger query word. -/
theorem delayed_decomposition (coarse : α → C) (b : Block α) (m : LastMicro b)
    (word outerBefore middle outerAfter : List α)
    (word_split : word = outerBefore ++ b.word ++ middle ++ outerAfter)
    (homogeneous : b.Homogeneous coarse)
    (retained : ∀ z ∈ middle, coarse z = coarse b.first → z = m.next)
    (hit : ∃ z ∈ middle, Opposite coarse m.source m.next z) :
    ∃ earlier x post,
      word = (outerBefore ++ m.before) ++ m.source :: m.next :: (earlier ++ x :: post) ∧
      Opposite coarse m.source m.next x ∧
      (∀ z ∈ earlier, z = m.next ∨ (coarse z ≠ coarse m.source ∧
        ((m.source < m.next ∧ m.source < z) ∨ (m.next < m.source ∧ z < m.source)))) := by
  have hs : coarse m.source = coarse b.first := homogeneous m.source m.source_mem
  have hretain : ∀ z ∈ m.tail ++ middle, coarse z = coarse m.source → z = m.next := by
    intro z hz hzc
    rcases List.mem_append.mp hz with hz | hz
    · exact m.constant z hz
    · exact retained z hz (hzc.trans hs)
  have hh : ∃ z ∈ m.tail ++ middle, Opposite coarse m.source m.next z := by
    obtain ⟨z, hz, hp⟩ := hit
    exact ⟨z, List.mem_append.mpr (Or.inr hz), hp⟩
  obtain ⟨earlier, x, later, hgap, hopposite, hearlier⟩ :=
    first_opposite_split coarse m.source m.next (m.tail ++ middle) m.change hretain hh
  refine ⟨earlier, x, later ++ outerAfter, ?_, hopposite, hearlier⟩
  rw [word_split, m.split]
  simpa only [List.append_assoc, List.cons_append] using
    congrArg (fun xs => outerBefore ++ m.before ++ m.source :: m.next :: (xs ++ outerAfter)) hgap

omit [LinearOrder α] [LinearOrder C] in
/-- The last-micro source is inside its actual chunk query word. -/
theorem source_valid_in_chunk (c : GapChunks.Chunk (Block α)) (m : LastMicro c.source) :
    m.before.length < (PeriodicChunks.chunkQueryWord c).length := by
  have h := m.valid
  simp only [PeriodicChunks.chunkQueryWord, GapChunks.Chunk.word, List.map_cons,
    List.flatten_cons, List.length_append]
  omega

omit [LinearOrder α] [LinearOrder C] in
/-- Chosen last-micro sources in different chunks have different chronological
query coordinates. Repeated fine labels do not merge these occurrences. -/
theorem source_ordinal_injective (cs : List (GapChunks.Chunk (Block α)))
    (data : (i : Fin cs.length) → LastMicro cs[i].source) :
    Function.Injective (fun i =>
      (PeriodicChunks.chunkQueries (cs.take i.val)).flatten.length + (data i).before.length) := by
  intro i j heq
  have hvalid : ∀ k : Fin cs.length,
      (data k).before.length < ((PeriodicChunks.chunkQueries cs)[k.val]'(by simp [PeriodicChunks.chunkQueries])).length := by
    intro k
    have hk := source_valid_in_chunk cs[k] (data k)
    simp only [PeriodicChunks.chunkQueries, List.getElem_map, Fin.getElem_fin] at hk ⊢
    exact hk
  have hrewrite : ∀ k : Fin cs.length,
      (PeriodicChunks.chunkQueries (cs.take k.val)).flatten.length =
        ChunkOccurrences.offset (PeriodicChunks.chunkQueries cs) k.val := by
    intro k
    simp only [PeriodicChunks.chunkQueries, ChunkOccurrences.offset, List.map_take]
  dsimp only at heq
  rw [hrewrite i, hrewrite j] at heq
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · let hi : Fin (PeriodicChunks.chunkQueries cs).length := ⟨i.val, by simp [PeriodicChunks.chunkQueries]⟩
    let hj : Fin (PeriodicChunks.chunkQueries cs).length := ⟨j.val, by simp [PeriodicChunks.chunkQueries]⟩
    have ht := ChunkOccurrences.occurrence_time_lt (PeriodicChunks.chunkQueries cs) hi hj
      (data i).before.length (data j).before.length (hvalid i) hij
    dsimp only [hi, hj] at ht
    omega
  · let hi : Fin (PeriodicChunks.chunkQueries cs).length := ⟨i.val, by simp [PeriodicChunks.chunkQueries]⟩
    let hj : Fin (PeriodicChunks.chunkQueries cs).length := ⟨j.val, by simp [PeriodicChunks.chunkQueries]⟩
    have ht := ChunkOccurrences.occurrence_time_lt (PeriodicChunks.chunkQueries cs) hj hi
      (data j).before.length (data i).before.length (hvalid j) hji
    dsimp only [hi, hj] at ht
    omega

/-- A delayed side bit denotes an actual opposite-side key in the chunk's
intervening word, measured from its last-micro source. -/
theorem delayed_hit (coarse : α → C) (ordered : Monotone coarse) (cell : C)
    (c : GapChunks.Chunk (Block α)) (next : Block α) (m : LastMicro c.source)
    (homogeneous : c.source.Homogeneous coarse) (hcell : coarse c.source.first = cell)
    (delayed : (CyclicGapAccounting.outgoingGap coarse cell c next).delayed = 1) :
    ∃ z ∈ (c.middle.map Block.word).flatten, Opposite coarse m.source m.next z := by
  obtain ⟨z, hz, hzc, hdir⟩ :=
    (CyclicGapAccounting.outgoingGap_delayed_iff coarse cell c next).mp delayed
  have hs : coarse m.source = cell := (homogeneous m.source m.source_mem).trans hcell
  have hdiff : coarse z ≠ coarse m.source := by simpa only [hs] using hzc
  have hzsource : z ≠ m.source := fun he => hdiff (congrArg coarse he)
  refine ⟨z, hz, hdiff, ?_⟩
  apply (opposite_iff_direction_ne m.source m.next z m.change hzsource).mpr
  rw [direction_coarse coarse ordered m.source z (Ne.symm hdiff), hs, ← m.direction]
  exact hdir

end TangoSquared.GapSourceData
