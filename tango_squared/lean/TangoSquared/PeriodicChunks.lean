import TangoSquared.ChunkOccurrences

/-!
# Placing two rotated gap cycles inside four original periods

There are two independent changes of origin: the coarse-run layout and the
fixed-cell selected-run chunks. Their offsets add. Four copied periods contain
two complete chunk cycles without modular occurrence indices.
-/

namespace TangoSquared.PeriodicChunks

open CyclicRuns GapChunks

variable {α C : Type*} [LinearOrder α] [LinearOrder C]

def chunkQueryWord (c : Chunk (Block α)) : List α := (c.word.map Block.word).flatten

def chunkQueries (chunks : List (Chunk (Block α))) : List (List α) := chunks.map chunkQueryWord

omit [LinearOrder α] [LinearOrder C] in
theorem chunkQueries_flatten (chunks : List (Chunk (Block α))) :
    (chunkQueries chunks).flatten =
      (((chunks.map Chunk.word).flatten).map Block.word).flatten := by
  induction chunks with
  | nil => rfl
  | cons c cs ih =>
    simp only [chunkQueries, List.map_cons, List.flatten_cons, List.map_append,
      List.flatten_append, chunkQueryWord] at ih ⊢
    rw [ih]

omit [LinearOrder α] [LinearOrder C] in
theorem chunkQueryWord_nonempty (c : Chunk (Block α)) : chunkQueryWord c ≠ [] := by
  simp [chunkQueryWord, Chunk.word, Block.word]

omit [LinearOrder α] [LinearOrder C] in
theorem four_period_embedding (a b t s : List α) (second_cut : b ++ a = t ++ s) :
    (a ++ b) ++ ((a ++ b) ++ ((a ++ b) ++ (a ++ b))) =
      (a ++ t) ++ ((s ++ t) ++ ((s ++ t) ++ (s ++ b))) := by
  calc
    _ = a ++ ((b ++ a) ++ ((b ++ a) ++ ((b ++ a) ++ b))) := by
      simp only [List.append_assoc]
    _ = _ := by rw [second_cut]; simp only [List.append_assoc]

/-- Two full gap cycles fit in the literal four-period projected query word.
The prefix and suffix are explicitly retained for actual event constructors. -/
theorem layout_chunk_embedding {coarse : α → C} {xs : List α}
    (layout : CyclicLayout coarse xs)
    (selected : Block α → Bool)
    (chunks : CycleLayout selected (layout.first :: layout.rest)) :
    xs ++ (xs ++ (xs ++ xs)) =
      (layout.cutBefore ++ (chunks.cutBefore.map Block.word).flatten) ++
        ((chunkQueries chunks.chunks).flatten ++
          ((chunkQueries chunks.chunks).flatten ++
            ((chunks.cutAfter.map Block.word).flatten ++ layout.suffix))) := by
  have hsplit : ((layout.first :: layout.rest).map Block.word).flatten =
      (chunks.cutBefore.map Block.word).flatten ++ (chunks.cutAfter.map Block.word).flatten := by
    have h := congrArg (fun bs => (bs.map Block.word).flatten) chunks.split
    simpa only [List.map_append, List.flatten_append] using h
  have hsecond : layout.suffix ++ layout.cutBefore =
      (chunks.cutBefore.map Block.word).flatten ++ (chunks.cutAfter.map Block.word).flatten :=
    layout.rotation.symm.trans hsplit
  have hrot : (chunkQueries chunks.chunks).flatten =
      (chunks.cutAfter.map Block.word).flatten ++ (chunks.cutBefore.map Block.word).flatten := by
    rw [chunkQueries_flatten, chunks.rotation]
    simp only [List.map_append, List.flatten_append]
  have h := four_period_embedding layout.cutBefore layout.suffix
    (chunks.cutBefore.map Block.word).flatten (chunks.cutAfter.map Block.word).flatten hsecond
  simpa only [← layout.split, ← hrot] using h

omit [LinearOrder α] [LinearOrder C] in
/-- Every actual query in a chunk has an ordinary bounded occurrence index in
the doubled cycle. This is the word to which source and successor offsets apply. -/
theorem doubled_chunk_word (chunks : List (Chunk (Block α))) :
    (chunkQueries (chunks ++ chunks)).flatten =
      (chunkQueries chunks).flatten ++ (chunkQueries chunks).flatten := by
  simp [chunkQueries]

end TangoSquared.PeriodicChunks
