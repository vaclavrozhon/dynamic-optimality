import TangoSquared.PeriodicChunks

/-!
# Literal source-gap occurrence decompositions

A gap belongs to a specific occurrence of a selected run. We expose its source
and successor in two literal copies of the chunk cycle; no quotient of query
positions or identification of repeated keys is used.
-/

namespace TangoSquared.GapChronology

open CyclicRuns GapChunks PeriodicChunks ChunkOccurrences

variable {α : Type*}

/-- Two consecutive indexed elements, with their exact surrounding lists. -/
theorem adjacent_split (xs : List α) (i : Nat) (hi : i + 1 < xs.length) :
    xs = xs.take i ++ xs[i] :: xs[i+1] :: xs.drop (i+2) := by
  have hi₀ : i < xs.length := by omega
  have h := (List.take_append_drop i xs).symm
  rw [List.drop_eq_getElem_cons hi₀] at h
  rw [List.drop_eq_getElem_cons hi] at h
  simpa only [Nat.add_assoc] using h

/-- The successor of every source in the first cycle occurs in the doubled cycle. -/
def nextIndex (cs : List α) (i : Fin cs.length) : Fin (cs ++ cs).length :=
  ⟨i.val + 1, by simp only [List.length_append]; have := i.isLt; omega⟩

/-- Expose the actual source run, intervening blocks, and successor run of an
indexed outgoing gap. -/
theorem doubled_gap_split (cs : List (Chunk (Block α))) (i : Fin cs.length) :
    let next := (cs ++ cs)[nextIndex cs i]
    (chunkQueries (cs ++ cs)).flatten =
      (chunkQueries (cs.take i.val)).flatten ++ cs[i].source.word ++
        (cs[i].middle.map Block.word).flatten ++ next.source.word ++
          ((next.middle.map Block.word).flatten ++
            (chunkQueries ((cs ++ cs).drop (i.val + 2))).flatten) := by
  dsimp only
  have h := adjacent_split (cs ++ cs) i.val (nextIndex cs i).isLt
  have htake : (cs ++ cs).take i.val = cs.take i.val := by
    rw [List.take_append_of_le_length (Nat.le_of_lt i.isLt)]
  have hget : (cs ++ cs)[i.val] = cs[i] := by simp only [List.getElem_append_left i.isLt, Fin.getElem_fin]
  have hm := congrArg (fun ds => (chunkQueries ds).flatten) h
  rw [htake, hget] at hm
  simp only [chunkQueries, List.map_append, List.flatten_append, List.map_cons,
    List.flatten_cons, chunkQueryWord, Chunk.word, List.append_assoc,
    Fin.getElem_fin, nextIndex] at hm ⊢
  exact hm

/-- The same indexed gap decomposition at the level of actual blocks. -/
theorem doubled_gap_blocks_split {β : Type*} (cs : List (Chunk β)) (i : Fin cs.length) :
    let next := (cs ++ cs)[nextIndex cs i]
    (((cs ++ cs).map Chunk.word).flatten) =
      (((cs.take i.val).map Chunk.word).flatten) ++
        (cs[i].source :: (cs[i].middle ++ [next.source])) ++
          (next.middle ++ ((((cs ++ cs).drop (i.val + 2)).map Chunk.word).flatten)) := by
  dsimp only
  have h := adjacent_split (cs ++ cs) i.val (nextIndex cs i).isLt
  have htake : (cs ++ cs).take i.val = cs.take i.val := by
    rw [List.take_append_of_le_length (Nat.le_of_lt i.isLt)]
  have hget : (cs ++ cs)[i.val] = cs[i] := by simp only [List.getElem_append_left i.isLt, Fin.getElem_fin]
  have hm := congrArg (fun ds => (ds.map Chunk.word).flatten) h
  rw [htake, hget] at hm
  simp only [List.map_append, List.flatten_append, List.map_cons,
    List.flatten_cons, Chunk.word, List.append_assoc, List.cons_append,
    List.nil_append, Fin.getElem_fin, nextIndex] at hm ⊢
  exact hm

end TangoSquared.GapChronology
