import DynamicOptimality.ColoredWalks.ShuffleModel
import DynamicOptimality.ColoredWalks.Embedding

/-! # The colored embedding on the observed finite alphabet

Deleting unobserved keys cannot introduce a new key between two neighbors
of one source walk. The dense ordered encoding keeps each color's order,
so the static colored-tree theorem applies to the actual walk steps.
-/

namespace DynamicOptimality.ColoredWalks.Encoding

open ChaCha.MTR

variable {n k : Nat} {events : List (Fin k × Fin n)}

def natLabel (encoding : Encoding events) (rank : Nat) : Fin encoding.count :=
  if bounded : rank < encoding.size then encoding.label ⟨rank,bounded⟩
  else ⟨0,encoding.count_pos⟩

@[simp] theorem natLabel_fin (encoding : Encoding events) (rank : Fin encoding.size) :
    encoding.natLabel rank.val = encoding.label rank := by
  simp only [natLabel,dif_pos rank.isLt]

theorem natLabel_encode (encoding : Encoding events) (event : Fin k × Fin n)
    (member : event ∈ events) :
    encoding.natLabel (encoding.encode event).val = encoding.color event.1 := by
  rw [natLabel_fin]
  simp only [label,encoding.decode_encode event member]

theorem le_same_color (encoding : Encoding events) (first last : Fin encoding.size)
    (same : (encoding.decode first).1 = (encoding.decode last).1) :
    (first ≤ last ↔ (encoding.decode first).2 ≤ (encoding.decode last).2) := by
  simpa only [not_lt] using not_congr (encoding.order_same_color last first same.symm)

theorem encoded_neighbors (encoding : Encoding events) (sets : Fin k → Finset (Fin n))
    (members : ∀ event ∈ events, event.2 ∈ sets event.1)
    (color : Fin k) (first last : Fin n)
    (firstMem : (color,first) ∈ events) (lastMem : (color,last) ∈ events)
    (step : NeighborStep (sets color) first last) (increasing : first < last) :
    Neighbors encoding.natLabel (List.range encoding.size)
      (encoding.encode (color,first)).val (encoding.encode (color,last)).val := by
  have firstDecode := encoding.decode_encode (color,first) firstMem
  have lastDecode := encoding.decode_encode (color,last) lastMem
  have same : (encoding.decode (encoding.encode (color,first))).1 =
      (encoding.decode (encoding.encode (color,last))).1 := by rw [firstDecode,lastDecode]
  have grows : encoding.encode (color,first) < encoding.encode (color,last) :=
    (encoding.order_same_color _ _ same).mpr (by simpa only [firstDecode,lastDecode] using increasing)
  refine ⟨List.mem_range.mpr (encoding.encode _).isLt,List.mem_range.mpr (encoding.encode _).isLt,
    grows,?_,?_⟩
  · rw [encoding.natLabel_encode _ firstMem,encoding.natLabel_encode _ lastMem]
  · intro index present colorEq
    let rank : Fin encoding.size := ⟨index,List.mem_range.mp present⟩
    have labelEq : encoding.color (encoding.decode rank).1 = encoding.color color := by
      change encoding.natLabel rank.val = _ at colorEq
      rw [natLabel_fin,encoding.natLabel_encode _ firstMem] at colorEq
      exact colorEq
    have sameFirst : (encoding.decode rank).1 = color := by
      have equal := (encoding.same_color rank (encoding.encode (color,first))).mp
        (by simpa only [firstDecode] using labelEq)
      simpa only [firstDecode] using equal
    have inSet : (encoding.decode rank).2 ∈ sets color := by
      simpa only [sameFirst] using members (encoding.decode rank) (encoding.decode_mem rank)
    rcases step.consecutive _ inSet with below | above
    · rw [min_eq_left increasing.le] at below
      have sameKeys : (encoding.decode rank).1 = (encoding.decode (encoding.encode (color,first))).1 := by
        simpa only [firstDecode] using sameFirst
      have bound := (encoding.le_same_color rank (encoding.encode (color,first)) sameKeys).mpr
        (by simpa only [firstDecode] using below)
      exact Or.inl bound
    · rw [max_eq_right increasing.le] at above
      have sameKeys : (encoding.decode (encoding.encode (color,last))).1 = (encoding.decode rank).1 := by
        simpa only [lastDecode] using sameFirst.symm
      have bound := (encoding.le_same_color (encoding.encode (color,last)) rank sameKeys).mpr
        (by simpa only [lastDecode] using above)
      exact Or.inr bound

theorem key_present (encoding : Encoding events) {tree : RawTree Nat} {height : Nat}
    (embedding : Embedding encoding.natLabel (List.range encoding.size) height tree)
    (rank : Fin encoding.size) : rank.val ∈ tree.inorder := by
  rw [embedding.word]
  exact List.mem_range.mpr rank.isLt

theorem stay_distance (encoding : Encoding events) {tree : RawTree Nat} {height budget : Nat}
    (embedding : Embedding encoding.natLabel (List.range encoding.size) height tree)
    (rank : Fin encoding.size) : DistanceLE tree rank.val rank.val budget := by
  obtain ⟨depth,path⟩ := exists_rootPath (encoding.key_present embedding rank)
  exact path.distance_self.mono (Nat.zero_le _)

theorem neighbor_distance (encoding : Encoding events) (sets : Fin k → Finset (Fin n))
    (members : ∀ event ∈ events, event.2 ∈ sets event.1)
    {tree : RawTree Nat} {height : Nat}
    (embedding : Embedding encoding.natLabel (List.range encoding.size) height tree)
    (color : Fin k) (first last : Fin n)
    (firstMem : (color,first) ∈ events) (lastMem : (color,last) ∈ events)
    (step : NeighborStep (sets color) first last) :
    DistanceLE tree (encoding.encode (color,first)).val (encoding.encode (color,last)).val (4*height) := by
  rcases lt_trichotomy first last with increasing | same | decreasing
  · exact embedding.neighbors _ _ (encoding.encoded_neighbors sets members color first last
      firstMem lastMem step increasing)
  · subst last
    exact encoding.stay_distance embedding _
  · exact (embedding.neighbors _ _ (encoding.encoded_neighbors sets members color last first
      lastMem firstMem step.symm decreasing)).symm

end DynamicOptimality.ColoredWalks.Encoding
