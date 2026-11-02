import ChaCha.GapChunks

/-!
# Genuine occurrence indices in concatenated run chunks

Repeated keys or identical-looking chunks remain distinct occurrences. Prefix
lengths locate each chosen source query in the actual concatenated query word.
These lemmas provide the injective time coordinates used by gap payments.
-/

namespace ChaCha.ChunkOccurrences

variable {α : Type*}

def offset (words : List (List α)) (i : ℕ) : ℕ := (words.take i).flatten.length

theorem offset_succ (words : List (List α)) (i : ℕ) (hi : i < words.length) :
    offset words (i + 1) = offset words i + words[i].length := by
  simp only [offset, List.take_succ_eq_append_getElem hi, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]

theorem offset_mono (words : List (List α)) : Monotone (offset words) := by
  intro i j hij
  obtain ⟨tail, ht⟩ := List.take_prefix_take_left (l := words) hij
  unfold offset
  rw [← ht, List.flatten_append, List.length_append]
  omega

theorem offset_strict (words : List (List α))
    (nonempty : ∀ word ∈ words, word ≠ []) {i j : ℕ}
    (hij : i < j) (hj : j ≤ words.length) : offset words i < offset words j := by
  have hi : i < words.length := lt_of_lt_of_le hij hj
  have hw := nonempty words[i] (List.getElem_mem hi)
  have hp : 0 < words[i].length := List.length_pos_iff.mpr hw
  have hs := offset_succ words i hi
  have hm := offset_mono words (by omega : i + 1 ≤ j)
  omega

/-- Chosen occurrences inside different words have strictly ordered global
indices, even when the words and the chosen keys themselves are equal. -/
theorem occurrence_time_lt (words : List (List α)) (i j : Fin words.length)
    (localI localJ : ℕ) (validI : localI < words[i].length)
    (hij : i.val < j.val) : offset words i.val + localI < offset words j.val + localJ := by
  simp only [Fin.getElem_fin] at validI
  have hs := offset_succ words i.val i.isLt
  have hm := offset_mono words (by omega : i.val + 1 ≤ j.val)
  omega

theorem occurrence_time_injective (words : List (List α))
    (localIndex : (i : Fin words.length) → ℕ)
    (valid : ∀ i, localIndex i < words[i].length) :
    Function.Injective (fun i => offset words i.val + localIndex i) := by
  intro i j heq
  dsimp only at heq
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := occurrence_time_lt words i j (localIndex i) (localIndex j) (valid i) hlt
    omega
  · have h := occurrence_time_lt words j i (localIndex j) (localIndex i) (valid j) hgt
    omega

/-- Expose a selected query occurrence, preserving the full chronological prefix
and suffix in the concatenated word. -/
theorem flatten_at_occurrence (words : List (List α)) (i : Fin words.length)
    (before after : List α) (x : α) (split : words[i] = before ++ x :: after) :
    words.flatten = (words.take i.val).flatten ++ before ++
      x :: (after ++ (words.drop (i.val + 1)).flatten) := by
  have hw : words = words.take i.val ++ words[i] :: words.drop (i.val + 1) := by
    simp only [Fin.getElem_fin]
    rw [← List.drop_eq_getElem_cons i.isLt]
    exact (List.take_append_drop i.val words).symm
  calc
    words.flatten = (words.take i.val).flatten ++ words[i] ++
        (words.drop (i.val + 1)).flatten := by
      conv_lhs => rw [hw]
      simp only [List.flatten_append, List.flatten_cons, List.append_assoc]
    _ = _ := by rw [split]; simp only [List.append_assoc, List.cons_append]

theorem occurrence_time_bound (words : List (List α)) (i : Fin words.length)
    (localIndex : ℕ) (valid : localIndex < words[i].length) :
    offset words i.val + localIndex < words.flatten.length := by
  simp only [Fin.getElem_fin] at valid
  have hs := offset_succ words i.val i.isLt
  have hm := offset_mono words (by omega : i.val + 1 ≤ words.length)
  have ht : offset words words.length = words.flatten.length := by simp [offset]
  omega

/-- The occurrence is not merely an abstract number: indexing the flattened
word at its computed time returns the literal requested key. -/
theorem getElem_occurrence (words : List (List α)) (i : Fin words.length)
    (before after : List α) (x : α) (split : words[i] = before ++ x :: after) :
    words.flatten[offset words i.val + before.length]'(by
      apply occurrence_time_bound words i before.length
      rw [split]
      simp) = x := by
  have hsplit := flatten_at_occurrence words i before after x split
  have hlen : ((words.take i.val).flatten ++ before).length = offset words i.val + before.length := by
    simp [offset]
  have h : (words.flatten)[((words.take i.val).flatten ++ before).length]? = some x := by
    rw [hsplit]
    rw [List.getElem?_append_right (by rfl), Nat.sub_self]
    rfl
  have hv : offset words i.val + before.length < words.flatten.length := by
    apply occurrence_time_bound words i before.length
    rw [split]
    simp
  rw [hlen, List.getElem?_eq_getElem hv] at h
  exact Option.some.inj h

end ChaCha.ChunkOccurrences
