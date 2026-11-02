import ChaCha.RunOccurrences

/-!
# Constructing occurrence gaps by splitting an actual cyclic word

A selected occurrence starts a chunk; all following unselected occurrences up
to the next selected occurrence form its middle. Applied to coarse runs, select
the nontrivial runs of one fixed coarse cell. The resulting chunks are exactly
the demand gaps, retaining their full chronological block lists.
-/

namespace ChaCha.GapChunks

variable {β : Type*}

structure Chunk (β : Type*) where
  source : β
  middle : List β

def Chunk.word (c : Chunk β) : List β := c.source :: c.middle

/-- Structural scan; the accumulator consists of actual intervening occurrences. -/
def scan (selected : β → Bool) (source : β) (middle : List β) : List β → List (Chunk β)
  | [] => [⟨source, middle⟩]
  | x :: xs =>
      if selected x then ⟨source, middle⟩ :: scan selected x [] xs
      else scan selected source (middle ++ [x]) xs

theorem scan_flatten (selected : β → Bool) (source : β) (middle xs : List β) :
    ((scan selected source middle xs).map Chunk.word).flatten = source :: (middle ++ xs) := by
  induction xs generalizing source middle with
  | nil => simp [scan, Chunk.word]
  | cons x xs ih =>
    by_cases h : selected x = true
    · simp [scan, h, Chunk.word, ih]
    · simp [scan, h, ih, List.append_assoc]

/-- Sources enumerate selected occurrences in their actual visitation order. -/
theorem scan_sources (selected : β → Bool) (source : β) (middle xs : List β) :
    (scan selected source middle xs).map Chunk.source = source :: xs.filter selected := by
  induction xs generalizing source middle with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : selected x = true <;> simp [scan, h, ih]

theorem scan_nonempty (selected : β → Bool) (source : β) (middle xs : List β) :
    scan selected source middle xs ≠ [] := by
  intro h
  have hs := scan_sources selected source middle xs
  simp only [h, List.map_nil, List.nil_eq] at hs
  simp at hs

/-- A constructed chunk always starts at a selected occurrence and has no other
selected occurrence in its middle. -/
theorem scan_selected (selected : β → Bool) (source : β) (middle xs : List β)
    (hsource : selected source = true)
    (hmiddle : ∀ x ∈ middle, selected x = false) :
    ∀ c ∈ scan selected source middle xs,
      selected c.source = true ∧ ∀ x ∈ c.middle, selected x = false := by
  induction xs generalizing source middle with
  | nil => simpa [scan] using And.intro hsource hmiddle
  | cons x xs ih =>
    by_cases h : selected x = true
    · simp only [scan, h, ↓reduceIte, List.mem_cons]
      intro c hc
      rcases hc with rfl | hc
      · exact ⟨hsource, hmiddle⟩
      · exact ih x [] h (by simp) c hc
    · simp only [scan, h, Bool.false_eq_true, ↓reduceIte]
      apply ih source (middle ++ [x]) hsource
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hmiddle z hz
      · have heq : z = x := List.mem_singleton.mp hz
        subst z
        exact Bool.eq_false_iff.mpr h

/-- A cyclic chunk layout is an actual rotation, rather than merely a bijection
between counts. Prefix and suffix retain its embedding in two copied periods. -/
structure CycleLayout (selected : β → Bool) (xs : List β) where
  chunks : List (Chunk β)
  nonempty : chunks ≠ []
  cutBefore : List β
  cutAfter : List β
  split : xs = cutBefore ++ cutAfter
  rotation : (chunks.map Chunk.word).flatten = cutAfter ++ cutBefore
  source_selected : ∀ c ∈ chunks, selected c.source = true
  middle_unselected : ∀ c ∈ chunks, ∀ x ∈ c.middle, selected x = false
  number : chunks.length = (xs.filter selected).length

/-- Every nonempty set of selected occurrences has a canonical scan-based cyclic
gap decomposition, including the case of only one selected occurrence per period. -/
theorem exists_cycleLayout (selected : β → Bool) (xs : List β)
    (has_selected : ∃ x ∈ xs, selected x = true) : Nonempty (CycleLayout selected xs) := by
  obtain ⟨x, hx, hselected⟩ := has_selected
  obtain ⟨before, after, hsplit⟩ := List.mem_iff_append.mp hx
  let cs := scan selected x [] (after ++ before)
  have hvalid := scan_selected selected x [] (after ++ before) hselected (by simp)
  refine ⟨{
    chunks := cs
    nonempty := scan_nonempty selected x [] (after ++ before)
    cutBefore := before
    cutAfter := x :: after
    split := hsplit
    rotation := ?_
    source_selected := fun c hc => (hvalid c hc).1
    middle_unselected := fun c hc => (hvalid c hc).2
    number := ?_ }⟩
  · simpa only [cs, List.nil_append, List.cons_append] using
      scan_flatten selected x [] (after ++ before)
  · have hs := congrArg List.length (scan_sources selected x [] (after ++ before))
    simp only [List.length_map, List.length_cons, List.filter_append, List.length_append] at hs
    change cs.length = _ at hs
    rw [hsplit]
    simp only [List.filter_append, List.filter_cons, hselected, ↓reduceIte,
      List.length_append, List.length_cons]
    change cs.length = _
    omega

/-- Concatenating chunks introduces no unidentified query occurrences: their
lengths add to exactly the original period length. -/
theorem CycleLayout.total_length {selected : β → Bool} {xs : List β}
    (layout : CycleLayout selected xs) :
    ((layout.chunks.map Chunk.word).flatten).length = xs.length := by
  have hr := congrArg List.length layout.rotation
  have hs := congrArg List.length layout.split
  simp only [List.length_append] at hr hs
  omega

end ChaCha.GapChunks
