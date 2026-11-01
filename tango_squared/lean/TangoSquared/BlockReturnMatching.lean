import TangoSquared.CyclicRuns

/-!
# Normalized returns imply matching cyclic coarse-run endpoints

This is a word theorem. It assumes the literal return property for two copies of
the flattened run word and derives the endpoint condition used by the turn
identity. It does not assume any equality of potentials or demand counts.
-/

namespace TangoSquared.CyclicRuns

variable {α C : Type*} [LinearOrder α] [LinearOrder C]

/-- The first local return after a nonempty outside excursion repeats its source. -/
def ReturnWord (coarse : α → C) (word : List α) : Prop :=
  ∀ pre a away b post, word = pre ++ a :: (away ++ b :: post) →
    coarse a = coarse b → away ≠ [] →
    (∀ z ∈ away, coarse z ≠ coarse a) → a = b

private theorem filter_isChain_of_gap_pairs {β : Type*} (p : β → Bool)
    (R : β → β → Prop) (xs : List β)
    (hgap : ∀ pre a middle b post, xs = pre ++ a :: (middle ++ b :: post) →
      p a = true → p b = true → (∀ z ∈ middle, p z ≠ true) → R a b) :
    List.IsChain R (xs.filter p) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have htail : List.IsChain R (xs.filter p) := by
      apply ih
      intro pre x middle y post heq hx hy hm
      exact hgap (a :: pre) x middle y post (by simpa using congrArg (List.cons a) heq) hx hy hm
    by_cases ha : p a = true
    · simp only [List.filter_cons, ha, ↓reduceIte]
      apply List.isChain_cons.mpr
      refine ⟨?_, htail⟩
      intro b hb
      cases hf : xs.filter p with
      | nil => simp [hf] at hb
      | cons c cs =>
        have hbc : b = c := by simpa [hf] using hb.symm
        subst b
        obtain ⟨middle, post, heq, hm, hc, hrest⟩ := List.filter_eq_cons_iff.mp hf
        exact hgap [] a middle c post (by simpa using congrArg (List.cons a) heq) ha hc hm
    · simpa [ha] using htail

omit [LinearOrder α] [LinearOrder C] in
private theorem adjacentDistinct_iff_isChain (coarse : α → C) (blocks : List (Block α)) :
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

private theorem isChain_double_of_cyclic {β : Type*} (R : β → β → Prop)
    (b : β) (bs : List β) (h : List.IsChain R ((b :: bs) ++ [b])) :
    List.IsChain R ((b :: bs) ++ (b :: bs)) := by
  obtain ⟨hchain, hsingle, hwrap⟩ := List.isChain_append.mp h
  apply List.isChain_append.mpr
  exact ⟨hchain, hchain, by simpa using hwrap⟩

private theorem isChain_cyclic_of_double {β : Type*} (R : β → β → Prop)
    (b : β) (bs : List β) (h : List.IsChain R ((b :: bs) ++ (b :: bs))) :
    List.IsChain R ((b :: bs) ++ [b]) := by
  obtain ⟨hchain, hchain', hwrap⟩ := List.isChain_append.mp h
  apply List.isChain_append.mpr
  exact ⟨hchain, by simp, by simpa using hwrap⟩

omit [LinearOrder α] in
private theorem matchingBoundaries_iff_isChain (closing : Block α) (blocks : List (Block α)) :
    MatchingBoundaries closing.first blocks ↔
      List.IsChain (fun b c : Block α => b.last = c.first) (blocks ++ [closing]) := by
  induction blocks with
  | nil => simp [MatchingBoundaries]
  | cons b bs ih =>
    cases bs with
    | nil => simp [MatchingBoundaries, List.isChain_cons]
    | cons c cs =>
      change (b.last = c.first ∧ MatchingBoundaries closing.first (c :: cs)) ↔
        List.IsChain (fun b c : Block α => b.last = c.first) (b :: c :: (cs ++ [closing]))
      rw [List.isChain_cons_cons]
      exact and_congr Iff.rfl ih

omit [LinearOrder α] in
private theorem block_word_prefix_last (b : Block α) :
    ∃ pre, b.word = pre ++ [b.last] := by
  cases b with
  | mk a as =>
    induction as using List.reverseRecOn with
    | nil => exact ⟨[], rfl⟩
    | append_singleton as z _ =>
      exact ⟨a :: as, by simp [Block.word, Block.last, List.cons_append]⟩

omit [LinearOrder α] in
/-- Consecutive retained coarse blocks have equal final/first fine labels. -/
theorem returnWord_filtered_blocks (coarse : α → C) (blocks : List (Block α))
    (homogeneous : ∀ b ∈ blocks, b.Homogeneous coarse)
    (adjacent : List.IsChain (fun b c => coarse b.first ≠ coarse c.first) blocks)
    (returns : ReturnWord coarse (blocks.map Block.word).flatten) (cell : C) :
    List.IsChain (fun b c : Block α => b.last = c.first) (cellBlocks coarse blocks cell) := by
  unfold cellBlocks
  apply filter_isChain_of_gap_pairs (fun (b : Block α) => decide (coarse b.first = cell))
  intro before b middle c after heq hb hc hm
  have hbcell : coarse b.first = cell := of_decide_eq_true hb
  have hccell : coarse c.first = cell := of_decide_eq_true hc
  have hbmem : b ∈ blocks := by rw [heq]; simp
  have hcmem : c ∈ blocks := by rw [heq]; simp
  have hbflat := homogeneous b hbmem
  have hcb : coarse b.last = coarse b.first := Block.homogeneous_last coarse b hbflat
  have hmiddle : middle ≠ [] := by
    intro hnil
    have ha := adjacent
    rw [heq, hnil] at ha
    have htail := (List.isChain_append.mp ha).2.1
    have hne := htail.rel
    exact hne (hbcell.trans hccell.symm)
  have haway : (middle.map Block.word).flatten ≠ [] := by
    cases middle with
    | nil => exact (hmiddle rfl).elim
    | cons z zs => simp [Block.word]
  obtain ⟨preB, hbword⟩ := block_word_prefix_last b
  apply returns ((before.map Block.word).flatten ++ preB) b.last
    (middle.map Block.word).flatten c.first (c.rest ++ (after.map Block.word).flatten)
  · simp only [heq, List.map_append, List.map_cons, List.flatten_append, List.flatten_cons]
    rw [hbword]
    simp [Block.word, List.append_assoc]
  · exact hcb.trans (hbcell.trans hccell.symm)
  · exact haway
  · intro z hz
    obtain ⟨word, hword, hzword⟩ := List.mem_flatten.mp hz
    obtain ⟨m, hmMem, rfl⟩ := List.mem_map.mp hword
    have hmblocks : m ∈ blocks := by rw [heq]; simp [hmMem]
    have hzcoarse := homogeneous m hmblocks z hzword
    intro hsame
    apply hm m hmMem
    apply decide_eq_true
    exact hzcoarse.symm.trans (hsame.trans (hcb.trans hbcell))

omit [LinearOrder α] in
/-- A literal return property for two periods forces every cyclic micro join to
have matching fine endpoints. -/
theorem returnsMatch_of_returnWord (coarse : α → C) (b : Block α) (bs : List (Block α))
    (homogeneous : ∀ c ∈ b :: bs, c.Homogeneous coarse)
    (boundary : DistinctBoundaries (coarse b.first)
      ((b :: bs).map (Block.coarseSingleton coarse)))
    (returns : ReturnWord coarse
      (((b :: bs).map Block.word).flatten ++ ((b :: bs).map Block.word).flatten)) :
    ReturnsMatch coarse (b :: bs) := by
  have hcycle : List.IsChain (fun b c => coarse b.first ≠ coarse c.first)
      ((b :: bs) ++ [b]) :=
    (adjacentDistinct_iff_isChain coarse _).mp ((adjacent_append_singleton coarse _ b).mpr boundary)
  have hdouble := isChain_double_of_cyclic _ b bs hcycle
  have hhom : ∀ c ∈ (b :: bs) ++ (b :: bs), c.Homogeneous coarse := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc <;> exact homogeneous c hc
  have hreturn : ReturnWord coarse ((((b :: bs) ++ (b :: bs)).map Block.word).flatten) := by
    simpa only [List.map_append, List.flatten_append] using returns
  intro cell hcell
  have hchain := returnWord_filtered_blocks coarse ((b :: bs) ++ (b :: bs)) hhom hdouble hreturn cell
  simp only [cellBlocks, List.filter_append] at hchain
  change List.IsChain (fun b c : Block α => b.last = c.first)
    (cellBlocks coarse (b :: bs) cell ++ cellBlocks coarse (b :: bs) cell) at hchain
  cases hf : cellBlocks coarse (b :: bs) cell with
  | nil => trivial
  | cons c cs =>
    rw [hf] at hchain
    exact (matchingBoundaries_iff_isChain c _).mpr (isChain_cyclic_of_double _ c cs hchain)

end TangoSquared.CyclicRuns
