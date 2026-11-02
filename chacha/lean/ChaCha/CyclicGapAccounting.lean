import ChaCha.GapChunks
import ChaCha.ChunkRetention

/-!
# Actual cyclic gaps between nontrivial runs

The gaps retain their intervening query words. Their join charges are exactly
those of the original cell's micro words; empty micro words and cyclic cuts do
not change this account.
-/

namespace ChaCha.CyclicGapAccounting

open CyclicRuns TurnAccounting GapChunks

variable {α C : Type*} [LinearOrder α] [LinearOrder C]

def selected (coarse : α → C) (cell : C) (b : Block α) : Bool :=
  decide (coarse b.first = cell ∧ b.micro ≠ [])

def outsideSides (coarse : α → C) (cell : C) (c : Chunk (Block α)) : List Bool :=
  ((((c.middle.map Block.word).flatten).filter (fun z => decide (coarse z ≠ cell))).map
    (fun z => decide (cell < coarse z)))

def outgoingGap (coarse : α → C) (cell : C) (c : Chunk (Block α))
    (next : Block α) : Gap where
  previousMicro := c.source.micro.getLastD false
  nextMicro := next.micro.headD false
  outsideSides := outsideSides coarse cell c

def gapsFrom (coarse : α → C) (cell : C) :
    Chunk (Block α) → List (Chunk (Block α)) → List Gap
  | _, [] => []
  | previous, c :: cs => outgoingGap coarse cell previous c.source :: gapsFrom coarse cell c cs

/-- One outgoing gap per actual selected source, in chronological source order. -/
def outgoingGaps (coarse : α → C) (cell : C) : List (Chunk (Block α)) → List Gap
  | [] => []
  | c :: cs => gapsFrom coarse cell c cs ++
      [outgoingGap coarse cell ((c :: cs).getLastD c) c.source]

@[simp] theorem gapsFrom_length (coarse : α → C) (cell : C)
    (c : Chunk (Block α)) (cs : List (Chunk (Block α))) :
    (gapsFrom coarse cell c cs).length = cs.length := by
  induction cs generalizing c with
  | nil => rfl
  | cons d ds ih => simp [gapsFrom, ih]

@[simp] theorem outgoingGaps_length (coarse : α → C) (cell : C)
    (cs : List (Chunk (Block α))) :
    (outgoingGaps coarse cell cs).length = cs.length := by
  cases cs <;> simp [outgoingGaps]

theorem gapsFrom_join (coarse : α → C) (cell : C) (previous : Chunk (Block α))
    (cs : List (Chunk (Block α)))
    (nonempty : ∀ c ∈ cs, c.source.micro ≠ []) :
    ((gapsFrom coarse cell previous cs).map Gap.join).sum =
      joinsFrom (previous.source.micro.getLastD false) (cs.map (fun c => c.source.micro)) := by
  induction cs generalizing previous with
  | nil => rfl
  | cons c cs ih =>
    have hc := nonempty c (by simp)
    cases h : c.source.micro with
    | nil => exact False.elim (hc h)
    | cons d ds =>
      simp only [gapsFrom, List.map_cons, List.sum_cons, Gap.join, outgoingGap, h,
        List.headD_cons, joinsFrom]
      rw [ih c (fun z hz => nonempty z (by simp [hz]))]
      simp only [h, List.getLastD_cons]

private theorem flatten_last_nonempty {β : Type*} (f : β → List Bool)
    (b : β) (bs : List β) (nonempty : ∀ z ∈ b :: bs, f z ≠ []) :
    (((b :: bs).map f).flatten).getLastD false = (f ((b :: bs).getLastD b)).getLastD false := by
  induction bs generalizing b with
  | nil => simp
  | cons c cs ih =>
    have hi := ih c (fun z hz => nonempty z (by simp only [List.mem_cons] at hz ⊢; tauto))
    have hn : ((c :: cs).map f).flatten ≠ [] := by
      intro he
      have hf := nonempty c (by simp)
      simp only [List.map_cons, List.flatten_cons, List.append_eq_nil_iff] at he
      exact hf he.1
    change (f b ++ ((c :: cs).map f).flatten).getLastD false = _
    rw [getLastD_append]
    have hf : (((c :: cs).map f).flatten).getLastD ((f b).getLastD false) =
        (((c :: cs).map f).flatten).getLastD false := by
      cases he : ((c :: cs).map f).flatten with
      | nil => exact False.elim (hn he)
      | cons d ds => simp only [List.getLastD_cons]
    rw [hf, hi]
    rfl

/-- Joining the actual successive selected runs counts all cyclic micro joins. -/
theorem outgoingGaps_join (coarse : α → C) (cell : C)
    (cs : List (Chunk (Block α))) (nonempty : ∀ c ∈ cs, c.source.micro ≠ []) :
    ((outgoingGaps coarse cell cs).map Gap.join).sum =
      cyclicJoins (cs.map (fun c => c.source.micro)) := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    have hc := nonempty c (by simp)
    have hl := flatten_last_nonempty (fun c : Chunk (Block α) => c.source.micro) c cs nonempty
    have hg := gapsFrom_join coarse cell c cs (fun z hz => nonempty z (by simp [hz]))
    unfold outgoingGaps cyclicJoins
    rw [hl]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero, Gap.join, outgoingGap]
    rw [hg]
    cases hm : c.source.micro with
    | nil => exact False.elim (hc hm)
    | cons d ds => simp only [List.headD_cons, joinsFrom, List.getLastD_cons]; omega

/-- Cyclic joins do not depend on the cut used to list the blocks. -/
theorem cyclicJoins_swap_append (as bs : List (List Bool)) :
    cyclicJoins (as ++ bs) = cyclicJoins (bs ++ as) := by
  have ha := cyclicTurns_flatten (as ++ bs)
  have hb := cyclicTurns_flatten (bs ++ as)
  have hr := CyclicRuns.cyclicTurns_swap_append as.flatten bs.flatten
  simp only [List.flatten_append, List.map_append, List.sum_append] at ha hb
  omega

private theorem joinsFrom_filter_empty {β : Type*} (p : β → Bool) (f : β → List Bool)
    (xs : List β) (hempty : ∀ x ∈ xs, p x = false → f x = []) (incoming : Bool) :
    joinsFrom incoming ((xs.filter p).map f) = joinsFrom incoming (xs.map f) := by
  induction xs generalizing incoming with
  | nil => rfl
  | cons x xs ih =>
    have ht : ∀ z ∈ xs, p z = false → f z = [] := fun z hz => hempty z (by simp [hz])
    cases h : p x with
    | false => simpa [h, hempty x (by simp) h, joinsFrom] using ih ht incoming
    | true =>
      cases hw : f x with
      | nil => simpa [h, hw, joinsFrom] using ih ht incoming
      | cons d ds => simpa [h, hw, joinsFrom] using congrArg (fun n => turn incoming d + n) (ih ht (ds.getLastD d))

private theorem flatten_filter_empty {β : Type*} (p : β → Bool) (f : β → List Bool)
    (xs : List β) (hempty : ∀ x ∈ xs, p x = false → f x = []) :
    ((xs.filter p).map f).flatten = (xs.map f).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ht : ∀ z ∈ xs, p z = false → f z = [] := fun z hz => hempty z (by simp [hz])
    cases h : p x <;> simp [h, hempty x (by simp), ih ht]

theorem cyclicJoins_filter_empty {β : Type*} (p : β → Bool) (f : β → List Bool)
    (xs : List β) (hempty : ∀ x ∈ xs, p x = false → f x = []) :
    cyclicJoins ((xs.filter p).map f) = cyclicJoins (xs.map f) := by
  unfold cyclicJoins
  rw [flatten_filter_empty p f xs hempty]
  exact joinsFrom_filter_empty p f xs hempty _

theorem selected_filter (coarse : α → C) (cell : C) (blocks : List (Block α)) :
    blocks.filter (selected coarse cell) =
      (cellBlocks coarse blocks cell).filter (fun b => decide (b.micro ≠ [])) := by
  simp only [cellBlocks, List.filter_filter]
  apply List.filter_congr
  intro b hb
  simp [selected, Bool.and_comm]

theorem selected_micro_joins (coarse : α → C) (cell : C) (blocks : List (Block α)) :
    cyclicJoins ((blocks.filter (selected coarse cell)).map Block.micro) =
      cyclicJoins ((cellBlocks coarse blocks cell).map Block.micro) := by
  rw [selected_filter]
  apply cyclicJoins_filter_empty
  intro b hb hn
  simpa only [decide_eq_false_iff_not, not_not] using hn

private theorem filter_chunk_flatten {β : Type*} (p : β → Bool)
    (cs : List (Chunk β))
    (hsource : ∀ c ∈ cs, p c.source = true)
    (hmiddle : ∀ c ∈ cs, ∀ x ∈ c.middle, p x = false) :
    ((cs.map Chunk.word).flatten).filter p = cs.map Chunk.source := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hm : c.middle.filter p = [] := List.filter_eq_nil_iff.mpr (fun x hx => by rw [hmiddle c (by simp) x hx]; decide)
    simp only [List.map_cons, List.flatten_cons, List.filter_append, Chunk.word,
      List.filter_cons, hsource c (by simp), ↓reduceIte, hm, List.cons_append, List.nil_append]
    rw [ih (fun z hz => hsource z (by simp [hz])) (fun z hz => hmiddle z (by simp [hz]))]

/-- The exact join account in the original coarse-cell word, retaining occurrence
multiplicity through the actual cyclic chunk decomposition. -/
theorem layout_joins (coarse : α → C) (cell : C) (blocks : List (Block α))
    (layout : CycleLayout (selected coarse cell) blocks) :
    ((outgoingGaps coarse cell layout.chunks).map Gap.join).sum =
      cyclicJoins ((cellBlocks coarse blocks cell).map Block.micro) := by
  have hn : ∀ c ∈ layout.chunks, c.source.micro ≠ [] := by
    intro c hc
    exact (of_decide_eq_true (layout.source_selected c hc)).2
  rw [outgoingGaps_join coarse cell layout.chunks hn]
  have hf := filter_chunk_flatten (selected coarse cell) layout.chunks
    layout.source_selected layout.middle_unselected
  rw [layout.rotation] at hf
  have hm := congrArg (fun bs => bs.map Block.micro) hf
  simp only [List.map_map, Function.comp_def, List.filter_append, List.map_append] at hm
  rw [← hm, cyclicJoins_swap_append]
  have hs := selected_micro_joins coarse cell blocks
  rw [layout.split, List.filter_append, List.map_append] at hs
  simpa only [← layout.split] using hs

/-- Every selected nontrivial run receives one genuine cyclic gap charge. -/
theorem layout_cover (coarse : α → C) (cell : C) (blocks : List (Block α))
    (layout : CycleLayout (selected coarse cell) blocks) :
    (blocks.filter (selected coarse cell)).length ≤
      ((outgoingGaps coarse cell layout.chunks).map Gap.delayed).sum +
      ((outgoingGaps coarse cell layout.chunks).map Gap.entry).sum +
      cyclicJoins ((cellBlocks coarse blocks cell).map Block.micro) := by
  have h := gaps_cover (outgoingGaps coarse cell layout.chunks)
  rw [outgoingGaps_length, layout.number, layout_joins] at h
  exact h

/-- A delayed Boolean charge is witnessed by an actual outside query in the
intervening block word, not by an auxiliary side label. -/
theorem outgoingGap_delayed_iff (coarse : α → C) (cell : C)
    (c : Chunk (Block α)) (next : Block α) :
    (outgoingGap coarse cell c next).delayed = 1 ↔
      ∃ z ∈ (c.middle.map Block.word).flatten,
        coarse z ≠ cell ∧ decide (cell < coarse z) ≠ c.source.micro.getLastD false := by
  have hb (v : Bool) : (if v then 1 else 0) = (1 : ℕ) ↔ v = true := by
    cases v <;> decide
  change (if (outsideSides coarse cell c).any
      (fun side => side != c.source.micro.getLastD false) then 1 else 0) = 1 ↔ _
  rw [hb]
  simp only [outsideSides, List.any_map, List.any_eq_true, List.mem_filter,
    decide_eq_true_eq, bne_iff_ne, Function.comp_apply]
  constructor
  · rintro ⟨z, ⟨hz, hcell⟩, hdir⟩
    exact ⟨z, hz, hcell, hdir⟩
  · rintro ⟨z, hz, hcell, hdir⟩
    exact ⟨z, ⟨hz, hcell⟩, hdir⟩

private theorem filter_length_micro (blocks : List (Block α)) :
    (blocks.filter (fun b => decide (b.micro ≠ []))).length = nontrivialRuns blocks := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
    simp only [nontrivialRuns] at ih ⊢
    by_cases h : b.micro = [] <;> simp [h, Nat.add_comm] <;>
      simpa only [decide_not] using ih

theorem selected_count (coarse : α → C) (cell : C) (blocks : List (Block α)) :
    (blocks.filter (selected coarse cell)).length =
      nontrivialRuns (cellBlocks coarse blocks cell) := by
  rw [selected_filter, filter_length_micro]

/-- Selected demands partition by their actual coarse cell. -/
theorem sum_selected_counts (coarse : α → C) (blocks : List (Block α)) :
    ∑ cell ∈ cells coarse blocks, (blocks.filter (selected coarse cell)).length =
      nontrivialRuns blocks := by
  simp_rw [selected_count]
  apply sum_cell_blocks coarse blocks (fun b => if b.micro = [] then 0 else 1)
  intro b hb
  simp only [cells, List.mem_toFinset, List.mem_map]
  exact ⟨b, hb, rfl⟩

omit [LinearOrder α] [LinearOrder C] in
private theorem adjacent_last (coarse : α → C) (a b : Block α)
    (middle : List (Block α))
    (h : AdjacentDistinct coarse (a :: (middle ++ [b]))) :
    coarse ((a :: middle).getLastD a).first ≠ coarse b.first := by
  induction middle generalizing a with
  | nil => exact h.1
  | cons c cs ih =>
    exact ih c h.2

omit [LinearOrder α] [LinearOrder C] in
/-- The final intervening run is outside the selected cell. Distinct adjacent
coarse runs also ensure that the intervening list is genuinely nonempty. -/
theorem outgoing_middle_last (coarse : α → C) (cell : C)
    (c : Chunk (Block α)) (next : Block α)
    (hsource : coarse c.source.first = cell) (hnext : coarse next.first = cell)
    (adjacent : AdjacentDistinct coarse (c.word ++ [next])) :
    c.middle ≠ [] ∧ coarse (c.word.getLastD c.source).first ≠ cell := by
  have hlast := adjacent_last coarse c.source next c.middle adjacent
  rw [hnext] at hlast
  refine ⟨?_, hlast⟩
  intro he
  simp only [he, List.getLastD_cons, List.getLastD_nil, hsource, ne_eq, not_true_eq_false] at hlast

omit [LinearOrder α] in
private theorem outsideSides_last_concat (coarse : α → C) (cell : C)
    (c : Chunk (Block α)) (before : List (Block α)) (last : Block α)
    (split : c.middle = before ++ [last])
    (homogeneous : last.Homogeneous coarse) (outside : coarse last.first ≠ cell)
    (fallback : Bool) :
    (outsideSides coarse cell c).getLastD fallback = decide (cell < coarse last.last) := by
  have hf : last.word.filter (fun z => decide (coarse z ≠ cell)) = last.word := by
    apply List.filter_eq_self.mpr
    intro z hz
    simp only [decide_eq_true_eq]
    rw [homogeneous z hz]
    exact outside
  unfold outsideSides
  rw [split]
  simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.filter_append, hf, List.map_append]
  rw [getLastD_append]
  change ((last.first :: last.rest).map (fun z => decide (cell < coarse z))).getLastD _ = _
  simp only [List.map_cons, List.getLastD_cons]
  exact List.getLastD_map

/-- The gap's entry charge is exactly the destination run's actual incoming
macro-to-micro turn. -/
theorem outgoingGap_entry (coarse : α → C) (ordered : Monotone coarse) (cell : C)
    (c : Chunk (Block α)) (next : Block α)
    (hsource : coarse c.source.first = cell) (hnext : coarse next.first = cell)
    (nontrivial : next.micro ≠ [])
    (homogeneous : ∀ b ∈ c.middle, b.Homogeneous coarse)
    (adjacent : AdjacentDistinct coarse (c.word ++ [next])) :
    (outgoingGap coarse cell c next).entry =
      (Run.mk next.micro false).entryTurn
        (decide ((c.word.getLastD c.source).last < next.first)) := by
  obtain ⟨hn, hout⟩ := outgoing_middle_last coarse cell c next hsource hnext adjacent
  obtain he | ⟨before, last, hsplit⟩ := List.eq_nil_or_concat c.middle
  · exact False.elim (hn he)
  have hlast : c.word.getLastD c.source = last := by
    simp only [Chunk.word, hsplit, List.concat_eq_append, List.getLastD_cons, List.getLastD_concat]
  rw [hlast] at hout ⊢
  have hh := homogeneous last (by simp [hsplit])
  have ho := outsideSides_last_concat coarse cell c before last (by simpa only [List.concat_eq_append] using hsplit) hh hout
  have hdiff : coarse last.last ≠ coarse next.first := by
    rw [Block.homogeneous_last coarse last hh, hnext]
    exact hout
  have hd := direction_coarse coarse ordered last.last next.first hdiff
  rw [hnext] at hd
  have hnot : (!decide (cell < coarse last.last)) = decide (coarse last.last < cell) := by
    have he : coarse last.last ≠ cell := by
      rw [Block.homogeneous_last coarse last hh]
      exact hout
    rcases lt_or_gt_of_ne he with hlt | hgt
    · simp [hlt, not_lt_of_gt hlt]
    · simp [hgt, not_lt_of_gt hgt]
  unfold Gap.entry outgoingGap
  rw [ho, hnot, ← hd]
  cases hm : next.micro with
  | nil => exact False.elim (nontrivial hm)
  | cons d ds => rfl

end ChaCha.CyclicGapAccounting
