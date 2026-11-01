import TangoSquared.PaymentFamilies
import TangoSquared.DelayedChunkPayments

/-!
# Finite delayed-payment occurrences in cell-specific chunk cycles

A delayed charge belongs to its source chunk. Its Boolean value is independent
of the following selected run, so its positive indexed occurrences count the
literal outgoing-gap delayed sum exactly.
-/

namespace TangoSquared.DelayedPayments

open Primary Witnesses NormalizedWords CyclicRuns GapChunks CyclicGapAccounting TurnAccounting

variable {α C : Type*} [LinearOrder α] [LinearOrder C]

/-- Visited coarse cells with at least one nontrivial source run. -/
def activeCells (coarse : α → C) (blocks : List (Block α)) : Finset C :=
  (CyclicRuns.cells coarse blocks).filter
    (fun cell => (blocks.filter (selected coarse cell)).length > 0)

theorem activeCells_subset (coarse : α → C) (blocks : List (Block α)) :
    activeCells coarse blocks ⊆ CyclicRuns.cells coarse blocks := Finset.filter_subset _ _

/-- Every active cell has a literal selected run occurrence. -/
theorem activeCell_has_selected (coarse : α → C) (blocks : List (Block α))
    {cell : C} (hc : cell ∈ activeCells coarse blocks) :
    ∃ b ∈ blocks, selected coarse cell b = true := by
  have hp := (Finset.mem_filter.mp hc).2
  cases hfilter : blocks.filter (selected coarse cell) with
  | nil => simp only [hfilter, List.length_nil] at hp; omega
  | cons b bs =>
    have hb : b ∈ blocks.filter (selected coarse cell) := by rw [hfilter]; simp
    obtain ⟨hm, hs⟩ := List.mem_filter.mp hb
    exact ⟨b, hm, hs⟩

/-- Choose the proved chronological chunk layout for every active cell. -/
noncomputable def activeLayout (coarse : α → C) (blocks : List (Block α))
    (cell : activeCells coarse blocks) : CycleLayout (selected coarse cell.val) blocks :=
  Classical.choice (exists_cycleLayout (selected coarse cell.val) blocks
    (activeCell_has_selected coarse blocks cell.property))

/-- The delayed charge depends on the source and its intervening word. -/
def delayedWeight (coarse : α → C) (cell : C) (c : Chunk (Block α)) : Nat :=
  (outgoingGap coarse cell c c.source).delayed

@[simp] theorem outgoingGap_delayed_eq_weight (coarse : α → C) (cell : C)
    (c : Chunk (Block α)) (next : Block α) :
    (outgoingGap coarse cell c next).delayed = delayedWeight coarse cell c := rfl

theorem delayedWeight_le_one (coarse : α → C) (cell : C) (c : Chunk (Block α)) :
    delayedWeight coarse cell c ≤ 1 := by
  unfold delayedWeight Gap.delayed
  split <;> omega

private theorem gapsFrom_delayed_append (coarse : α → C) (cell : C)
    (previous : Chunk (Block α)) (cs : List (Chunk (Block α))) :
    (gapsFrom coarse cell previous cs).map Gap.delayed ++
      [delayedWeight coarse cell (cs.getLastD previous)] =
        (previous :: cs).map (delayedWeight coarse cell) := by
  induction cs generalizing previous with
  | nil => rfl
  | cons c cs ih =>
    simpa only [gapsFrom, List.map_cons, outgoingGap_delayed_eq_weight, List.cons_append,
      List.getLastD_cons] using congrArg (List.cons (delayedWeight coarse cell previous)) (ih c)

theorem outgoingGaps_delayed_map (coarse : α → C) (cell : C)
    (cs : List (Chunk (Block α))) :
    (outgoingGaps coarse cell cs).map Gap.delayed = cs.map (delayedWeight coarse cell) := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    simp only [outgoingGaps, List.map_append, List.map_cons, List.map_nil,
      outgoingGap_delayed_eq_weight]
    simpa only [List.getLastD_cons, List.map_cons] using gapsFrom_delayed_append coarse cell c cs

/-- Positive delayed payments indexed by source occurrences, including repeated
identical chunk values as distinct occurrences. -/
def DelayedIndex (coarse : α → C) (cell : C) (cs : List (Chunk (Block α))) :=
  {i : Fin cs.length // delayedWeight coarse cell cs[i] = 1}

instance (coarse : α → C) (cell : C) (cs : List (Chunk (Block α))) :
    Fintype (DelayedIndex coarse cell cs) :=
  inferInstanceAs (Fintype {i : Fin cs.length // delayedWeight coarse cell cs[i] = 1})

theorem card_delayedIndex (coarse : α → C) (cell : C) (cs : List (Chunk (Block α))) :
    Fintype.card (DelayedIndex coarse cell cs) =
      ((outgoingGaps coarse cell cs).map Gap.delayed).sum := by
  rw [outgoingGaps_delayed_map, ← List.ofFn_getElem_eq_map, List.sum_ofFn]
  unfold DelayedIndex
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  have h := delayedWeight_le_one coarse cell cs[i]
  simp only [Fin.getElem_fin] at h ⊢
  split <;> omega

/-- The canonical finite delayed occurrence family for a collection of actual
cell-specific chunk contexts. -/
abbrev ContextIndex {H : Nat} {q : Gadget} {word : List Key}
    (cells : Finset Key) (contexts : (cell : cells) → ChunkPaymentContext H q word cell.val) :=
  Σ cell : cells, DelayedIndex q.coarse cell.val (contexts cell).chunks

/-- Actual contexts construct all delayed event records and their joint source
occurrence injection, including different cyclic origins for different cells. -/
theorem family_of_contexts {H : Nat} {q : Gadget} {word : List Key}
    (hq : Valid H q) (initial : Key → Bool) (leaves : OnLeaves H word)
    (normal : Normalized initial H word) (cells : Finset Key)
    (contexts : (cell : cells) → ChunkPaymentContext H q word cell.val) :
    Nonempty (IndexedDelayedFamily H q word (ContextIndex cells contexts)) := by
  apply projected_delayed_family_by_cell_exists hq initial leaves normal cells
    (fun cell => DelayedIndex q.coarse cell.val (contexts cell).chunks)
    (fun cell i => (contexts cell).delayedGap i.val i.property)
  · intro cell i
    exact (contexts cell).delayedGap_source_coarse i.val i.property
  · intro cell i j heq
    apply Subtype.ext
    apply (contexts cell).source_ordinal_injective
    simpa only [ChunkPaymentContext.delayedGap_pre_length] using heq

/-- The finite family cardinality is the literal delayed-gap sum over all cells. -/
theorem card_contextIndex {H : Nat} {q : Gadget} {word : List Key}
    (cells : Finset Key) (contexts : (cell : cells) → ChunkPaymentContext H q word cell.val) :
    Fintype.card (ContextIndex cells contexts) =
      ∑ cell : cells,
        ((outgoingGaps q.coarse cell.val (contexts cell).chunks).map Gap.delayed).sum := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro cell _
  exact card_delayedIndex q.coarse cell.val (contexts cell).chunks

/-- Joint entry and delayed counts are paid by actual events in the global word. -/
theorem entries_contexts_bound {H : Nat} {q : Gadget} {word : List Key}
    {E : Type*} [Fintype E] (qs : Finset Gadget) (hqmem : q ∈ qs)
    (hq : Valid H q) (initial : Key → Bool) (leaves : OnLeaves H word)
    (normal : Normalized initial H word) (entries : IndexedEntryFamily H q word E)
    (cells : Finset Key) (contexts : (cell : cells) → ChunkPaymentContext H q word cell.val) :
    Fintype.card E + ∑ cell : cells,
      ((outgoingGaps q.coarse cell.val (contexts cell).chunks).map Gap.delayed).sum ≤
        eventSum H qs [] word := by
  obtain ⟨delays⟩ := family_of_contexts hq initial leaves normal cells contexts
  rw [← card_contextIndex]
  exact indexed_families_card_le_eventSum qs hqmem leaves entries delays

/-- For arbitrary actual chunk layouts of all active cells, every counted entry
and delayed charge is an event in the literal four-copy global query word. -/
theorem entries_layouts_bound {H : Nat} {q : Gadget} {xs : List Key}
    {E : Type*} [Fintype E] (qs : Finset Gadget) (hqmem : q ∈ qs)
    (hq : Valid H q) (initial : Key → Bool) (leaves : OnLeaves H xs)
    (normal : Normalized initial H (xs ++ (xs ++ (xs ++ xs))))
    (layout : CyclicLayout q.coarse (xs.filterMap (gadgetProjection H q)))
    (layouts : (cell : activeCells q.coarse (layout.first :: layout.rest)) →
      CycleLayout (selected q.coarse cell.val) (layout.first :: layout.rest))
    (entries : IndexedEntryFamily H q (xs ++ (xs ++ (xs ++ xs))) E) :
    Fintype.card E + ∑ cell : activeCells q.coarse (layout.first :: layout.rest),
      ((outgoingGaps q.coarse cell.val (layouts cell).chunks).map Gap.delayed).sum ≤
        eventSum H qs [] (xs ++ (xs ++ (xs ++ xs))) := by
  let contexts := fun cell : activeCells q.coarse (layout.first :: layout.rest) =>
    chunkContext_of_layout hq initial leaves normal layout (layouts cell)
  have leaves4 : OnLeaves H (xs ++ (xs ++ (xs ++ xs))) := by
    intro x hx
    exact leaves x (by simpa using hx)
  exact entries_contexts_bound qs hqmem hq initial leaves4 normal entries
    (activeCells q.coarse (layout.first :: layout.rest)) contexts

end TangoSquared.DelayedPayments
