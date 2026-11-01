import MultiSplay.IntervalChunkPayments
import TangoSquared.EntryPayments
import TangoSquared.DelayedPayments

/-!
# Entry and delayed payment families for arbitrary interval hierarchies

Every payment still uses the original actual query index, source key, and
physical witness record. No injection or aggregate cost premise is supplied.
-/

namespace MultiSplay.IntervalLower.EntryPayments

open TangoSquared MultiSplay.IntervalLower
open TangoSquared.Primary TangoSquared.Witnesses TangoSquared.NormalizedWords TangoSquared.CyclicRuns TangoSquared.RunOccurrences
open TangoSquared.CyclicEntryAccounting TangoSquared.ChunkOccurrences TangoSquared.TurnAccounting TangoSquared.EntryPayments

theorem entry_at_occurrence {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {word : List Key}
    (hq : Valid hierarchy q) (initial : Key → Bool) (leaves : OnLeaves H word)
    (normal : Normalized initial H word)
    (b : Block Key) (bs : List (Block Key)) (i : Fin (b :: bs).length)
    (outerBefore outerAfter : List Key)
    (embed : word.filterMap (gadgetProjection H q) = outerBefore ++
      (((b :: bs).map Block.word).flatten ++ ((b :: bs).map Block.word).flatten) ++ outerAfter)
    (k : Nat) (x : Key) (after : List Key)
    (split : (b :: bs)[i].word = List.replicate (k + 1) (b :: bs)[i].first ++ x :: after)
    (different : (b :: bs)[i].first ≠ x)
    (same : q.coarse (b :: bs)[i].first = q.coarse x)
    (other : q.coarse (predecessor b (b :: bs) i.val).last ≠ q.coarse x)
    (reversal : ((predecessor b (b :: bs) i.val).last < x ∧ x < (b :: bs)[i].first) ∨
      ((b :: bs)[i].first < x ∧ x < (predecessor b (b :: bs) i.val).last)) :
    ∃ (time : Fin word.length) (source : Key),
      Nonempty (EntryEvent (queryHistory [] word time) word[time] q source) ∧
      ((word.take time.val).filterMap (gadgetProjection H q)).length =
        outerBefore.length + ((b :: bs).map Block.word).flatten.length +
          offset ((b :: bs).map Block.word) i.val + (k + 1) := by
  obtain ⟨pre, post, hsplit, hlen⟩ := second_cycle_run_split b bs i
  have hword : word.filterMap (gadgetProjection H q) =
      (outerBefore ++ pre) ++ (predecessor b (b :: bs) i.val).last ::
        (List.replicate k (b :: bs)[i].first ++ (b :: bs)[i].first ::
          x :: (after ++ post ++ outerAfter)) := by
    rw [embed, hsplit, split, List.replicate_succ']
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨time, source, _, _, record, _, htime⟩ := indexed_projected_entry hq initial
    leaves normal hword same other different reversal (by simp)
  refine ⟨time, source, ⟨record⟩, ?_⟩
  simp only [List.length_append, List.length_replicate] at htime
  omega


theorem family_of_doubled_runs {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {word : List Key}
    (hq : Valid hierarchy q) (initial : Key → Bool) (leaves : OnLeaves H word)
    (normal : Normalized initial H word)
    (b : Block Key) (bs : List (Block Key))
    (homogeneous : ∀ c ∈ b :: bs, c.Homogeneous q.coarse)
    (boundary : DistinctBoundaries (q.coarse b.first)
      ((b :: bs).map (Block.coarseSingleton q.coarse)))
    (outerBefore outerAfter : List Key)
    (embed : word.filterMap (gadgetProjection H q) = outerBefore ++
      (((b :: bs).map Block.word).flatten ++ ((b :: bs).map Block.word).flatten) ++ outerAfter) :
    Nonempty (IndexedEntryFamily H q word (EntryIndex b bs)) := by
  classical
  have hother (i : Fin (b :: bs).length) :
      q.coarse (predecessor b (b :: bs) i.val).last ≠ q.coarse (b :: bs)[i].first := by
    rw [Block.homogeneous_last q.coarse _ (homogeneous _ (predecessor_mem b bs i.val))]
    exact predecessor_other q.coarse b bs boundary i
  have hgeometry (i : EntryIndex b bs) := entry_geometry q.coarse
    (fun _ _ h => take_mono_lex h _) (predecessor b (b :: bs) i.val.val) (b :: bs)[i.val]
    (homogeneous _ (List.getElem_mem i.val.isLt)) (hother i.val) i.property
  choose k x after hsplit hdiff hcoarse hreversal using hgeometry
  have hrecords (i : EntryIndex b bs) := entry_at_occurrence hq initial leaves normal b bs i.val
    outerBefore outerAfter embed (k i) (x i) (after i) (hsplit i) (hdiff i) (hcoarse i).symm
    (by rw [hcoarse i]; exact hother i.val) (hreversal i)
  choose time source hrecord hordinal using hrecords
  refine ⟨{
    time := time
    source := source
    record := fun i => Classical.choice (hrecord i)
    ordinal := fun i => outerBefore.length + ((b :: bs).map Block.word).flatten.length +
      offset ((b :: bs).map Block.word) i.val.val + (k i + 1)
    ordinal_eq := hordinal
    injective := ?_ }⟩
  intro i j hij
  apply Subtype.ext
  apply Fin.ext
  let words := (b :: bs).map Block.word
  let index (v : EntryIndex b bs) : Fin words.length := ⟨v.val.val, by
    simpa only [words, List.length_map] using v.val.isLt⟩
  have valid (v : EntryIndex b bs) : k v + 1 < words[index v].length := by
    have hl := congrArg List.length (hsplit v)
    simp only [List.length_append, List.length_replicate, List.length_cons] at hl
    have hw : words[index v] = (b :: bs)[v.val].word := by
      simp only [words, index, Fin.getElem_fin, List.getElem_map]
    rw [hw]
    omega
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := occurrence_time_lt words (index i) (index j) (k i + 1) (k j + 1) (valid i) hlt
    dsimp only [index, words] at h
    dsimp only at hij
    omega
  · have h := occurrence_time_lt words (index j) (index i) (k j + 1) (k i + 1) (valid j) hgt
    dsimp only [index, words] at h
    dsimp only at hij
    omega


theorem layout_family {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {xs : List Key}
    (hq : Valid hierarchy q) (initial : Key → Bool) (leaves : OnLeaves H xs)
    (normal : Normalized initial H (xs ++ (xs ++ (xs ++ xs))))
    (layout : CyclicLayout q.coarse (xs.filterMap (gadgetProjection H q))) :
    Nonempty (IndexedEntryFamily H q (xs ++ (xs ++ (xs ++ xs)))
      (EntryIndex layout.first layout.rest)) := by
  have hl : OnLeaves H (xs ++ (xs ++ (xs ++ xs))) := by
    intro x hx
    exact leaves x (by simpa only [List.mem_append, or_self] using hx)
  apply family_of_doubled_runs hq initial hl normal layout.first layout.rest
    layout.homogeneous layout.boundaries layout.cutBefore
    (layout.suffix ++ xs.filterMap (gadgetProjection H q))
  simp only [List.filterMap_append, layout.rotation, layout.split, List.append_assoc]


end MultiSplay.IntervalLower.EntryPayments

namespace MultiSplay.IntervalLower.DelayedPayments

open TangoSquared MultiSplay.IntervalLower
open TangoSquared.Primary TangoSquared.Witnesses TangoSquared.NormalizedWords TangoSquared.CyclicRuns TangoSquared.GapChunks
open TangoSquared.CyclicGapAccounting TangoSquared.TurnAccounting TangoSquared.DelayedPayments

theorem family_of_contexts {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {word : List Key}
    (hq : Valid hierarchy q) (initial : Key → Bool) (leaves : OnLeaves H word)
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


theorem entries_contexts_bound {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {word : List Key}
    {E : Type*} [Fintype E] (qs : Finset Gadget) (hqmem : q ∈ qs)
    (hq : Valid hierarchy q) (initial : Key → Bool) (leaves : OnLeaves H word)
    (normal : Normalized initial H word) (entries : IndexedEntryFamily H q word E)
    (cells : Finset Key) (contexts : (cell : cells) → ChunkPaymentContext H q word cell.val) :
    Fintype.card E + ∑ cell : cells,
      ((outgoingGaps q.coarse cell.val (contexts cell).chunks).map Gap.delayed).sum ≤
        eventSum H qs [] word := by
  obtain ⟨delays⟩ := family_of_contexts hq initial leaves normal cells contexts
  rw [← card_contextIndex]
  exact indexed_families_card_le_eventSum qs hqmem leaves entries delays


theorem entries_layouts_bound {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {xs : List Key}
    {E : Type*} [Fintype E] (qs : Finset Gadget) (hqmem : q ∈ qs)
    (hq : Valid hierarchy q) (initial : Key → Bool) (leaves : OnLeaves H xs)
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


end MultiSplay.IntervalLower.DelayedPayments
