import TangoSquared.GapSourceData
import TangoSquared.GapInheritance
import TangoSquared.PaymentFamilies

/-!
# Actual delayed payments from indexed cyclic chunks

Each context contains literal words and their structural inheritance from the
normalized projected word. A delayed side bit constructs an actual projected
record, with the source occurrence retained exactly.
-/

namespace TangoSquared

open Primary CyclicRuns GapChunks PeriodicChunks GapChronology GapSourceData
  CyclicGapAccounting GapInheritance

structure ChunkPaymentContext (H : Nat) (q : Gadget) (word : List Key) (cell : Key) where
  chunks : List (Chunk (Block Key))
  before : List Key
  after : List Key
  embedding : word.filterMap (gadgetProjection H q) =
    before ++ (chunkQueries (chunks ++ chunks)).flatten ++ after
  source_selected : ∀ c ∈ chunks, selected q.coarse cell c.source = true
  middle_unselected : ∀ c ∈ chunks, ∀ b ∈ c.middle, selected q.coarse cell b = false
  homogeneous : ∀ b ∈ (((chunks ++ chunks).map Chunk.word).flatten), b.Homogeneous q.coarse
  adjacent : AdjacentDistinct q.coarse (((chunks ++ chunks).map Chunk.word).flatten)
  returns : ReturnWord q.coarse (chunkQueries (chunks ++ chunks)).flatten

namespace ChunkPaymentContext

variable {H : Nat} {q : Gadget} {word : List Key} {cell : Key}

noncomputable def micro (ctx : ChunkPaymentContext H q word cell) (i : Fin ctx.chunks.length) :
    LastMicro ctx.chunks[i].source :=
  Classical.choice (lastMicro_exists _ (by
    have h := ctx.source_selected ctx.chunks[i] (List.getElem_mem _)
    simp only [selected, decide_eq_true_eq] at h
    exact h.2))

def next (ctx : ChunkPaymentContext H q word cell) (i : Fin ctx.chunks.length) : Block Key :=
  ((ctx.chunks ++ ctx.chunks)[nextIndex ctx.chunks i]).source

def delayedWeight (ctx : ChunkPaymentContext H q word cell) (i : Fin ctx.chunks.length) : Nat :=
  (outgoingGap q.coarse cell ctx.chunks[i] (ctx.next i)).delayed

theorem source_cell (ctx : ChunkPaymentContext H q word cell) (i : Fin ctx.chunks.length) :
    q.coarse ctx.chunks[i].source.first = cell := by
  have h := ctx.source_selected ctx.chunks[i] (List.getElem_mem _)
  simp only [selected, decide_eq_true_eq] at h
  exact h.1

theorem next_cell (ctx : ChunkPaymentContext H q word cell) (i : Fin ctx.chunks.length) :
    q.coarse (ctx.next i).first = cell := by
  have hm := List.getElem_mem (nextIndex ctx.chunks i).isLt
  obtain hm | hm := List.mem_append.mp hm
  · have h := ctx.source_selected _ hm
    simp only [selected, decide_eq_true_eq] at h
    exact h.1
  · have h := ctx.source_selected _ hm
    simp only [selected, decide_eq_true_eq] at h
    exact h.1

/-- Normalized returns retain the last fine label throughout this literal gap. -/
theorem retained (ctx : ChunkPaymentContext H q word cell) (i : Fin ctx.chunks.length) :
    ∀ z ∈ (ctx.chunks[i].middle.map Block.word).flatten,
      q.coarse z = cell → z = (ctx.micro i).next := by
  let a := ctx.chunks[i].source
  let b := ctx.next i
  let mid := ctx.chunks[i].middle
  let pre := (((ctx.chunks.take i.val).map Chunk.word).flatten)
  let post := ((ctx.chunks ++ ctx.chunks)[nextIndex ctx.chunks i]).middle ++
    ((((ctx.chunks ++ ctx.chunks).drop (i.val + 2)).map Chunk.word).flatten)
  have hs : (((ctx.chunks ++ ctx.chunks).map Chunk.word).flatten) =
      pre ++ (a :: (mid ++ [b])) ++ post := doubled_gap_blocks_split ctx.chunks i
  have hh : ∀ c ∈ a :: (mid ++ [b]), c.Homogeneous q.coarse := by
    intro c hc
    apply ctx.homogeneous c
    rw [hs]
    simp only [List.mem_append]
    exact Or.inl (Or.inr hc)
  have ha : AdjacentDistinct q.coarse (a :: (mid ++ [b])) := by
    apply adjacent_infix q.coarse pre _ post
    rw [← hs]
    exact ctx.adjacent
  have ht : ∀ c ∈ mid, q.coarse c.first = cell → c.micro = [] := by
    intro c hc hcc
    have hf := ctx.middle_unselected _ (List.getElem_mem _) c hc
    simp only [selected, decide_eq_false_iff_not, not_and, not_not] at hf
    exact hf hcc
  have hr : ReturnWord q.coarse ((a :: (mid ++ [b])).map Block.word).flatten := by
    apply returnWord_blocks_infix q.coarse pre _ post
    rw [← hs, ← chunkQueries_flatten]
    exact ctx.returns
  obtain ⟨_, hkeep⟩ := ChunkRetention.retained_between_runs q.coarse cell a b mid
    (ctx.source_cell i) (ctx.next_cell i) hh ha ht hr
  intro z hz hzc
  have hm : z ∈ cellWord q.coarse (mid.map Block.word).flatten cell := by
    apply List.mem_filter.mpr
    exact ⟨hz, by simpa using hzc⟩
  exact (hkeep z hm).trans (ctx.micro i).final_label

/-- Source run homogeneity is inherited at the same actual occurrence. -/
theorem source_homogeneous (ctx : ChunkPaymentContext H q word cell) (i : Fin ctx.chunks.length) :
    ctx.chunks[i].source.Homogeneous q.coarse := by
  apply ctx.homogeneous
  apply List.mem_flatten.mpr
  refine ⟨ctx.chunks[i].word, ?_, ?_⟩
  · apply List.mem_map.mpr
    exact ⟨ctx.chunks[i], List.mem_append.mpr (Or.inl (List.getElem_mem _)), rfl⟩
  · simp [Chunk.word]

/-- A selected delayed side bit becomes a literal projected source/trigger gap. -/
noncomputable def delayedGap (ctx : ChunkPaymentContext H q word cell)
    (i : Fin ctx.chunks.length) (hi : ctx.delayedWeight i = 1) : ProjectedDelayedGap H q word := by
  let m := ctx.micro i
  let pre := ctx.before ++ (chunkQueries (ctx.chunks.take i.val)).flatten ++ m.before
  let gap := m.tail ++ (ctx.chunks[i].middle.map Block.word).flatten
  let post := (ctx.next i).word ++
    (((ctx.chunks ++ ctx.chunks)[nextIndex ctx.chunks i]).middle.map Block.word).flatten ++
    (chunkQueries ((ctx.chunks ++ ctx.chunks).drop (i.val + 2))).flatten ++ ctx.after
  have hs := doubled_gap_split ctx.chunks i
  refine ⟨pre, m.source, m.next, gap, post, ?_, ?_, m.change, ?_, ?_⟩
  · rw [ctx.embedding, hs, m.split]
    simp only [pre, gap, post, next, List.append_assoc, List.cons_append]
  · exact (ctx.source_homogeneous i m.source m.source_mem).trans
      (ctx.source_homogeneous i m.next m.next_mem).symm
  · intro z hz hzc
    rcases List.mem_append.mp hz with hz | hz
    · exact m.constant z hz
    · apply ctx.retained i z hz
      exact hzc.trans ((ctx.source_homogeneous i m.source m.source_mem).trans (ctx.source_cell i))
  · obtain ⟨z, hz, hp⟩ := delayed_hit q.coarse (fun _ _ h => take_mono_lex h _) cell
      ctx.chunks[i] (ctx.next i) m (ctx.source_homogeneous i) (ctx.source_cell i) hi
    exact ⟨z, List.mem_append.mpr (Or.inr hz), hp⟩

@[simp] theorem delayedGap_source_coarse (ctx : ChunkPaymentContext H q word cell)
    (i : Fin ctx.chunks.length) (hi : ctx.delayedWeight i = 1) :
    q.coarse (ctx.delayedGap i hi).source = cell :=
  (ctx.source_homogeneous i (ctx.micro i).source (ctx.micro i).source_mem).trans (ctx.source_cell i)

@[simp] theorem delayedGap_pre_length (ctx : ChunkPaymentContext H q word cell)
    (i : Fin ctx.chunks.length) (hi : ctx.delayedWeight i = 1) :
    (ctx.delayedGap i hi).pre.length = ctx.before.length +
      (chunkQueries (ctx.chunks.take i.val)).flatten.length + (ctx.micro i).before.length := by
  simp only [delayedGap, List.length_append]

theorem source_ordinal_injective (ctx : ChunkPaymentContext H q word cell) :
    Function.Injective (fun i : Fin ctx.chunks.length => ctx.before.length +
      (chunkQueries (ctx.chunks.take i.val)).flatten.length + (ctx.micro i).before.length) := by
  intro i j h
  apply GapSourceData.source_ordinal_injective ctx.chunks ctx.micro
  dsimp only at h ⊢
  omega

end ChunkPaymentContext

/-- The actual normalized owner/fine projection has literal same-cell returns. -/
theorem gadgetProjection_returnWord {H : Nat} {q : Gadget} {word : List Key}
    (hq : Witnesses.Valid H q) (initial : Key → Bool) (leaves : OnLeaves H word)
    (normal : NormalizedWords.Normalized initial H word) :
    ReturnWord q.coarse (word.filterMap (gadgetProjection H q)) := by
  intro pre a away b post hw hab hn ha
  have hb := DepthTree.node_bounds _ hq.1
  have hlen := hq.2
  have howner : q.owner.length ≤ q.split.cut + 1 := by omega
  have hw' : (ownerWord q.owner word).map (List.take (min (q.split.hi + 1) H)) =
      pre ++ a :: (away ++ b :: post) := by
    simpa only [gadgetProjection, fineProjection_word] using hw
  exact projected_return initial howner (projection_coarse_depth hq)
    (Nat.min_le_right _ _) leaves normal hw' hab hn ha

/-- Canonical selected-run chunks inherit every needed fact from the actual
normalized four-period query word and its two concrete rotations. -/
def chunkContext_of_layout {H : Nat} {q : Gadget} {xs : List Key} {cell : Key}
    (hq : Witnesses.Valid H q) (initial : Key → Bool) (leaves : OnLeaves H xs)
    (normal : NormalizedWords.Normalized initial H (xs ++ (xs ++ (xs ++ xs))))
    (layout : CyclicLayout q.coarse (xs.filterMap (gadgetProjection H q)))
    (chunks : CycleLayout (selected q.coarse cell) (layout.first :: layout.rest)) :
    ChunkPaymentContext H q (xs ++ (xs ++ (xs ++ xs))) cell := by
  let before := layout.cutBefore ++ (chunks.cutBefore.map Block.word).flatten
  let after := (chunks.cutAfter.map Block.word).flatten ++ layout.suffix
  have embed : (xs ++ (xs ++ (xs ++ xs))).filterMap (gadgetProjection H q) =
      before ++ (chunkQueries (chunks.chunks ++ chunks.chunks)).flatten ++ after := by
    have he := layout_chunk_embedding layout (selected q.coarse cell) chunks
    simp only [List.filterMap_append, doubled_chunk_word, before, after,
      List.append_assoc] at he ⊢
    exact he
  refine ⟨chunks.chunks, before, after, embed, chunks.source_selected,
    chunks.middle_unselected, ?_, ?_, ?_⟩
  · intro b hb
    have hrot : (((chunks.chunks ++ chunks.chunks).map Chunk.word).flatten) =
        (chunks.cutAfter ++ chunks.cutBefore) ++ (chunks.cutAfter ++ chunks.cutBefore) := by
      simp only [List.map_append, List.flatten_append, chunks.rotation]
    rw [hrot] at hb
    have hm : b ∈ chunks.cutBefore ++ chunks.cutAfter := by
      simp only [List.mem_append] at hb ⊢
      tauto
    apply layout.homogeneous b
    rwa [chunks.split]
  · have ha := rotated_double_adjacent q.coarse layout.first layout.rest
      chunks.cutBefore chunks.cutAfter chunks.split layout.boundaries
    simpa only [List.map_append, List.flatten_append, chunks.rotation] using ha
  · apply returnWord_infix q.coarse before _ after
    rw [← embed]
    apply gadgetProjection_returnWord hq initial _ normal
    intro y hy
    exact leaves y (by simpa using hy)

end TangoSquared
