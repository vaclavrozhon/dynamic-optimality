import MultiSplay.IntervalPaymentFamilies
import TangoSquared.DelayedChunkPayments

/-! # Actual chunk contexts for arbitrary interval hierarchies -/

namespace MultiSplay.IntervalLower

open TangoSquared
open TangoSquared.Primary TangoSquared.CyclicRuns TangoSquared.GapChunks TangoSquared.PeriodicChunks
open TangoSquared.GapChronology TangoSquared.GapSourceData TangoSquared.CyclicGapAccounting TangoSquared.GapInheritance

theorem gadgetProjection_returnWord {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {word : List Key}
    (hq : Valid hierarchy q) (initial : Key → Bool) (leaves : OnLeaves H word)
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


def chunkContext_of_layout {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {xs : List Key} {cell : Key}
    (hq : Valid hierarchy q) (initial : Key → Bool) (leaves : OnLeaves H xs)
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


end MultiSplay.IntervalLower
