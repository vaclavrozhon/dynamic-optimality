import TangoSquared.CyclicGapAccounting
import TangoSquared.CyclicEntryAccounting
import TangoSquared.GapInheritance

/-! The actual cell gap entries partition the encoded cyclic run entries. -/

namespace TangoSquared.EntryGapBridge

open CyclicRuns TurnAccounting GapChunks CyclicGapAccounting CyclicEntryAccounting GapInheritance

variable {α C : Type*} [LinearOrder α] [LinearOrder C]

private theorem gapsFrom_sum (coarse : α → C) (cell : C) (f : Gap → Nat)
    (previous : Chunk (Block α)) (cs : List (Chunk (Block α))) :
    ((gapsFrom coarse cell previous cs).map f).sum =
      adjacencyFrom (fun c d => f (outgoingGap coarse cell c d.source)) previous cs := by
  induction cs generalizing previous with
  | nil => rfl
  | cons c cs ih => simp only [gapsFrom, List.map_cons, List.sum_cons, adjacencyFrom, ih]

theorem outgoingGaps_sum (coarse : α → C) (cell : C) (f : Gap → Nat)
    (fallback : Chunk (Block α)) (cs : List (Chunk (Block α))) :
    ((outgoingGaps coarse cell cs).map f).sum =
      cyclicAdjacency (fun c d => f (outgoingGap coarse cell c d.source)) fallback cs := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    simp only [outgoingGaps, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero, cyclicAdjacency, List.getLastD_cons,
      adjacencyFrom, gapsFrom_sum]
    omega

private theorem adjacencyFrom_congr_chain {β : Type*} (f g : β → β → Nat)
    (b : β) (bs : List β) (h : List.IsChain (fun a b => f a b = g a b) (b :: bs)) :
    adjacencyFrom f b bs = adjacencyFrom g b bs := by
  induction bs generalizing b with
  | nil => rfl
  | cons c cs ih =>
    rw [List.isChain_cons_cons] at h
    simp only [adjacencyFrom, h.1, ih c h.2]

private theorem cyclicAdjacency_congr_chain {β : Type*} (f g : β → β → Nat)
    (b : β) (bs : List β) (h : List.IsChain (fun a b => f a b = g a b) ((b :: bs) ++ [b])) :
    cyclicAdjacency f b (b :: bs) = cyclicAdjacency g b (b :: bs) := by
  obtain ⟨hc, _, hw⟩ := List.isChain_append.mp h
  have hwrap : f (bs.getLastD b) b = g (bs.getLastD b) b := by
    exact hw _ (by simp [List.getLast?_cons]) _ (by simp)
  simp only [cyclicAdjacency, List.getLastD_cons, adjacencyFrom, hwrap,
    adjacencyFrom_congr_chain f g b bs hc]

omit [LinearOrder α] [LinearOrder C] in
private theorem chunk_links (coarse : α → C) (closing : Chunk (Block α))
    (cs : List (Chunk (Block α)))
    (h : AdjacentDistinct coarse ((cs.map Chunk.word).flatten ++ [closing.source])) :
    List.IsChain (fun c d => AdjacentDistinct coarse (c.word ++ [d.source])) (cs ++ [closing]) := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    cases cs with
    | nil =>
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at h
      simpa only [List.cons_append, List.nil_append, List.isChain_cons_cons, List.isChain_singleton,
        and_true] using h
    | cons d ds =>
      have ht : AdjacentDistinct coarse (((d :: ds).map Chunk.word).flatten ++ [closing.source]) := by
        apply adjacent_infix coarse c.word _ []
        simpa only [List.map_cons, List.flatten_cons, List.append_nil, List.append_assoc] using h
      have hp : AdjacentDistinct coarse (c.word ++ [d.source]) := by
        apply adjacent_infix coarse [] _ (d.middle ++ (ds.map Chunk.word).flatten ++ [closing.source])
        simpa only [List.map_cons, List.flatten_cons, Chunk.word, List.nil_append,
          List.append_assoc, List.cons_append] using h
      exact List.isChain_cons_cons.mpr ⟨hp, ih ht⟩

omit [LinearOrder α] [LinearOrder C] in
private theorem cyclic_chunk_links (coarse : α → C) (c : Chunk (Block α))
    (cs : List (Chunk (Block α)))
    (h : AdjacentDistinct coarse
      (((c :: cs).map Chunk.word).flatten ++ ((c :: cs).map Chunk.word).flatten)) :
    List.IsChain (fun c d => AdjacentDistinct coarse (c.word ++ [d.source])) ((c :: cs) ++ [c]) := by
  apply chunk_links coarse c (c :: cs)
  apply adjacent_infix coarse [] _ (c.middle ++ (cs.map Chunk.word).flatten)
  simpa only [List.map_cons, List.flatten_cons, Chunk.word, List.nil_append,
    List.append_assoc, List.cons_append] using h

/-- The complete entry charge of one selected coarse cell is the corresponding
part of the original run entry account, with each occurrence preserved. -/
theorem layout_entries (coarse : α → C) (ordered : Monotone coarse) (cell : C)
    (b : Block α) (bs : List (Block α))
    (layout : CycleLayout (selected coarse cell) (b :: bs))
    (homogeneous : ∀ z ∈ b :: bs, z.Homogeneous coarse)
    (boundary : DistinctBoundaries (coarse b.first)
      ((b :: bs).map (Block.coarseSingleton coarse))) :
    ((outgoingGaps coarse cell layout.chunks).map Gap.entry).sum =
      cyclicAdjacency (fun p q => if coarse q.first = cell then entryWeight p q else 0)
        b (b :: bs) := by
  let weight := fun p q : Block α => if coarse q.first = cell then entryWeight p q else 0
  have hz : ∀ y, selected coarse cell y = false → ∀ x, weight x y = 0 := by
    intro y hy x
    by_cases hc : coarse y.first = cell
    · have hm : y.micro = [] := by
        simp only [selected, decide_eq_false_iff_not, not_and, not_not] at hy
        exact hy hc
      simp only [weight, hc, ↓reduceIte, entryWeight_zero x y hm]
    · simp only [weight, hc, ↓reduceIte]
  cases he : layout.chunks with
  | nil => exact False.elim (layout.nonempty he)
  | cons c cs =>
    have hs := CycleLayout.selected_chunk_adjacency layout weight b c hz
    have hhom : ∀ d ∈ c :: cs, ∀ z ∈ d.word, z.Homogeneous coarse := by
      intro d hd z hz
      apply homogeneous z
      have hm : z ∈ (layout.chunks.map Chunk.word).flatten :=
        List.mem_flatten.mpr ⟨d.word, List.mem_map.mpr ⟨d, by simpa [he] using hd, rfl⟩, hz⟩
      rw [layout.rotation] at hm
      rw [layout.split]
      simpa only [List.mem_append, or_comm] using hm
    have hselect : ∀ d ∈ c :: cs, coarse d.source.first = cell ∧ d.source.micro ≠ [] := by
      intro d hd
      exact of_decide_eq_true (layout.source_selected d (by simpa [he] using hd))
    have hd := rotated_double_adjacent coarse b bs layout.cutBefore layout.cutAfter layout.split boundary
    rw [← layout.rotation, he] at hd
    have hlinks := cyclic_chunk_links coarse c cs hd
    have heq : List.IsChain (fun p q =>
        (outgoingGap coarse cell p q.source).entry = weight (Chunk.last p) q.source)
        ((c :: cs) ++ [c]) := by
      apply hlinks.imp_of_mem_imp
      intro p q hp hq hpq
      have hp' : p ∈ c :: cs := by simp only [List.mem_append, List.mem_cons] at hp ⊢; tauto
      have hq' : q ∈ c :: cs := by simp only [List.mem_append, List.mem_cons] at hq ⊢; tauto
      rw [show weight (Chunk.last p) q.source = entryWeight (Chunk.last p) q.source by
        simp only [weight, (hselect q hq').1, ↓reduceIte]]
      have hg := outgoingGap_entry coarse ordered cell p q.source (hselect p hp').1
        (hselect q hq').1 (hselect q hq').2
        (fun z hz => hhom p hp' z (by simp [Chunk.word, hz])) hpq
      simp only [entryWeight, Chunk.last, Chunk.word, List.getLastD_cons] at hg ⊢
      convert hg using 2
      · simp
    rw [he] at hs
    rw [outgoingGaps_sum coarse cell Gap.entry c, cyclicAdjacency_congr_chain _ _ c cs heq]
    exact hs.symm

private theorem exists_next_cyclic {β : Type*} (R : β → β → Prop)
    (b : β) (bs : List β) (chain : List.IsChain R ((b :: bs) ++ [b]))
    (x : β) (hx : x ∈ b :: bs) : ∃ y ∈ b :: bs, R x y := by
  obtain ⟨before, after, he⟩ := List.mem_iff_append.mp hx
  have ht := chain
  rw [he, List.append_assoc] at ht
  have hs := (List.isChain_append.mp ht).2.1
  cases after with
  | nil => exact ⟨b, by simp, hs.rel⟩
  | cons y ys =>
    refine ⟨y, ?_, hs.rel⟩
    rw [he]
    simp

/-- Each selected source has its literal cyclic successor, together with all
actual intervening coarse boundaries. -/
theorem layout_chunk_next (coarse : α → C) (cell : C) (b : Block α) (bs : List (Block α))
    (layout : CycleLayout (selected coarse cell) (b :: bs))
    (boundary : DistinctBoundaries (coarse b.first)
      ((b :: bs).map (Block.coarseSingleton coarse))) :
    ∀ c ∈ layout.chunks, ∃ next ∈ layout.chunks,
      AdjacentDistinct coarse (c.word ++ [next.source]) := by
  intro d hd
  cases he : layout.chunks with
  | nil => simp [he] at hd
  | cons c cs =>
    have hb := rotated_double_adjacent coarse b bs layout.cutBefore layout.cutAfter layout.split boundary
    rw [← layout.rotation, he] at hb
    have hc := cyclic_chunk_links coarse c cs hb
    simpa only [he] using exists_next_cyclic _ c cs hc d (by simpa only [he] using hd)

/-- Every genuine selected-source chunk has a nonempty outside excursion. -/
theorem layout_middle_nonempty (coarse : α → C) (cell : C) (b : Block α) (bs : List (Block α))
    (layout : CycleLayout (selected coarse cell) (b :: bs))
    (boundary : DistinctBoundaries (coarse b.first)
      ((b :: bs).map (Block.coarseSingleton coarse))) :
    ∀ c ∈ layout.chunks, c.middle ≠ [] := by
  intro c hc
  obtain ⟨next, hn, ha⟩ := layout_chunk_next coarse cell b bs layout boundary c hc
  have hs := of_decide_eq_true (layout.source_selected c hc)
  have ht := of_decide_eq_true (layout.source_selected next hn)
  exact (outgoing_middle_last coarse cell c next.source hs.1 ht.1 ha).1

end TangoSquared.EntryGapBridge
