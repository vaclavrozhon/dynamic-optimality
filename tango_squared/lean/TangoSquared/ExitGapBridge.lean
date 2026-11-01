import TangoSquared.EntryGapBridge
import TangoSquared.SourceExit
import TangoSquared.DelayedPayments

/-!
# Outgoing run turns preserved by selected-source chunks

Each nontrivial source run contributes its actual immediate exit direction.
Grouping all later unselected runs into its chunk preserves this source-edge
weight exactly, including after a cyclic change of origin.
-/

namespace TangoSquared.ExitGapBridge

open CyclicRuns TurnAccounting GapChunks CyclicGapAccounting CyclicEntryAccounting

variable {β : Type*}

def outgoingFrom (weight : β → β → Nat) (closing : β) : List β → Nat
  | [] => 0
  | b :: bs => weight b (bs.headD closing) + outgoingFrom weight closing bs

theorem outgoingFrom_eq (weight : β → β → Nat) (closing b : β) (bs : List β) :
    outgoingFrom weight closing (b :: bs) =
      adjacencyFrom weight b bs + weight (bs.getLastD b) closing := by
  induction bs generalizing b with
  | nil => simp [outgoingFrom, adjacencyFrom]
  | cons c cs ih =>
    simp only [outgoingFrom, List.headD_cons, List.getLastD_cons, adjacencyFrom]
    have h := ih c
    simp only [outgoingFrom] at h
    omega

theorem outgoingFrom_cyclic (weight : β → β → Nat) (b : β) (bs : List β) :
    outgoingFrom weight b (b :: bs) = cyclicAdjacency weight b (b :: bs) := by
  rw [outgoingFrom_eq]
  simp only [cyclicAdjacency, List.getLastD_cons, adjacencyFrom]
  omega

theorem outgoingFrom_append (weight : β → β → Nat) (closing : β) (xs ys : List β) :
    outgoingFrom weight closing (xs ++ ys) =
      outgoingFrom weight (ys.headD closing) xs + outgoingFrom weight closing ys := by
  induction xs with
  | nil => simp [outgoingFrom]
  | cons b bs ih =>
    simp only [List.cons_append, outgoingFrom, ih]
    have hh : (bs ++ ys).headD closing = bs.headD (ys.headD closing) := by cases bs <;> rfl
    rw [hh]
    omega

theorem outgoingFrom_congr (f g : β → β → Nat) (closing : β) (xs : List β)
    (eq : ∀ x ∈ xs, ∀ y, f x y = g x y) :
    outgoingFrom f closing xs = outgoingFrom g closing xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [outgoingFrom, eq x (by simp)]
    rw [ih (fun z hz => eq z (by simp [hz]))]

theorem outgoingFrom_zero (weight : β → β → Nat) (closing : β) (xs : List β)
    (zero : ∀ x ∈ xs, ∀ y, weight x y = 0) : outgoingFrom weight closing xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [outgoingFrom, zero x (by simp), zero_add]; exact ih (fun z hz => zero z (by simp [hz]))

theorem outgoingFrom_chunks (weight : β → β → Nat) (closing : β) (cs : List (Chunk β))
    (nonempty : ∀ c ∈ cs, c.middle ≠ [])
    (zero : ∀ c ∈ cs, ∀ x ∈ c.middle, ∀ y, weight x y = 0) :
    outgoingFrom weight closing ((cs.map Chunk.word).flatten) =
      (cs.map (fun c => weight c.source (c.middle.headD c.source))).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.flatten_cons, List.sum_cons]
    rw [outgoingFrom_append]
    have hm := nonempty c (by simp)
    have hzero := zero c (by simp)
    have hh (fallback : β) : c.middle.headD fallback = c.middle.headD c.source := by
      cases he : c.middle with
      | nil => exact (hm he).elim
      | cons a as => rfl
    simp only [Chunk.word, outgoingFrom, hh,
      outgoingFrom_zero weight _ c.middle hzero, Nat.add_zero]
    rw [ih (fun d hd => nonempty d (by simp [hd])) (fun d hd => zero d (by simp [hd]))]

theorem outgoingFrom_sum {ι : Type*} (s : Finset ι) (weight : ι → β → β → Nat)
    (closing : β) (xs : List β) :
    outgoingFrom (fun x y => ∑ i ∈ s, weight i x y) closing xs =
      ∑ i ∈ s, outgoingFrom (weight i) closing xs := by
  induction xs with
  | nil => simp [outgoingFrom]
  | cons x xs ih => simp only [outgoingFrom, ih, Finset.sum_add_distrib]

theorem outgoingFrom_partition {C : Type*} [DecidableEq C]
    (cell : β → C) (cells : Finset C) (weight : β → β → Nat)
    (closing : β) (xs : List β) (cover : ∀ x ∈ xs, cell x ∈ cells) :
    (∑ c ∈ cells, outgoingFrom (fun x y => if cell x = c then weight x y else 0)
      closing xs) = outgoingFrom weight closing xs := by
  rw [← outgoingFrom_sum]
  apply outgoingFrom_congr
  intro x hx y
  simp [cover x hx]

section Ordered

variable {α C : Type*} [LinearOrder α] [LinearOrder C]

def exitWeight (previous current : Block α) : Nat :=
  Run.exitTurn ⟨previous.micro, decide (previous.last < current.first)⟩

theorem exitWeight_zero (previous current : Block α) (empty : previous.micro = []) :
    exitWeight previous current = 0 := by simp [exitWeight, Run.exitTurn, empty]

theorem outgoingFrom_exitWeight (closing : Block α) (blocks : List (Block α)) :
    outgoingFrom exitWeight closing blocks = exitTurns (encode closing.first blocks) := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
    simp only [outgoingFrom, exitTurns, encode, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    cases bs <;> rfl

/-- A cell's selected-source chunk sum is its exact share of original exits. -/
theorem layout_source_exits (coarse : α → C) (cell : C) (b : Block α) (bs : List (Block α))
    (layout : CycleLayout (selected coarse cell) (b :: bs))
    (middle_nonempty : ∀ c ∈ layout.chunks, c.middle ≠ []) :
    (layout.chunks.map (fun c => exitWeight c.source (c.middle.headD c.source))).sum =
      outgoingFrom (fun p q => if coarse p.first = cell then exitWeight p q else 0) b (b :: bs) := by
  let weight := fun p q : Block α => if coarse p.first = cell then exitWeight p q else 0
  have hz : ∀ c ∈ layout.chunks, ∀ x ∈ c.middle, ∀ y, weight x y = 0 := by
    intro c hc x hx y
    have hu := layout.middle_unselected c hc x hx
    by_cases he : coarse x.first = cell
    · have hm : x.micro = [] := by
        simp only [selected, decide_eq_false_iff_not, not_and, not_not] at hu
        exact hu he
      simp only [weight, he, ↓reduceIte, exitWeight_zero x y hm]
    · simp only [weight, he, ↓reduceIte]
  have hrotate : cyclicAdjacency weight b (b :: bs) =
      cyclicAdjacency weight b ((layout.chunks.map Chunk.word).flatten) := by
    calc
      _ = cyclicAdjacency weight b (layout.cutBefore ++ layout.cutAfter) :=
        congrArg (cyclicAdjacency weight b) layout.split
      _ = cyclicAdjacency weight b (layout.cutAfter ++ layout.cutBefore) :=
        cyclicAdjacency_swap_append weight b _ _
      _ = _ := congrArg (cyclicAdjacency weight b) layout.rotation.symm
  have heq : (layout.chunks.map (fun c => weight c.source (c.middle.headD c.source))).sum =
      (layout.chunks.map (fun c => exitWeight c.source (c.middle.headD c.source))).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro c hc
    have hh := (of_decide_eq_true (layout.source_selected c hc)).1
    simp only [weight, hh, ↓reduceIte]
  rw [outgoingFrom_cyclic, hrotate]
  cases he : layout.chunks with
  | nil => exact (layout.nonempty he).elim
  | cons c cs =>
    have hg := outgoingFrom_chunks weight c.source (c :: cs)
      (by simpa only [he] using middle_nonempty) (by simpa only [he] using hz)
    have hcyc : cyclicAdjacency weight b (((c :: cs).map Chunk.word).flatten) =
        outgoingFrom weight c.source (((c :: cs).map Chunk.word).flatten) := by
      rw [cyclicAdjacency_fallback weight b c.source]
      exact (outgoingFrom_cyclic weight c.source (c.middle ++ (cs.map Chunk.word).flatten)).symm
    rw [hcyc, hg]
    simpa only [he] using heq.symm

/-- Cells with no nontrivial selected source contribute no outgoing turns. -/
theorem no_selected_exit_zero (coarse : α → C) (cell : C) (closing : Block α)
    (blocks : List (Block α))
    (empty : (blocks.filter (selected coarse cell)).length = 0) :
    outgoingFrom (fun p q => if coarse p.first = cell then exitWeight p q else 0)
      closing blocks = 0 := by
  apply outgoingFrom_zero
  intro p hp q
  by_cases hc : coarse p.first = cell
  · have hm : p.micro = [] := by
      by_contra hn
      have hs : p ∈ blocks.filter (selected coarse cell) := by
        apply List.mem_filter.mpr
        exact ⟨hp, by simp [selected, hc, hn]⟩
      rw [List.length_eq_zero_iff.mp empty] at hs
      simp at hs
    simp only [hc, ↓reduceIte, exitWeight_zero p q hm]
  · simp only [hc, ↓reduceIte]

/-- Only cells containing nontrivial runs contribute to the exact exit sum. -/
theorem exitTurns_eq_active_sum (coarse : α → C) (b : Block α) (bs : List (Block α)) :
    exitTurns (encode b.first (b :: bs)) =
      ∑ cell : (cells coarse (b :: bs)).filter
        (fun cell => ((b :: bs).filter (selected coarse cell)).length > 0),
        outgoingFrom (fun p q => if coarse p.first = cell.val then exitWeight p q else 0)
          b (b :: bs) := by
  classical
  rw [Finset.sum_coe_sort ((cells coarse (b :: bs)).filter
    (fun cell => ((b :: bs).filter (selected coarse cell)).length > 0))
    (fun cell => outgoingFrom (fun p q => if coarse p.first = cell then exitWeight p q else 0)
      b (b :: bs))]
  have hfull := outgoingFrom_partition (fun p : Block α => coarse p.first)
    (cells coarse (b :: bs)) exitWeight b (b :: bs) (by
      intro p hp
      simp only [cells, List.mem_toFinset, List.mem_map]
      exact ⟨p, hp, rfl⟩)
  rw [outgoingFrom_exitWeight] at hfull
  rw [← hfull]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro cell hcell hnot
  have hn : ¬ ((b :: bs).filter (selected coarse cell)).length > 0 := by
    intro h
    exact hnot (Finset.mem_filter.mpr ⟨hcell, h⟩)
  exact no_selected_exit_zero coarse cell b (b :: bs) (by omega)

/-- The exact exit account of one cell is paid by delayed charges on its actual
outgoing gaps. Each first outside run witnesses the charge. -/
theorem layout_exits_le_delayed (coarse : α → C) (ordered : Monotone coarse) (cell : C)
    (b : Block α) (bs : List (Block α))
    (layout : CycleLayout (selected coarse cell) (b :: bs))
    (homogeneous : ∀ z ∈ b :: bs, z.Homogeneous coarse)
    (boundary : DistinctBoundaries (coarse b.first)
      ((b :: bs).map (Block.coarseSingleton coarse))) :
    outgoingFrom (fun p q => if coarse p.first = cell then exitWeight p q else 0)
        b (b :: bs) ≤
      ((outgoingGaps coarse cell layout.chunks).map Gap.delayed).sum := by
  rw [← layout_source_exits coarse cell b bs layout
    (EntryGapBridge.layout_middle_nonempty coarse cell b bs layout boundary)]
  rw [DelayedPayments.outgoingGaps_delayed_map]
  have hpoint : ∀ c ∈ layout.chunks,
      exitWeight c.source (c.middle.headD c.source) ≤ DelayedPayments.delayedWeight coarse cell c := by
    intro c hc
    obtain ⟨next, hn, ha⟩ := EntryGapBridge.layout_chunk_next coarse cell b bs layout boundary c hc
    have hs := of_decide_eq_true (layout.source_selected c hc)
    have ht := of_decide_eq_true (layout.source_selected next hn)
    have hmem : c.source ∈ b :: bs := by
      have h : c.source ∈ (layout.chunks.map Chunk.word).flatten :=
        List.mem_flatten.mpr ⟨c.word, List.mem_map.mpr ⟨c, hc, rfl⟩, by simp [Chunk.word]⟩
      rw [layout.rotation] at h
      rw [layout.split]
      simpa only [List.mem_append, or_comm] using h
    have hp := SourceExit.sourceExit_le_delayed coarse ordered cell c next.source hs.1 ht.1
      (homogeneous c.source hmem) ha
    exact hp
  have hsum : ∀ cs : List (Chunk (Block α)),
      (∀ c ∈ cs, exitWeight c.source (c.middle.headD c.source) ≤
        DelayedPayments.delayedWeight coarse cell c) →
      (cs.map (fun c => exitWeight c.source (c.middle.headD c.source))).sum ≤
        (cs.map (DelayedPayments.delayedWeight coarse cell)).sum := by
    intro cs hh
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (hh c (by simp)) (ih (fun z hz => hh z (by simp [hz])))
  exact hsum layout.chunks hpoint

/-- All concrete exit turns are covered by the delayed gap family, partitioned
by the actual active coarse cells. -/
theorem exitTurns_le_delayed (coarse : α → C) (ordered : Monotone coarse)
    (b : Block α) (bs : List (Block α))
    (homogeneous : ∀ z ∈ b :: bs, z.Homogeneous coarse)
    (boundary : DistinctBoundaries (coarse b.first)
      ((b :: bs).map (Block.coarseSingleton coarse)))
    (layouts : (cell : DelayedPayments.activeCells coarse (b :: bs)) →
      CycleLayout (selected coarse cell.val) (b :: bs)) :
    exitTurns (encode b.first (b :: bs)) ≤
      ∑ cell : DelayedPayments.activeCells coarse (b :: bs),
        ((outgoingGaps coarse cell.val (layouts cell).chunks).map Gap.delayed).sum := by
  rw [exitTurns_eq_active_sum coarse b bs]
  apply Finset.sum_le_sum
  intro cell _
  exact layout_exits_le_delayed coarse ordered cell.val b bs (layouts cell) homogeneous boundary

end Ordered
end TangoSquared.ExitGapBridge
