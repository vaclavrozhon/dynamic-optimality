import TangoSquared.GapChunks

/-!
# Cyclic entry weights and actual selected-run chunks

Weighted adjacency sums retain occurrences. Rotating a word preserves the
cyclic sum, and grouping at selected occurrences preserves every weight whose
destination is selected. This connects gap entries to actual run entries.
-/

namespace TangoSquared.CyclicEntryAccounting

open CyclicRuns GapChunks TurnAccounting

variable {β : Type*}

def adjacencyFrom (weight : β → β → Nat) : β → List β → Nat
  | _, [] => 0
  | previous, x :: xs => weight previous x + adjacencyFrom weight x xs

def cyclicAdjacency (weight : β → β → Nat) (fallback : β) (xs : List β) : Nat :=
  adjacencyFrom weight (xs.getLastD fallback) xs

theorem adjacencyFrom_append (weight : β → β → Nat) (previous : β) (xs ys : List β) :
    adjacencyFrom weight previous (xs ++ ys) =
      adjacencyFrom weight previous xs + adjacencyFrom weight (xs.getLastD previous) ys := by
  induction xs generalizing previous with
  | nil => simp [adjacencyFrom]
  | cons x xs ih => simp only [List.cons_append, adjacencyFrom, List.getLastD_cons, ih]; omega

theorem lastD_fallback (xs : List β) (x y : β) (hne : xs ≠ []) :
    xs.getLastD x = xs.getLastD y := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons a as => simp only [List.getLastD_cons]

theorem cyclicAdjacency_fallback (weight : β → β → Nat) (x y : β) (xs : List β) :
    cyclicAdjacency weight x xs = cyclicAdjacency weight y xs := by
  cases xs <;> simp only [cyclicAdjacency, adjacencyFrom, List.getLastD_cons]

theorem cyclicAdjacency_move_head (weight : β → β → Nat) (fallback b : β) (bs : List β) :
    cyclicAdjacency weight fallback (b :: bs) =
      cyclicAdjacency weight fallback (bs ++ [b]) := by
  simp only [cyclicAdjacency, List.getLastD_cons, lastD_append, List.getLastD_nil]
  rw [adjacencyFrom_append]
  simp only [adjacencyFrom]
  omega

theorem cyclicAdjacency_swap_append (weight : β → β → Nat) (fallback : β) (xs ys : List β) :
    cyclicAdjacency weight fallback (xs ++ ys) =
      cyclicAdjacency weight fallback (ys ++ xs) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    calc
      _ = cyclicAdjacency weight fallback ((xs ++ ys) ++ [x]) :=
        cyclicAdjacency_move_head weight fallback x _
      _ = cyclicAdjacency weight fallback (xs ++ (ys ++ [x])) := by rw [List.append_assoc]
      _ = cyclicAdjacency weight fallback ((ys ++ [x]) ++ xs) := ih _
      _ = _ := by simp [List.append_assoc]

theorem adjacencyFrom_congr (f g : β → β → Nat) (previous : β) (xs : List β)
    (eq : ∀ y ∈ xs, ∀ x, f x y = g x y) :
    adjacencyFrom f previous xs = adjacencyFrom g previous xs := by
  induction xs generalizing previous with
  | nil => rfl
  | cons y ys ih =>
    simp only [adjacencyFrom, eq y (by simp) previous]
    rw [ih y (fun z hz => eq z (by simp [hz]))]

theorem cyclicAdjacency_sum {ι : Type*} (s : Finset ι) (weight : ι → β → β → Nat)
    (fallback : β) (xs : List β) :
    cyclicAdjacency (fun x y => ∑ i ∈ s, weight i x y) fallback xs =
      ∑ i ∈ s, cyclicAdjacency (weight i) fallback xs := by
  suffices h : ∀ previous, adjacencyFrom (fun x y => ∑ i ∈ s, weight i x y) previous xs =
      ∑ i ∈ s, adjacencyFrom (weight i) previous xs from h _
  intro previous
  induction xs generalizing previous with
  | nil => simp [adjacencyFrom]
  | cons x xs ih => simp only [adjacencyFrom, ih, Finset.sum_add_distrib]

/-- Destination cells partition the full cyclic entry account exactly. -/
theorem cyclicAdjacency_partition {C : Type*} [DecidableEq C]
    (cell : β → C) (cells : Finset C) (weight : β → β → Nat)
    (fallback : β) (xs : List β) (cover : ∀ x ∈ xs, cell x ∈ cells) :
    (∑ c ∈ cells, cyclicAdjacency (fun x y => if cell y = c then weight x y else 0)
      fallback xs) = cyclicAdjacency weight fallback xs := by
  rw [← cyclicAdjacency_sum]
  apply adjacencyFrom_congr
  intro y hy x
  simp [cover y hy]

def Chunk.last (c : Chunk β) : β := c.middle.getLastD c.source

def chunkEntriesFrom (weight : β → β → Nat) : β → List (Chunk β) → Nat
  | _, [] => 0
  | previous, c :: cs => weight previous c.source + chunkEntriesFrom weight (Chunk.last c) cs

theorem chunkEntriesFrom_eq_adjacency (weight : β → β → Nat) (previous : Chunk β)
    (cs : List (Chunk β)) :
    chunkEntriesFrom weight (Chunk.last previous) cs =
      adjacencyFrom (fun c d => weight (Chunk.last c) d.source) previous cs := by
  induction cs generalizing previous with
  | nil => rfl
  | cons c cs ih => simp only [chunkEntriesFrom, adjacencyFrom, ih]

theorem chunks_last (fallback : β) (c : Chunk β) (cs : List (Chunk β)) :
    ((((c :: cs).map Chunk.word).flatten).getLastD fallback) =
      Chunk.last ((c :: cs).getLastD c) := by
  induction cs generalizing c with
  | nil => simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, Chunk.word, List.getLastD_cons, List.getLastD_nil, Chunk.last]
  | cons d ds ih =>
    simp only [List.map_cons, List.flatten_cons, Chunk.word, List.cons_append,
      List.getLastD_cons, lastD_append]
    have h := ih d
    simpa only [List.map_cons, List.flatten_cons, Chunk.word, List.cons_append,
      List.getLastD_cons, lastD_append] using h

theorem adjacencyFrom_zero (weight : β → β → Nat) (previous : β) (xs : List β)
    (zero : ∀ y ∈ xs, ∀ x, weight x y = 0) : adjacencyFrom weight previous xs = 0 := by
  induction xs generalizing previous with
  | nil => rfl
  | cons y ys ih =>
    simp only [adjacencyFrom, zero y (by simp) previous, zero_add]
    exact ih y (fun z hz => zero z (by simp [hz]))

theorem adjacencyFrom_chunks (weight : β → β → Nat) (previous : β) (cs : List (Chunk β))
    (zero : ∀ c ∈ cs, ∀ y ∈ c.middle, ∀ x, weight x y = 0) :
    adjacencyFrom weight previous ((cs.map Chunk.word).flatten) =
      chunkEntriesFrom weight previous cs := by
  induction cs generalizing previous with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.flatten_cons, Chunk.word, List.cons_append, adjacencyFrom]
    rw [adjacencyFrom_append, adjacencyFrom_zero weight c.source c.middle (zero c (by simp))]
    simp only [zero_add, chunkEntriesFrom, Chunk.last]
    rw [ih _ (fun d hd => zero d (by simp [hd]))]

theorem CycleLayout.selected_entry_sum {selected : β → Bool} {xs : List β}
    (layout : CycleLayout selected xs) (weight : β → β → Nat) (fallback : β)
    (zero : ∀ y, selected y = false → ∀ x, weight x y = 0) :
    cyclicAdjacency weight fallback xs =
      chunkEntriesFrom weight
        (((layout.chunks.map Chunk.word).flatten).getLastD fallback) layout.chunks := by
  have hrot : cyclicAdjacency weight fallback xs =
      cyclicAdjacency weight fallback ((layout.chunks.map Chunk.word).flatten) := by
    calc
      _ = cyclicAdjacency weight fallback (layout.cutBefore ++ layout.cutAfter) :=
        congrArg (cyclicAdjacency weight fallback) layout.split
      _ = cyclicAdjacency weight fallback (layout.cutAfter ++ layout.cutBefore) :=
        cyclicAdjacency_swap_append weight fallback _ _
      _ = _ := congrArg (cyclicAdjacency weight fallback) layout.rotation.symm
  rw [hrot]
  exact adjacencyFrom_chunks weight _ layout.chunks
    (fun c hc y hy => zero y (layout.middle_unselected c hc y hy))

/-- Read the same selected cyclic sum as weights on successive chunks. -/
theorem CycleLayout.selected_chunk_adjacency {selected : β → Bool} {xs : List β}
    (layout : CycleLayout selected xs) (weight : β → β → Nat) (fallback : β)
    (chunkFallback : Chunk β)
    (zero : ∀ y, selected y = false → ∀ x, weight x y = 0) :
    cyclicAdjacency weight fallback xs =
      cyclicAdjacency (fun c d => weight (Chunk.last c) d.source)
        chunkFallback layout.chunks := by
  rw [CycleLayout.selected_entry_sum layout weight fallback zero]
  cases he : layout.chunks with
  | nil => exact (layout.nonempty he).elim
  | cons c cs =>
    rw [chunks_last, chunkEntriesFrom_eq_adjacency]
    rfl

section Ordered

variable {α : Type*} [LinearOrder α]

/-- The entry cost depends on the predecessor and destination blocks only. -/
def entryWeight (previous current : Block α) : Nat :=
  Run.entryTurn (decide (previous.last < current.first)) ⟨current.micro, false⟩

theorem entryWeight_zero (previous current : Block α) (empty : current.micro = []) :
    entryWeight previous current = 0 := by simp [entryWeight, Run.entryTurn, empty]

theorem entryWeight_le_one (previous current : Block α) : entryWeight previous current ≤ 1 := by
  cases h : current.micro <;> simp only [entryWeight, Run.entryTurn, h, turn]
  · omega
  · split <;> omega

theorem adjacencyFrom_entryWeight (closing : α) (previous : Block α)
    (blocks : List (Block α)) :
    adjacencyFrom entryWeight previous blocks =
      runSum Run.entryTurn
        (decide (previous.last < ((blocks.head?).map Block.first).getD closing))
        (encode closing blocks) := by
  induction blocks generalizing previous with
  | nil => rfl
  | cons b bs ih =>
    simp only [adjacencyFrom, encode, runSum, List.head?_cons, Option.map_some, Option.getD_some]
    rw [ih b]
    congr 1

theorem cyclicIncoming_encode (closing : α) (b : Block α) (bs : List (Block α)) :
    cyclicIncoming (encode closing (b :: bs)) =
      decide ((bs.getLastD b).last < closing) := by
  induction bs generalizing b with
  | nil => rfl
  | cons c cs ih =>
    simp only [cyclicIncoming, encode, List.map_cons, List.getLastD_cons] at ih ⊢
    exact ih c

/-- The generic weighted cyclic sum is precisely the encoded run entry count. -/
theorem cyclicAdjacency_entryWeight (b : Block α) (bs : List (Block α)) :
    cyclicAdjacency entryWeight b (b :: bs) = entryTurns (encode b.first (b :: bs)) := by
  rw [cyclicAdjacency, adjacencyFrom_entryWeight b.first]
  simp only [List.head?_cons, Option.map_some, Option.getD_some, List.getLastD_cons,
    entryTurns, cyclicIncoming_encode]

end Ordered

end TangoSquared.CyclicEntryAccounting
