import TangoSquared.CyclicEntryAccounting
import TangoSquared.ProjectedGapPayments
import TangoSquared.PaymentFamilies
import TangoSquared.ChunkOccurrences
import Mathlib.Algebra.BigOperators.Fin

/-!
# Entry payments at distinct actual first-micro occurrences

The selected index is a run occurrence, not a run value. Its payment takes
place at the first genuine micro change in the second copied cyclic run word.
-/

namespace TangoSquared.EntryPayments

open Primary Witnesses NormalizedWords CyclicRuns RunOccurrences
open CyclicEntryAccounting ChunkOccurrences TurnAccounting

variable {β : Type*}

def predecessor (fallback : β) (xs : List β) (i : Nat) : β :=
  (xs.take i).getLastD (xs.getLastD fallback)

theorem predecessor_mem (b : β) (bs : List β) (i : Nat) :
    predecessor b (b :: bs) i ∈ b :: bs := by
  have h : predecessor b (b :: bs) i ∈ (b :: bs).getLastD b :: (b :: bs).take i :=
    List.getLastD_mem_cons
  rcases List.mem_cons.mp h with h | h
  · rw [h]
    simpa only [List.getLastD_cons] using (List.getLastD_mem_cons (l := bs) (a := b))
  · exact List.mem_of_mem_take h

theorem adjacencyFrom_eq_sum (weight : β → β → Nat) (previous : β) (xs : List β) :
    adjacencyFrom weight previous xs =
      ∑ i : Fin xs.length, weight ((xs.take i.val).getLastD previous) xs[i] := by
  induction xs generalizing previous with
  | nil => simp [adjacencyFrom]
  | cons x xs ih =>
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [adjacencyFrom, Fin.getElem_fin, Fin.val_zero, List.take_zero, List.getLastD_nil,
      List.getElem_cons_zero, Fin.val_succ, List.take_succ_cons, List.getLastD_cons,
      List.getElem_cons_succ, ih]

theorem cyclicAdjacency_eq_sum (weight : β → β → Nat) (fallback : β) (xs : List β) :
    cyclicAdjacency weight fallback xs =
      ∑ i : Fin xs.length, weight (predecessor fallback xs i.val) xs[i] :=
  adjacencyFrom_eq_sum weight _ xs

section Blocks

variable {α C : Type*} [LinearOrder α] [LinearOrder C]

omit [LinearOrder α] in
theorem blockWords_last (b : Block α) (bs : List (Block α)) (fallback : α) :
    (((b :: bs).map Block.word).flatten).getLastD fallback =
      ((b :: bs).getLastD b).last := by
  induction bs generalizing b with
  | nil => simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, Block.word, List.getLastD_cons, List.getLastD_nil, Block.last]
  | cons c cs ih =>
    simp only [List.map_cons, List.flatten_cons, Block.word, List.cons_append,
      List.getLastD_cons, lastD_append]
    have h := ih c
    simpa only [List.map_cons, List.flatten_cons, Block.word, List.cons_append,
      List.getLastD_cons, lastD_append] using h

omit [LinearOrder α] in
theorem precedingWord_last (b : Block α) (bs : List (Block α)) (i : Nat) :
    ((((b :: bs).map Block.word).flatten ++
      (((b :: bs).take i).map Block.word).flatten).getLastD b.first) =
      (predecessor b (b :: bs) i).last := by
  rw [lastD_append, blockWords_last]
  unfold predecessor
  cases ht : (b :: bs).take i with
  | nil => rfl
  | cons c cs =>
    rw [blockWords_last]
    simp only [List.getLastD_cons]

omit [LinearOrder α] [LinearOrder C] in
theorem adjacent_at_split (coarse : α → C) (previous : Block α)
    (before : List (Block α)) (current : Block α) (after : List (Block α))
    (adjacent : AdjacentDistinct coarse (previous :: (before ++ current :: after))) :
    coarse (before.getLastD previous).first ≠ coarse current.first := by
  induction before generalizing previous with
  | nil => exact adjacent.1
  | cons b bs ih => simpa only [List.getLastD_cons] using ih b adjacent.2

omit [LinearOrder α] [LinearOrder C] in
theorem adjacent_head_last (coarse : α → C) (b : Block α) (bs : List (Block α))
    (boundary : DistinctBoundaries (coarse b.first)
      ((b :: bs).map (Block.coarseSingleton coarse))) :
    coarse ((b :: bs).getLastD b).first ≠ coarse b.first := by
  have h := (adjacent_append_singleton coarse (b :: bs) b).mpr boundary
  simpa only [List.getLastD_cons] using adjacent_at_split coarse b bs b [] h

omit [LinearOrder α] [LinearOrder C] in
theorem predecessor_other (coarse : α → C) (b : Block α) (bs : List (Block α))
    (boundary : DistinctBoundaries (coarse b.first)
      ((b :: bs).map (Block.coarseSingleton coarse)))
    (i : Fin (b :: bs).length) :
    coarse (predecessor b (b :: bs) i.val).first ≠ coarse (b :: bs)[i].first := by
  have hall := (adjacent_append_singleton coarse (b :: bs) b).mpr boundary
  have hadj := adjacent_init coarse (b :: bs) b hall
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [predecessor, Fin.getElem_fin, Fin.val_zero, List.take_zero, List.getLastD_nil,
      List.getElem_cons_zero] using adjacent_head_last coarse b bs boundary
  · have hs : bs = bs.take j.val ++ bs[j] :: bs.drop (j.val + 1) := by
      simp only [Fin.getElem_fin]
      rw [← List.drop_eq_getElem_cons j.isLt]
      exact (List.take_append_drop j.val bs).symm
    have hd : AdjacentDistinct coarse (b :: (bs.take j.val ++ bs[j] :: bs.drop (j.val + 1))) := by
      simpa only [← hs] using hadj
    have h := adjacent_at_split coarse b (bs.take j.val) bs[j] (bs.drop (j.val + 1)) hd
    simpa only [predecessor, Fin.getElem_fin, Fin.val_succ, List.take_succ_cons, List.getLastD_cons,
      List.getElem_cons_succ] using h

omit [LinearOrder α] in
/-- An occurrence in the second run cycle has a literal predecessor query.
The target run's start offset is preserved exactly. -/
theorem second_cycle_run_split (b : Block α) (bs : List (Block α))
    (i : Fin (b :: bs).length) :
    ∃ pre post,
      (((b :: bs).map Block.word).flatten ++ ((b :: bs).map Block.word).flatten) =
        pre ++ (predecessor b (b :: bs) i.val).last :: ((b :: bs)[i].word ++ post) ∧
      pre.length + 1 = ((b :: bs).map Block.word).flatten.length +
        offset ((b :: bs).map Block.word) i.val := by
  let blocks := b :: bs
  let words := blocks.map Block.word
  let before := words.flatten ++ (words.take i.val).flatten
  have hbefore : before ≠ [] := by
    simp [before, words, blocks, Block.word]
  obtain hb | ⟨pre, z, hpre⟩ := List.eq_nil_or_concat before
  · exact (hbefore hb).elim
  have hz : z = (predecessor b (b :: bs) i.val).last := by
    have hlast := precedingWord_last b bs i.val
    have heq : before.getLastD b.first = z := by
      rw [hpre]
      simp only [List.concat_eq_append, lastD_append, List.getLastD_cons, List.getLastD_nil]
    exact heq.symm.trans (by simpa only [before, words, blocks, List.map_take] using hlast)
  let post := (words.drop (i.val + 1)).flatten
  have hsplit : words.flatten = (words.take i.val).flatten ++ blocks[i].word ++ post := by
    have hb : blocks = blocks.take i.val ++ blocks[i] :: blocks.drop (i.val + 1) := by
      simp only [Fin.getElem_fin]
      rw [← List.drop_eq_getElem_cons i.isLt]
      exact (List.take_append_drop i.val blocks).symm
    have h := congrArg (fun l => (l.map Block.word).flatten) hb
    simpa only [words, post, List.map_append, List.map_cons, List.flatten_append,
      List.flatten_cons, List.map_take, List.map_drop, List.append_assoc] using h
  refine ⟨pre, post, ?_, ?_⟩
  · change words.flatten ++ words.flatten = _
    calc
      _ = before ++ (blocks[i].word ++ post) := by
        conv_lhs => arg 2; rw [hsplit]
        simp only [before, List.append_assoc]
      _ = _ := by rw [hpre, hz]; simp only [List.concat_eq_append, List.append_assoc,
        List.singleton_append]; rfl
  · have hl := congrArg List.length hpre
    simp only [List.length_concat, before, List.length_append] at hl
    exact hl.symm

/-- A positive encoded entry turn is the actual geometric reversal at the
first fine-cell change, with its full initial plateau retained. -/
theorem entry_geometry (coarse : α → C) (ordered : Monotone coarse)
    (previous current : Block α) (homogeneous : current.Homogeneous coarse)
    (other : coarse previous.last ≠ coarse current.first)
    (payment : entryWeight previous current = 1) :
    ∃ k x after, current.word = List.replicate (k + 1) current.first ++ x :: after ∧
      current.first ≠ x ∧ coarse x = coarse current.first ∧
      ((previous.last < x ∧ x < current.first) ∨
        (current.first < x ∧ x < previous.last)) := by
  have hm : current.micro ≠ [] := by
    intro h
    have := entryWeight_zero previous current h
    omega
  obtain ⟨k, x, after, hsplit, hdiff⟩ := exists_first_micro current.first current.rest hm
  change current.word = List.replicate (k + 1) current.first ++ x :: after at hsplit
  have hxmem : x ∈ current.word := by rw [hsplit]; simp
  have hc := homogeneous x hxmem
  have hd := first_micro_direction current k x after hsplit hdiff
  have ht : turn (decide (previous.last < current.first)) (decide (current.first < x)) = 1 := by
    cases he : current.micro with
    | nil => exact (hm he).elim
    | cons d ds =>
      have heq : d = decide (current.first < x) := by
        simpa only [he, List.head?_cons, Option.some.injEq] using hd
      simpa only [entryWeight, Run.entryTurn, he, heq] using payment
  have ho : coarse previous.last ≠ coarse x := by simpa only [hc] using other
  have heq : decide (previous.last < current.first) = decide (previous.last < x) := by
    rw [direction_coarse coarse ordered _ _ other, direction_coarse coarse ordered _ _ ho, hc]
  rw [heq] at ht
  have hzx : previous.last ≠ x := fun he => ho (congrArg coarse he)
  refine ⟨k, x, after, hsplit, hdiff, hc, ?_⟩
  rcases lt_or_gt_of_ne hdiff with hpx | hxp
  · rcases lt_or_gt_of_ne hzx with hzx | hxz
    · simp [turn, hpx, hzx] at ht
    · exact Or.inr ⟨hpx, hxz⟩
  · rcases lt_or_gt_of_ne hzx with hzx | hxz
    · exact Or.inl ⟨hzx, hxp⟩
    · simp [turn, not_lt_of_gt hxp, not_lt_of_gt hxz] at ht

/-- The positive entry turns, indexed by genuine run occurrences. -/
def EntryIndex (b : Block α) (bs : List (Block α)) :=
  {i : Fin (b :: bs).length // entryWeight (predecessor b (b :: bs) i.val) (b :: bs)[i] = 1}

instance (b : Block α) (bs : List (Block α)) : Fintype (EntryIndex b bs) :=
  inferInstanceAs (Fintype {i : Fin (b :: bs).length //
    entryWeight (predecessor b (b :: bs) i.val) (b :: bs)[i] = 1})

theorem card_entryIndex (b : Block α) (bs : List (Block α)) :
    Fintype.card (EntryIndex b bs) = entryTurns (encode b.first (b :: bs)) := by
  rw [← cyclicAdjacency_entryWeight, cyclicAdjacency_eq_sum]
  unfold EntryIndex
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  have h := entryWeight_le_one (predecessor b (b :: bs) i.val) (b :: bs)[i]
  split <;> omega

end Blocks

/-- Place one positive entry at its literal query time in the global word. -/
theorem entry_at_occurrence {H : Nat} {q : Gadget} {word : List Key}
    (hq : Valid H q) (initial : Key → Bool) (leaves : OnLeaves H word)
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

/-- All encoded entries form an injective family of actual global query events.
The only embedding assumption is a literal doubled run word, with its complete
prefix and suffix; cyclic layout lemmas supply that embedding. -/
theorem family_of_doubled_runs {H : Nat} {q : Gadget} {word : List Key}
    (hq : Valid H q) (initial : Key → Bool) (leaves : OnLeaves H word)
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

/-- The original four copied periods contain the required two full run cycles.
This closes the chronological embedding obligation for entry payments. -/
theorem layout_family {H : Nat} {q : Gadget} {xs : List Key}
    (hq : Valid H q) (initial : Key → Bool) (leaves : OnLeaves H xs)
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

end TangoSquared.EntryPayments
