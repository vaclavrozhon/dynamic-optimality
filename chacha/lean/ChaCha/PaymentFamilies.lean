import ChaCha.ProjectedGapPayments

/-!
# Finite families of actual chronological payments

Entry families distinguish first-micro target occurrences. Delayed families
distinguish their retained coarse cell and last-micro source occurrence. The
families have no unused indices, which permits empty query words and empty
payment sets without artificial query times.
-/

namespace ChaCha

open Primary Witnesses NormalizedWords

/-- Actual indexed entry records with distinct projected target occurrences. -/
structure IndexedEntryFamily (H : Nat) (q : Gadget) (word : List Key) (I : Type*) where
  time : I → Fin word.length
  source : I → Key
  record : ∀ i, EntryEvent (queryHistory [] word (time i)) word[time i] q (source i)
  ordinal : I → Nat
  ordinal_eq : ∀ i, ((word.take (time i).val).filterMap (gadgetProjection H q)).length = ordinal i
  injective : Function.Injective ordinal

/-- Actual indexed delayed records with distinct source occurrences per cell. -/
structure IndexedDelayedFamily (H : Nat) (q : Gadget) (word : List Key) (I : Type*) where
  time : I → Fin word.length
  source : I → Key
  record : ∀ i, DelayedEvent (queryHistory [] word (time i)) word[time i] q (source i)
  ordinal : I → Nat
  ordinal_eq : ∀ i, ((record i).before.filterMap (gadgetProjection H q)).length = ordinal i
  injective : Function.Injective (fun i => (q.coarse (source i), ordinal i))

/-- The combined finite families fit in the actual chronological event sum. -/
theorem indexed_families_card_le_eventSum {H : Nat} {q : Gadget} {word : List Key}
    {I J : Type*} [Fintype I] [Fintype J] (qs : Finset Gadget) (hq : q ∈ qs)
    (leaves : OnLeaves H word)
    (entries : IndexedEntryFamily H q word I) (delays : IndexedDelayedFamily H q word J) :
    Fintype.card I + Fintype.card J ≤ eventSum H qs [] word := by
  classical
  have h := entry_delayed_payment_bound_by_cell (Finset.univ : Finset I) (Finset.univ : Finset J)
    H qs q hq word leaves (gadgetProjection H q)
    entries.time entries.source (fun i _ => entries.record i) entries.ordinal
    (fun i _ => entries.ordinal_eq i) entries.injective.injOn
    delays.time delays.source (fun i _ => delays.record i) delays.ordinal
    (fun i _ => delays.ordinal_eq i) delays.injective.injOn
  simpa only [Finset.card_univ] using h

/-- A literal projected source pair, retained gap, and nonempty opposite excursion. -/
structure ProjectedDelayedGap (H : Nat) (q : Gadget) (word : List Key) where
  pre : List Key
  source : Key
  next : Key
  gap : List Key
  post : List Key
  split : word.filterMap (gadgetProjection H q) = pre ++ source :: next :: (gap ++ post)
  same : source.take (q.split.cut + 1) = next.take (q.split.cut + 1)
  different : source ≠ next
  retained : ∀ a ∈ gap, a.take (q.split.cut + 1) = source.take (q.split.cut + 1) → a = next
  hit : ∃ x ∈ gap, ProjectedGapGeometry.Opposite
    (fun a : Key => a.take (q.split.cut + 1)) source next x

/-- Projected occurrence data construct actual global record families. The only
injection input concerns distinct literal source occurrences in the projected
word; actual event injection has already been proved from record retention. -/
theorem projected_delayed_family_exists {H : Nat} {q : Gadget} {word : List Key} {I : Type*}
    (hq : Valid H q) (initial : Key → Bool) (leaves : OnLeaves H word)
    (normal : Normalized initial H word) (data : I → ProjectedDelayedGap H q word)
    (injective : Function.Injective
      (fun i => ((data i).source.take (q.split.cut + 1), (data i).pre.length))) :
    Nonempty (IndexedDelayedFamily H q word I) := by
  classical
  have hrecords := fun i => indexed_first_opposite_delayed hq initial leaves normal
    (data i).split (data i).same (data i).different (data i).retained (data i).hit
  choose time source hsource record hbefore hlength _hlower _hupper using hrecords
  refine ⟨{
    time := time
    source := source
    record := record
    ordinal := fun i => (data i).pre.length
    ordinal_eq := hlength
    injective := ?_ }⟩
  intro i j hij
  apply injective
  have hcoarse : q.coarse (source i) = q.coarse (source j) := congrArg Prod.fst hij
  have hordinal : (data i).pre.length = (data j).pre.length := congrArg Prod.snd hij
  rw [gadgetProjection_coarse hq (hsource i), gadgetProjection_coarse hq (hsource j)] at hcoarse
  exact Prod.ext hcoarse hordinal

/-- Separate rotations for different coarse cells combine without requiring
cross-cell equality of their chosen origins. The physical source cell is part
of the delayed event tag. -/
theorem projected_delayed_family_by_cell_exists {H : Nat} {q : Gadget} {word : List Key}
    (hq : Valid H q) (initial : Key → Bool) (leaves : OnLeaves H word)
    (normal : Normalized initial H word) (cells : Finset Key)
    (I : (cell : cells) → Type*)
    (data : (cell : cells) → I cell → ProjectedDelayedGap H q word)
    (source_cell : ∀ cell i, (data cell i).source.take (q.split.cut + 1) = cell.val)
    (injective : ∀ cell, Function.Injective (fun i => (data cell i).pre.length)) :
    Nonempty (IndexedDelayedFamily H q word (Σ cell : cells, I cell)) := by
  apply projected_delayed_family_exists hq initial leaves normal (fun i => data i.1 i.2)
  intro ⟨ci, i⟩ ⟨cj, j⟩ heq
  have hc := congrArg Prod.fst heq
  change (data ci i).source.take (q.split.cut + 1) =
    (data cj j).source.take (q.split.cut + 1) at hc
  rw [source_cell ci i, source_cell cj j] at hc
  have he : ci = cj := Subtype.ext hc
  cases he
  have ho : (data ci i).pre.length = (data ci j).pre.length := congrArg Prod.snd heq
  have hi : i = j := injective ci ho
  cases hi
  rfl

/-- Finite delayed families indexed independently in each coarse cell combine
with one entry family using the same actual event budget. -/
theorem indexed_entry_projected_delayed_card_le_eventSum {H : Nat} {q : Gadget} {word : List Key}
    {E : Type*} [Fintype E] (qs : Finset Gadget) (hqmem : q ∈ qs)
    (hq : Valid H q) (initial : Key → Bool) (leaves : OnLeaves H word)
    (normal : Normalized initial H word) (entries : IndexedEntryFamily H q word E)
    (cells : Finset Key) (I : (cell : cells) → Type*) [∀ cell, Fintype (I cell)]
    (data : (cell : cells) → I cell → ProjectedDelayedGap H q word)
    (source_cell : ∀ cell i, (data cell i).source.take (q.split.cut + 1) = cell.val)
    (injective : ∀ cell, Function.Injective (fun i => (data cell i).pre.length)) :
    Fintype.card E + ∑ cell : cells, Fintype.card (I cell) ≤ eventSum H qs [] word := by
  obtain ⟨delays⟩ := projected_delayed_family_by_cell_exists hq initial leaves normal
    cells I data source_cell injective
  simpa only [Fintype.card_sigma] using
    indexed_families_card_le_eventSum qs hqmem leaves entries delays

end ChaCha
