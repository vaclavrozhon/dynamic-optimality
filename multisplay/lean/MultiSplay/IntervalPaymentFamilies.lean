import MultiSplay.IntervalProjectedRecords
import ChaCha.ProjectedGapPayments
import ChaCha.PaymentFamilies

/-!
# Indexed payment families for an arbitrary interval hierarchy

These extensions keep the shared indexed-event records and actual query-time
injections. Only the interval-hierarchy membership parameter changes.
-/

namespace MultiSplay.IntervalLower

open ChaCha
open ChaCha.Primary ChaCha.Witnesses ChaCha.NormalizedWords

theorem indexed_projected_entry {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {word : List Key}
    (hq : Valid hierarchy q) (initial : Key → Bool) (leaves : OnLeaves H word)
    (normal : Normalized initial H word)
    {pre plateau post : List Key} {zF pF xF : Key}
    (split : word.filterMap (gadgetProjection H q) = pre ++ zF :: (plateau ++ pF :: xF :: post))
    (same : pF.take (q.split.cut + 1) = xF.take (q.split.cut + 1))
    (other : zF.take (q.split.cut + 1) ≠ xF.take (q.split.cut + 1))
    (different : pF ≠ xF)
    (reversal : (zF < xF ∧ xF < pF) ∨ (pF < xF ∧ xF < zF))
    (constant : ∀ a ∈ plateau, a = pF) :
    ∃ (time : Fin word.length) (source : Key),
      gadgetProjection H q source = some zF ∧
      gadgetProjection H q word[time] = some xF ∧
      ∃ _record : EntryEvent (queryHistory [] word time) word[time] q source,
        (word.take time.val).filterMap (gadgetProjection H q) = pre ++ zF :: (plateau ++ [pF]) ∧
        ((word.take time.val).filterMap (gadgetProjection H q)).length =
          pre.length + plateau.length + 2 := by
  obtain ⟨before, z, between, p, x, after, hw, hz, hp, hx, hb, hm, _, ⟨record⟩⟩ :=
    projected_entry_record hq initial leaves normal split same other different reversal constant
  let history := before ++ z :: (between ++ [p])
  have hsplit : word = history ++ x :: after := by
    simpa only [history, List.append_assoc, List.cons_append, List.nil_append] using hw
  let time := splitQueryIndex word history x after hsplit
  have htake : word.take time.val = history := splitQueryIndex_take word history x after hsplit
  have hget : word[time] = x := splitQueryIndex_get word history x after hsplit
  have hhistory : queryHistory [] word time = history := by simp only [queryHistory, List.nil_append, htake]
  have hproject : (word.take time.val).filterMap (gadgetProjection H q) =
      pre ++ zF :: (plateau ++ [pF]) := by
    simp only [htake, history, List.filterMap_append, List.filterMap_cons,
      hz, hp, List.filterMap_nil, hb, hm]
  refine ⟨time, z, hz, by simpa only [hget] using hx, ?_⟩
  have hrecord : EntryEvent (queryHistory [] word time) word[time] q z := by
    simpa only [hhistory, hget, history] using record
  refine ⟨hrecord, hproject, ?_⟩
  simp only [hproject, List.length_append, List.length_cons, List.length_nil]
  omega


theorem indexed_projected_delayed {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {word : List Key}
    (hq : Valid hierarchy q) (initial : Key → Bool) (leaves : OnLeaves H word)
    (normal : Normalized initial H word)
    {pre retainedF post : List Key} {yF pF xF : Key}
    (split : word.filterMap (gadgetProjection H q) = pre ++ yF :: pF :: (retainedF ++ xF :: post))
    (same : yF.take (q.split.cut + 1) = pF.take (q.split.cut + 1))
    (other : yF.take (q.split.cut + 1) ≠ xF.take (q.split.cut + 1))
    (different : yF ≠ pF)
    (reversal : (xF < yF ∧ yF < pF) ∨ (pF < yF ∧ yF < xF))
    (retained : ∀ a ∈ retainedF, a = pF ∨
      (a.take (q.split.cut + 1) ≠ yF.take (q.split.cut + 1) ∧
        ((yF < pF ∧ yF < a) ∨ (pF < yF ∧ a < yF)))) :
    ∃ (time : Fin word.length) (source : Key),
      gadgetProjection H q source = some yF ∧
      gadgetProjection H q word[time] = some xF ∧
      ∃ record : DelayedEvent (queryHistory [] word time) word[time] q source,
        record.before.filterMap (gadgetProjection H q) = pre ∧
        (record.before.filterMap (gadgetProjection H q)).length = pre.length ∧
        (word.take time.val).filterMap (gadgetProjection H q) = pre ++ yF :: pF :: retainedF ∧
        ((word.take time.val).filterMap (gadgetProjection H q)).length =
          pre.length + retainedF.length + 2 := by
  obtain ⟨before, y, p, between, x, after, hw, hy, hp, hx, hb, hm, _, record, hrb, _, _⟩ :=
    projected_delayed_record_exact hq initial leaves normal split same other different reversal retained
  let history := before ++ y :: p :: between
  have hsplit : word = history ++ x :: after := by
    simpa only [history, List.append_assoc, List.cons_append] using hw
  let time := splitQueryIndex word history x after hsplit
  have htake : word.take time.val = history := splitQueryIndex_take word history x after hsplit
  have hget : word[time] = x := splitQueryIndex_get word history x after hsplit
  have hhistory : queryHistory [] word time = history := by simp only [queryHistory, List.nil_append, htake]
  have hproject : (word.take time.val).filterMap (gadgetProjection H q) =
      pre ++ yF :: pF :: retainedF := by
    simp only [htake, history, List.filterMap_append, List.filterMap_cons, hy, hp, hb, hm]
  refine ⟨time, y, hy, by simpa only [hget] using hx, ?_⟩
  have hrecord : ∃ r : DelayedEvent (queryHistory [] word time) word[time] q y,
      r.before = before := by
    rw [hhistory, hget]
    exact ⟨record, hrb⟩
  obtain ⟨r, hr⟩ := hrecord
  refine ⟨r, by rw [hr]; exact hb, by rw [hr, hb], hproject, ?_⟩
  simp only [hproject, List.length_append, List.length_cons]
  omega


theorem indexed_first_opposite_delayed {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {word : List Key}
    (hq : Valid hierarchy q) (initial : Key → Bool) (leaves : OnLeaves H word)
    (normal : Normalized initial H word)
    {pre gap post : List Key} {yF pF : Key}
    (split : word.filterMap (gadgetProjection H q) = pre ++ yF :: pF :: (gap ++ post))
    (same : yF.take (q.split.cut + 1) = pF.take (q.split.cut + 1))
    (different : yF ≠ pF)
    (retained : ∀ a ∈ gap, a.take (q.split.cut + 1) = yF.take (q.split.cut + 1) → a = pF)
    (hit : ∃ x ∈ gap, ProjectedGapGeometry.Opposite (fun a : Key => a.take (q.split.cut + 1)) yF pF x) :
    ∃ (time : Fin word.length) (source : Key),
      gadgetProjection H q source = some yF ∧
      ∃ record : DelayedEvent (queryHistory [] word time) word[time] q source,
        record.before.filterMap (gadgetProjection H q) = pre ∧
        (record.before.filterMap (gadgetProjection H q)).length = pre.length ∧
        pre.length + 2 ≤ ((word.take time.val).filterMap (gadgetProjection H q)).length ∧
        ((word.take time.val).filterMap (gadgetProjection H q)).length < pre.length + gap.length + 2 := by
  obtain ⟨earlier, x, later, hgap, hopposite, hretained⟩ :=
    ProjectedGapGeometry.first_opposite_split (fun a : Key => a.take (q.split.cut + 1))
      yF pF gap different retained hit
  have hsplit : word.filterMap (gadgetProjection H q) =
      pre ++ yF :: pF :: (earlier ++ x :: (later ++ post)) := by
    rw [split, hgap]
    simp only [List.append_assoc, List.cons_append]
  obtain ⟨time, source, hsource, _, record, hbefore, hsourceLength, _, htargetLength⟩ :=
    indexed_projected_delayed hq initial leaves normal hsplit same
      (Ne.symm hopposite.1) different hopposite.2 hretained
  refine ⟨time, source, hsource, record, hbefore, hsourceLength, ?_, ?_⟩
  · rw [htargetLength]
    omega
  · have hlength := congrArg List.length hgap
    simp only [List.length_append, List.length_cons] at hlength
    omega


theorem projected_delayed_family_exists {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {word : List Key} {I : Type*}
    (hq : Valid hierarchy q) (initial : Key → Bool) (leaves : OnLeaves H word)
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


theorem projected_delayed_family_by_cell_exists {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {word : List Key}
    (hq : Valid hierarchy q) (initial : Key → Bool) (leaves : OnLeaves H word)
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


theorem indexed_entry_projected_delayed_card_le_eventSum {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {word : List Key}
    {E : Type*} [Fintype E] (qs : Finset Gadget) (hqmem : q ∈ qs)
    (hq : Valid hierarchy q) (initial : Key → Bool) (leaves : OnLeaves H word)
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


end MultiSplay.IntervalLower
