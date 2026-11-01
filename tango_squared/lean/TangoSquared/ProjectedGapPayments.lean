import TangoSquared.GapEventInjection
import TangoSquared.ProjectedGapGeometry

/-!
# Indexed payments from exact projected gap decompositions

The event records below occur in the actual global query sequence. Their
projected source and target ordinals are retained exactly, so finite gap
families can invoke the proved chronological event injection.
-/

namespace TangoSquared

open Primary Witnesses NormalizedWords

/-- A projected first micro turn yields an actual indexed entry record, with
its precise projected target ordinal. -/
theorem indexed_projected_entry {H : Nat} {q : Gadget} {word : List Key}
    (hq : Valid H q) (initial : Key → Bool) (leaves : OnLeaves H word)
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

/-- A projected retained micro pair and opposite trigger yield an actual indexed
delayed record. Both the source prefix and target prefix are preserved. -/
theorem indexed_projected_delayed {H : Nat} {q : Gadget} {word : List Key}
    (hq : Valid H q) (initial : Key → Bool) (leaves : OnLeaves H word)
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

/-- Any opposite excursion in an actual projected gap supplies an indexed
delayed payment at its first opposite occurrence, preserving the source ordinal. -/
theorem indexed_first_opposite_delayed {H : Nat} {q : Gadget} {word : List Key}
    (hq : Valid H q) (initial : Key → Bool) (leaves : OnLeaves H word)
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

end TangoSquared
