import ChaCha.ReturnLayouts
import ChaCha.GapRecords
import ChaCha.OccurrenceAccounting

/-!
# Lifting projected run payments to actual global witness records

All projection decompositions retain their prefix and suffix identities. This
keeps occurrence positions available when payment records are counted by time.
-/

namespace ChaCha

open Primary NormalizedWords Witnesses

/-- Two selected projected occurrences, with all three projected pieces retained. -/
theorem filterMap_pair_lift_exact {α β : Type*} (f : α → Option β)
    {xs : List α} {pre middle post : List β} {a b : β}
    (h : xs.filterMap f = pre ++ a :: (middle ++ b :: post)) :
    ∃ before p between q after,
      xs = before ++ p :: (between ++ q :: after) ∧
      f p = some a ∧ f q = some b ∧
      before.filterMap f = pre ∧ between.filterMap f = middle ∧ after.filterMap f = post := by
  obtain ⟨left, rest, hx, hleft, hrest⟩ := List.filterMap_eq_append_iff.mp h
  obtain ⟨skip, p, tail, hr, hskip, hp, htail⟩ := List.filterMap_eq_cons_iff.mp hrest
  obtain ⟨mid, rest', ht, hmid, hrest'⟩ := List.filterMap_eq_append_iff.mp htail
  obtain ⟨skip', q, after, hr', hskip', hq, hafter⟩ := List.filterMap_eq_cons_iff.mp hrest'
  refine ⟨left ++ skip, p, mid ++ skip', q, after, ?_, hp, hq, ?_, ?_, hafter⟩
  · simp only [hx, hr, ht, hr', List.append_assoc]
  · rw [List.filterMap_append, hleft, List.filterMap_eq_nil_iff.mpr hskip, List.append_nil]
  · rw [List.filterMap_append, hmid, List.filterMap_eq_nil_iff.mpr hskip', List.append_nil]

/-- Three selected projected occurrences, preserving exact intervening words. -/
theorem filterMap_three_lift_exact {α β : Type*} (f : α → Option β)
    {xs : List α} {pre middle₁ middle₂ post : List β} {a b c : β}
    (h : xs.filterMap f = pre ++ a :: (middle₁ ++ b :: (middle₂ ++ c :: post))) :
    ∃ before p between₁ q between₂ r after,
      xs = before ++ p :: (between₁ ++ q :: (between₂ ++ r :: after)) ∧
      f p = some a ∧ f q = some b ∧ f r = some c ∧
      before.filterMap f = pre ∧ between₁.filterMap f = middle₁ ∧
      between₂.filterMap f = middle₂ ∧ after.filterMap f = post := by
  obtain ⟨before, p, between₁, q, tail, hx, hp, hq, hb, hm₁, htail⟩ :=
    filterMap_pair_lift_exact f h
  obtain ⟨middle, rest, ht, hmiddle, hrest⟩ := List.filterMap_eq_append_iff.mp htail
  obtain ⟨skip, r, after, hr, hskip, hrr, hafter⟩ := List.filterMap_eq_cons_iff.mp hrest
  refine ⟨before, p, between₁, q, middle ++ skip, r, after, ?_, hp, hq, hrr,
    hb, hm₁, ?_, hafter⟩
  · simp only [hx, ht, hr, List.append_assoc]
  · rw [List.filterMap_append, hmiddle, List.filterMap_eq_nil_iff.mpr hskip, List.append_nil]

/-- Empty owner-local space between a fine-changing pair is also empty globally. -/
theorem normalized_projected_between_empty {H f : Nat} {u : Key} {word : List Key}
    (initial : Key → Bool) (leaves : OnLeaves H word) (normal : Normalized initial H word)
    (before between after : List Key) (p q : Key)
    (split : word = before ++ p :: (between ++ q :: after))
    (hp : u.IsPrefix p) (hq : u.IsPrefix q)
    (empty : between.filterMap (fineProjection u f) = [])
    (different : p.take f ≠ q.take f) : between = [] := by
  have outside : ∀ z ∈ between, ¬ u.IsPrefix z := by
    intro z hz hu
    have hn := List.filterMap_eq_nil_iff.mp empty z hz
    simp [fineProjection, hu] at hn
  have hpH := leaves p (by simp [split])
  have hqH := leaves q (by simp [split])
  have hmH : ∀ z ∈ between, z.length = H := fun z hz => leaves z (by simp [split, hz])
  apply local_change_is_global_step initial H before between after u p q hpH hqH hmH hp hq outside
    (by simpa only [List.append_assoc, List.singleton_append] using split ▸ normal)
  intro heq
  exact different (congrArg (List.take f) heq)

/-- The canonical fine-cell partial projection used in cyclic gadget layouts. -/
def gadgetProjection (H : Nat) (q : Gadget) : Key → Option Key :=
  fineProjection q.owner (min (q.split.hi + 1) H)

theorem gadgetProjection_some {H : Nat} {q : Gadget} {x a : Key}
    (hx : x.length = H) (h : gadgetProjection H q x = some a) :
    q.owner.IsPrefix x ∧ q.fine x = a := by
  obtain ⟨ho, ht⟩ := fineProjection_some h
  refine ⟨ho, ?_⟩
  have htake : x.take (min (q.split.hi + 1) H) = x.take (q.split.hi + 1) := by
    rw [← List.take_take, ← hx, List.take_length]
  exact htake.symm.trans ht

theorem projection_coarse_depth {H : Nat} {q : Gadget} (hq : Valid H q) :
    q.split.cut + 1 ≤ min (q.split.hi + 1) H := by
  have hb := DepthTree.node_bounds _ hq.1
  omega

theorem gadgetProjection_coarse {H : Nat} {q : Gadget} (hq : Valid H q) {x a : Key}
    (h : gadgetProjection H q x = some a) : q.coarse x = a.take (q.split.cut + 1) := by
  obtain ⟨_, ht⟩ := fineProjection_some h
  rw [← ht, List.take_take, Nat.min_eq_left (projection_coarse_depth hq)]
  rfl

/-- A strict comparison of fine prefixes implies the same actual-key comparison. -/
theorem lt_of_projected_lt {H : Nat} {q : Gadget} {x y a b : Key}
    (hx : gadgetProjection H q x = some a) (hy : gadgetProjection H q y = some b)
    (hab : a < b) : x < y := by
  obtain ⟨_, hxa⟩ := fineProjection_some hx
  obtain ⟨_, hyb⟩ := fineProjection_some hy
  by_contra hn
  have h := take_mono_lex (le_of_not_gt hn) (min (q.split.hi + 1) H)
  rw [hxa, hyb] at h
  exact (not_lt_of_ge h) hab

/-- Lift a projected entry source and first micro turn, retaining the exact
actual prefix and suffix and constructing its concrete global event record. -/
theorem projected_entry_record {H : Nat} {q : Gadget} {word : List Key}
    (hq : Valid H q) (initial : Key → Bool) (leaves : OnLeaves H word)
    (normal : Normalized initial H word)
    {pre plateau post : List Key} {zF pF xF : Key}
    (split : word.filterMap (gadgetProjection H q) = pre ++ zF :: (plateau ++ pF :: xF :: post))
    (same : pF.take (q.split.cut + 1) = xF.take (q.split.cut + 1))
    (other : zF.take (q.split.cut + 1) ≠ xF.take (q.split.cut + 1))
    (different : pF ≠ xF)
    (reversal : (zF < xF ∧ xF < pF) ∨ (pF < xF ∧ xF < zF))
    (constant : ∀ a ∈ plateau, a = pF) :
    ∃ before z between p x after,
      word = before ++ z :: (between ++ p :: x :: after) ∧
      gadgetProjection H q z = some zF ∧ gadgetProjection H q p = some pF ∧
      gadgetProjection H q x = some xF ∧
      before.filterMap (gadgetProjection H q) = pre ∧
      between.filterMap (gadgetProjection H q) = plateau ∧
      after.filterMap (gadgetProjection H q) = post ∧
      Nonempty (EntryEvent (before ++ z :: (between ++ [p])) x q z) := by
  obtain ⟨before, z, between, p, empty, x, after, hw, hz, hp, hx, hbefore, hbetween, hempty, hafter⟩ :=
    filterMap_three_lift_exact (gadgetProjection H q) (middle₂ := []) split
  have hpH := leaves p (by simp [hw])
  have hxH := leaves x (by simp [hw])
  have hzH := leaves z (by simp [hw])
  obtain ⟨hup, hpp⟩ := gadgetProjection_some hpH hp
  obtain ⟨hux, hxx⟩ := gadgetProjection_some hxH hx
  obtain ⟨huz, hzz⟩ := gadgetProjection_some hzH hz
  have hpair : word = (before ++ z :: between) ++ p :: (empty ++ x :: after) := by
    simpa only [List.append_assoc, List.cons_append] using hw
  have he := normalized_projected_between_empty initial leaves normal
    (before ++ z :: between) empty after p x hpair hup hux hempty
    (by obtain ⟨_, hp'⟩ := fineProjection_some hp
        obtain ⟨_, hx'⟩ := fineProjection_some hx
        simpa only [hp', hx'] using different)
  subst empty
  simp only [List.nil_append] at hw
  refine ⟨before, z, between, p, x, after, hw, hz, hp, hx, hbefore, hbetween, hafter, ?_⟩
  refine ⟨{
    before := before, middle := between, previous := p, history_eq := rfl,
    owner_source := huz, owner_target := hux, owner_previous := hup,
    coarse_same := ?_, coarse_other := ?_, fine_change := ?_, reversal := ?_, first_fine := ?_ }⟩
  · rw [gadgetProjection_coarse hq hp, gadgetProjection_coarse hq hx]
    exact same
  · rw [gadgetProjection_coarse hq hz, gadgetProjection_coarse hq hx]
    exact other
  · rw [hpp, hxx]
    exact different
  · rcases reversal with h | h
    · exact Or.inl ⟨lt_of_projected_lt hz hx h.1, lt_of_projected_lt hx hp h.2⟩
    · exact Or.inr ⟨lt_of_projected_lt hp hx h.1, lt_of_projected_lt hx hz h.2⟩
  · intro y hy huy
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · let a := y.take (min (q.split.hi + 1) H)
      have hya : gadgetProjection H q y = some a := by simp [gadgetProjection, fineProjection, huy, a]
      have ham : a ∈ plateau := by
        rw [← hbetween]
        exact List.mem_filterMap.mpr ⟨y, hy, hya⟩
      have hyH := leaves y (by simp [hw, hy])
      have hf := (gadgetProjection_some hyH hya).2
      exact hf.trans ((constant a ham).trans hpp.symm)
    · rfl

/-- Lift a projected retained micro record and its opposite trigger to the
actual global history. The source micro pair is proved globally adjacent, and
outside-owner requests remain present in the retained global interval. -/
theorem projected_delayed_record_exact {H : Nat} {q : Gadget} {word : List Key}
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
    ∃ before y p between x after,
      word = before ++ y :: p :: (between ++ x :: after) ∧
      gadgetProjection H q y = some yF ∧ gadgetProjection H q p = some pF ∧
      gadgetProjection H q x = some xF ∧
      before.filterMap (gadgetProjection H q) = pre ∧
      between.filterMap (gadgetProjection H q) = retainedF ∧
      after.filterMap (gadgetProjection H q) = post ∧
      ∃ record : DelayedEvent (before ++ y :: p :: between) x q y,
        record.before = before ∧ record.next = p ∧ record.later = between := by
  obtain ⟨before, y, empty, p, between, x, after, hw, hy, hp, hx, hbefore, hempty, hbetween, hafter⟩ :=
    filterMap_three_lift_exact (gadgetProjection H q) (middle₁ := []) split
  have hyH := leaves y (by simp [hw])
  have hpH := leaves p (by simp [hw])
  have hxH := leaves x (by simp [hw])
  obtain ⟨huy, hyy⟩ := gadgetProjection_some hyH hy
  obtain ⟨hup, hpp⟩ := gadgetProjection_some hpH hp
  obtain ⟨hux, hxx⟩ := gadgetProjection_some hxH hx
  have he := normalized_projected_between_empty initial leaves normal before empty
    (between ++ x :: after) y p hw huy hup hempty
    (by obtain ⟨_, hy'⟩ := fineProjection_some hy
        obtain ⟨_, hp'⟩ := fineProjection_some hp
        simpa only [hy', hp'] using different)
  subst empty
  simp only [List.nil_append] at hw
  refine ⟨before, y, p, between, x, after, hw, hy, hp, hx, hbefore, hbetween, hafter, ?_⟩
  refine ⟨{
    before := before, later := between, next := p, history_eq := rfl,
    owner_source := huy, owner_target := hux, owner_next := hup,
    coarse_same := ?_, coarse_other := ?_, fine_change := ?_, reversal := ?_, retained := ?_ },
    rfl, rfl, rfl⟩
  · rw [gadgetProjection_coarse hq hy, gadgetProjection_coarse hq hp]
    exact same
  · rw [gadgetProjection_coarse hq hy, gadgetProjection_coarse hq hx]
    exact other
  · rw [hyy, hpp]
    exact different
  · rcases reversal with h | h
    · exact Or.inl ⟨lt_of_projected_lt hx hy h.1, lt_of_projected_lt hy hp h.2⟩
    · exact Or.inr ⟨lt_of_projected_lt hp hy h.1, lt_of_projected_lt hy hx h.2⟩
  · intro z hz huz
    rcases List.mem_cons.mp hz with hzp | hz
    · subst z
      exact Or.inl rfl
    · let a := z.take (min (q.split.hi + 1) H)
      have hza : gadgetProjection H q z = some a := by simp [gadgetProjection, fineProjection, huz, a]
      have ham : a ∈ retainedF := by
        rw [← hbetween]
        exact List.mem_filterMap.mpr ⟨z, hz, hza⟩
      rcases retained a ham with ha | ⟨hother, hside⟩
      · left
        have hzH := leaves z (by simp [hw, hz])
        exact (gadgetProjection_some hzH hza).2.trans (ha.trans hpp.symm)
      · right
        refine ⟨?_, ?_⟩
        · rw [gadgetProjection_coarse hq hza, gadgetProjection_coarse hq hy]
          exact hother
        · rcases hside with hs | hs
          · exact Or.inl ⟨lt_of_projected_lt hy hp hs.1, lt_of_projected_lt hy hza hs.2⟩
          · exact Or.inr ⟨lt_of_projected_lt hp hy hs.1, lt_of_projected_lt hza hy hs.2⟩

/-- The projected delayed-record constructor without optional decomposition metadata. -/
theorem projected_delayed_record {H : Nat} {q : Gadget} {word : List Key}
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
    ∃ before y p between x after,
      word = before ++ y :: p :: (between ++ x :: after) ∧
      gadgetProjection H q y = some yF ∧ gadgetProjection H q p = some pF ∧
      gadgetProjection H q x = some xF ∧
      before.filterMap (gadgetProjection H q) = pre ∧
      between.filterMap (gadgetProjection H q) = retainedF ∧
      after.filterMap (gadgetProjection H q) = post ∧
      Nonempty (DelayedEvent (before ++ y :: p :: between) x q y) := by
  obtain ⟨before, y, p, between, x, after, hw, hy, hp, hx, hb, hm, ha, record, _, _, _⟩ :=
    projected_delayed_record_exact hq initial leaves normal split same other different reversal retained
  exact ⟨before, y, p, between, x, after, hw, hy, hp, hx, hb, hm, ha, ⟨record⟩⟩

/-- The actual query index determined by an exact chronological decomposition. -/
def splitQueryIndex (word before : List Key) (x : Key) (after : List Key)
    (split : word = before ++ x :: after) : Fin word.length :=
  ⟨before.length, by rw [split, List.length_append, List.length_cons]; omega⟩

theorem splitQueryIndex_take (word before : List Key) (x : Key) (after : List Key)
    (split : word = before ++ x :: after) :
    word.take (splitQueryIndex word before x after split).val = before := by
  simp [splitQueryIndex, split]

theorem splitQueryIndex_get (word before : List Key) (x : Key) (after : List Key)
    (split : word = before ++ x :: after) :
    word[splitQueryIndex word before x after split] = x := by
  have h : word[before.length]? = some x := by simp [split]
  have hi : before.length < word.length := (splitQueryIndex word before x after split).isLt
  rw [List.getElem?_eq_getElem hi] at h
  exact Option.some.inj h

/-- An actual entry record becomes an active time-tag event, preserving its
entire exact history (hence every projected occurrence ordinal). -/
theorem indexed_entry_record {H : Nat} {qs : Finset Gadget} {q : Gadget}
    (hq : q ∈ qs) {word before after : List Key} {x y : Key}
    (split : word = before ++ x :: after) (record : EntryEvent before x q y) :
    ∃ i : Fin word.length, Sum.inl q ∈ eventsAt H qs [] word i ∧
      word.take i.val = before ∧ word[i] = x := by
  let i := splitQueryIndex word before x after split
  have htake : word.take i.val = before := splitQueryIndex_take word before x after split
  have hget : word[i] = x := splitQueryIndex_get word before x after split
  refine ⟨i, ?_, htake, hget⟩
  apply entry_record_mem_eventsAt i hq
  simpa only [queryHistory, List.nil_append, htake, hget] using record

/-- The delayed event index retains its source coarse cell and exact history. -/
theorem indexed_delayed_record {H : Nat} {qs : Finset Gadget} {q : Gadget}
    (hq : q ∈ qs) {word before after : List Key} {x y : Key}
    (split : word = before ++ x :: after) (record : DelayedEvent before x q y)
    (leaves : OnLeaves H word) :
    ∃ i : Fin word.length, Sum.inr (q, q.coarse y) ∈ eventsAt H qs [] word i ∧
      word.take i.val = before ∧ word[i] = x := by
  let i := splitQueryIndex word before x after split
  have htake : word.take i.val = before := splitQueryIndex_take word before x after split
  have hget : word[i] = x := splitQueryIndex_get word before x after split
  refine ⟨i, ?_, htake, hget⟩
  apply delayed_record_mem_eventsAt i hq
  · simpa only [queryHistory, List.nil_append, htake, hget] using record
  · simp only [queryHistory, List.nil_append, htake, hget]
    intro z hz
    apply leaves z
    simp only [List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · simp [split, hz]
    · simp [split]

/-- Equal actual trigger times have equal projected prefix ordinals. -/
theorem projected_ordinal_eq_of_same_time {β : Type*} (project : Key → Option β)
    {word before₁ before₂ after₁ after₂ : List Key} {x₁ x₂ : Key}
    (split₁ : word = before₁ ++ x₁ :: after₁)
    (split₂ : word = before₂ ++ x₂ :: after₂)
    (same_time : before₁.length = before₂.length) :
    before₁.filterMap project = before₂.filterMap project := by
  have ht₁ := splitQueryIndex_take word before₁ x₁ after₁ split₁
  have ht₂ := splitQueryIndex_take word before₂ x₂ after₂ split₂
  change word.take before₁.length = before₁ at ht₁
  change word.take before₂.length = before₂ at ht₂
  have hb : before₁ = before₂ := ht₁.symm.trans (same_time ▸ ht₂)
  exact congrArg (List.filterMap project) hb

end ChaCha
