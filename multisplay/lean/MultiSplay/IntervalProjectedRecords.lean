import MultiSplay.IntervalWitnesses
import ChaCha.ProjectedRecords

/-!
# Actual projected records for arbitrary secondary depth hierarchies

The physical occurrence records and fine-cell projections are the existing
Cha-Cha objects. These extensions replace midpoint membership by
membership in the supplied interval hierarchy; all source occurrences and
exact chronological prefix/suffix decompositions are retained.
-/

namespace MultiSplay.IntervalLower

open ChaCha
open ChaCha.Primary ChaCha.NormalizedWords ChaCha.Witnesses

theorem projection_coarse_depth {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} (hq : Valid hierarchy q) :
    q.split.cut + 1 ≤ min (q.split.hi + 1) H := by
  have hb := DepthTree.node_bounds _ hq.1
  omega


theorem gadgetProjection_coarse {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} (hq : Valid hierarchy q) {x a : Key}
    (h : gadgetProjection H q x = some a) : q.coarse x = a.take (q.split.cut + 1) := by
  obtain ⟨_, ht⟩ := fineProjection_some h
  rw [← ht, List.take_take, Nat.min_eq_left (projection_coarse_depth hq)]
  rfl


theorem projected_entry_record {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {word : List Key}
    (hq : Valid hierarchy q) (initial : Key → Bool) (leaves : OnLeaves H word)
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


theorem projected_delayed_record_exact {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {word : List Key}
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


theorem projected_delayed_record {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} {word : List Key}
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


end MultiSplay.IntervalLower
