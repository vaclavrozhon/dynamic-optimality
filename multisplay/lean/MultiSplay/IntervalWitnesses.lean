import ChaCha.Witnesses

/-!
# Witness injection for an arbitrary binary depth hierarchy

This extends the concrete witness argument to any `DepthTree 0 H`. It reuses
exactly the existing entry/delayed records, physical search paths, and one-flip
normalization. The only hierarchy property needed for injection is uniqueness
of the split separating two depths, proved by `DepthTree.locate_of_separates`.
The shared Cha-Cha sources remain unchanged.
-/

namespace MultiSplay.IntervalLower

open ChaCha
open ChaCha.Primary ChaCha.NormalizedWords ChaCha.Witnesses

/-- Membership in the supplied hierarchy and the exact owner depth. -/
def Valid {H : Nat} (hierarchy : DepthTree 0 H) (gadget : Gadget) : Prop :=
  gadget.split ∈ hierarchy.nodes ∧ gadget.owner.length = gadget.split.lo

theorem separates_of_changes {H : Nat} {hierarchy : DepthTree 0 H} {q : Gadget} (hq : Valid hierarchy q)
    {a b c d : Key} (ha : a.length = H) (hb : b.length = H)
    (hc : c.length = H) (hd : d.length = H)
    (hua : q.owner.IsPrefix a) (hub : q.owner.IsPrefix b)
    (hmacro : q.coarse a ≠ q.coarse b) (hcoarse : q.coarse c = q.coarse d)
    (hfine : q.fine c ≠ q.fine d) :
    q.split.Separates (lcaDepth a b) (lcaDepth c d) := by
  obtain ⟨hqs, hlen⟩ := hq
  obtain ⟨_, hlo, hcut, hhi⟩ := DepthTree.node_bounds _ hqs
  have ho : a.take q.split.lo = b.take q.split.lo := by
    have hpa := List.prefix_iff_eq_take.mp hua
    have hpb := List.prefix_iff_eq_take.mp hub
    rw [hlen] at hpa hpb
    exact hpa.symm.trans hpb
  have helo : q.split.lo ≤ lcaDepth a b :=
    (take_eq_iff (by omega) (by omega)).1 ho
  have hehi : ¬ q.split.cut + 1 ≤ lcaDepth a b := by
    intro h
    exact hmacro ((take_eq_iff (by omega) (by omega)).2 h)
  have hflo : q.split.cut + 1 ≤ lcaDepth c d :=
    (take_eq_iff (by omega) (by omega)).1 hcoarse
  have hfhi : lcaDepth c d ≤ q.split.hi := by
    by_cases hh : q.split.hi < H
    · have hn : ¬ q.split.hi + 1 ≤ lcaDepth c d := by
        intro h
        exact hfine ((take_eq_iff (by omega) (by omega)).2 h)
      omega
    · have hlenbound := lcaDepth_le_left c d
      omega
  exact ⟨helo, by omega, by omega, hfhi⟩


theorem gadget_unique_of_separates {H : Nat} {hierarchy : DepthTree 0 H} {q r : Gadget} {x : Key} {e f : Nat}
    (hq : Valid hierarchy q) (hr : Valid hierarchy r) (hxq : q.owner.IsPrefix x) (hxr : r.owner.IsPrefix x)
    (hsq : q.split.Separates e f) (hsr : r.split.Separates e f) : q = r := by
  have h₁ := DepthTree.locate_of_separates _ hq.1 hsq
  have h₂ := DepthTree.locate_of_separates _ hr.1 hsr
  have hs : q.split = r.split := Option.some.inj (h₁.symm.trans h₂)
  have hlen : q.owner.length = r.owner.length := by rw [hq.2, hr.2, hs]
  have ho : q.owner = r.owner := by
    rw [List.prefix_iff_eq_take.mp hxq, List.prefix_iff_eq_take.mp hxr, hlen]
  cases q
  cases r
  simp_all


theorem EntryEvent.separated {H : Nat} {hierarchy : DepthTree 0 H} {history : List Key} {x y : Key} {q : Gadget}
    (e : EntryEvent history x q y) (hq : Valid hierarchy q) (hleaves : OnLeaves H (history ++ [x])) :
    q.split.Separates (lcaDepth y x) (lcaDepth e.previous x) := by
  have hyH : y.length = H := hleaves y (by simp [e.history_eq])
  have hxH : x.length = H := hleaves x (by simp)
  have hpH : e.previous.length = H := hleaves e.previous (by simp [e.history_eq])
  exact separates_of_changes hq hyH hxH hpH hxH e.owner_source e.owner_target
    e.coarse_other e.coarse_same e.fine_change


theorem DelayedEvent.separated {H : Nat} {hierarchy : DepthTree 0 H} {history : List Key} {x y : Key} {q : Gadget}
    (e : DelayedEvent history x q y) (hq : Valid hierarchy q) (hleaves : OnLeaves H (history ++ [x])) :
    q.split.Separates (lcaDepth y x) (lcaDepth y e.next) := by
  have hyH : y.length = H := hleaves y (by simp [e.history_eq])
  have hxH : x.length = H := hleaves x (by simp)
  have hpH : e.next.length = H := hleaves e.next (by simp [e.history_eq])
  exact separates_of_changes hq hyH hxH hyH hpH e.owner_source e.owner_target
    e.coarse_other e.coarse_same e.fine_change


theorem EntryEvent.gadget_unique {H : Nat} {hierarchy : DepthTree 0 H} {history : List Key} {x y : Key} {q r : Gadget}
    (e : EntryEvent history x q y) (f : EntryEvent history x r y)
    (hq : Valid hierarchy q) (hr : Valid hierarchy r) (hleaves : OnLeaves H (history ++ [x])) : q = r := by
  have hs := MultiSplay.IntervalLower.EntryEvent.separated f hr hleaves
  rw [← e.previous_unique f] at hs
  exact gadget_unique_of_separates hq hr e.owner_target f.owner_target (MultiSplay.IntervalLower.EntryEvent.separated e hq hleaves) hs


theorem DelayedEvent.gadget_unique {H : Nat} {hierarchy : DepthTree 0 H} {history : List Key} {x y : Key} {q r : Gadget}
    (e : DelayedEvent history x q y) (f : DelayedEvent history x r y)
    (hq : Valid hierarchy q) (hr : Valid hierarchy r) (hleaves : OnLeaves H (history ++ [x])) : q = r := by
  have hs := MultiSplay.IntervalLower.DelayedEvent.separated f hr hleaves
  rw [← e.next_unique f] at hs
  exact gadget_unique_of_separates hq hr e.owner_target f.owner_target (MultiSplay.IntervalLower.DelayedEvent.separated e hq hleaves) hs


theorem DelayedEvent.preference_retained {H : Nat} {hierarchy : DepthTree 0 H} {history : List Key} {x y : Key} {q : Gadget}
    (e : DelayedEvent history x q y) (hq : Valid hierarchy q) (hleaves : OnLeaves H (history ++ [x]))
    (initial : Key → Bool) {a : Bool}
    (hsource : branch (lcaNode y x) y = some a)
    (hside : ∀ z, z.length = H →
      ((y < e.next ∧ y < z) ∨ (e.next < y ∧ z < y)) →
      branch (lcaNode y x) z = none ∨ branch (lcaNode y x) z = some a) :
    preference initial history (lcaNode y x) = a := by
  have hsep := MultiSplay.IntervalLower.DelayedEvent.separated e hq hleaves
  have hvalid := DepthTree.node_bounds _ hq.1
  have hnested : q.owner.IsPrefix (lcaNode y x) := prefix_take_lca e.owner_source e.owner_target
  have hn : branch (lcaNode y x) e.next = some a := by
    apply branch_eq_of_take_eq _ e.coarse_same hsource
    rw [lcaNode_length]
    exact Nat.lt_succ_of_le hsep.2.1
  have hkeep : ∀ z ∈ e.next :: e.later,
      branch (lcaNode y x) z = none ∨ branch (lcaNode y x) z = some a := by
    intro z hz
    by_cases howner : q.owner.IsPrefix z
    · rcases e.retained z hz howner with hf | ⟨_, hs⟩
      · right
        apply branch_eq_of_take_eq _ hf.symm hn
        rw [lcaNode_length]
        obtain ⟨_, he, _, _⟩ := hsep
        omega
      · apply hside z _ hs
        apply hleaves z
        apply List.mem_append.mpr
        left
        simpa only [e.history_eq] using
          (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hz))) :
            z ∈ e.before ++ y :: e.next :: e.later)
    · left
      have hn : ¬ (lcaNode y x).IsPrefix z := fun h => howner (hnested.trans h)
      simp [branch, hn]
  have hstart := preference_append_last initial e.before y (lcaNode y x) a hsource
  have hpref := preference_append_same initial (e.before ++ [y]) (e.next :: e.later)
    (lcaNode y x) a hstart hkeep
  simpa only [List.append_assoc, List.singleton_append, ← e.history_eq] using hpref


theorem DelayedEvent.flips_lca {H : Nat} {hierarchy : DepthTree 0 H} {history : List Key} {x y : Key} {q : Gadget}
    (e : DelayedEvent history x q y) (hq : Valid hierarchy q) (hleaves : OnLeaves H (history ++ [x]))
    (initial : Key → Bool) : Flips initial history x (lcaNode y x) := by
  have hyH : y.length = H := hleaves y (by simp [e.history_eq])
  have hxH : x.length = H := hleaves x (by simp)
  rcases e.reversal with ⟨hxy, hyp⟩ | ⟨hpy, hyx⟩
  · obtain ⟨hxf, hyt⟩ := branches_lca_of_lt hxy (hxH.trans hyH.symm)
    rw [lcaNode_comm x y] at hxf hyt
    have hpref : preference initial history (lcaNode y x) = true := by
      apply MultiSplay.IntervalLower.DelayedEvent.preference_retained e hq hleaves initial hyt
      intro z hz hside
      apply branch_stays_right (hz.trans hyH.symm) hyt
      rcases hside with h | h
      · exact h.2
      · exact (not_lt_of_gt hyp h.1).elim
    exact ⟨false, hxf, by simp [hpref]⟩
  · obtain ⟨hyf, hxt⟩ := branches_lca_of_lt hyx (hyH.trans hxH.symm)
    have hpref : preference initial history (lcaNode y x) = false := by
      apply MultiSplay.IntervalLower.DelayedEvent.preference_retained e hq hleaves initial hyf
      intro z hz hside
      apply branch_stays_left (hz.trans hyH.symm) hyf
      rcases hside with h | h
      · exact (not_lt_of_gt hpy h.1).elim
      · exact h.2
    exact ⟨true, hxt, by simp [hpref]⟩


theorem entry_delayed_disjoint {H : Nat} {hierarchy : DepthTree 0 H} {history : List Key} {x y : Key} {q r : Gadget}
    (e : EntryEvent history x q y) (f : DelayedEvent history x r y)
    (hq : Valid hierarchy q) (hr : Valid hierarchy r) (hleaves : OnLeaves H (history ++ [x]))
    (initial : Key → Bool) (hone : OneFlip initial H history x) : False := by
  have hsep := MultiSplay.IntervalLower.EntryEvent.separated e hq hleaves
  have hpH : e.previous.length = H := hleaves e.previous (by simp [e.history_eq])
  have hxH : x.length = H := hleaves x (by simp)
  have hyH : y.length = H := hleaves y (by simp [e.history_eq])
  have hprev_ne : e.previous ≠ x := by
    rcases e.reversal with h | h
    · exact ne_of_gt h.2
    · exact ne_of_lt h.1
  have he_flip : Flips initial history x (lcaNode e.previous x) := by
    have h := consecutive_flip_lca initial (e.before ++ y :: e.middle)
      (hpH.trans hxH.symm) hprev_ne
    simpa only [lcaNode, List.append_assoc, List.cons_append, List.nil_append,
      ← e.history_eq] using h
  have hf_flip := MultiSplay.IntervalLower.DelayedEvent.flips_lca f hr hleaves initial
  have heH : lcaDepth e.previous x < H := by
    have h := lcaDepth_lt_of_ne (hpH.trans hxH.symm) hprev_ne
    omega
  have hyne : y ≠ x := by
    rcases e.reversal with h | h
    · exact ne_of_lt h.1
    · exact ne_of_gt h.2
  have hfH : lcaDepth y x < H := by
    have h := lcaDepth_lt_of_ne (hyH.trans hxH.symm) hyne
    omega
  have heowner : lcaNode e.previous x ∈ owners H :=
    (mem_owners _ _).2 (by simpa only [lcaNode_length] using heH)
  have hfowner : lcaNode y x ∈ owners H :=
    (mem_owners _ _).2 (by simpa only [lcaNode_length] using hfH)
  have heq := hone _ heowner _ hfowner he_flip hf_flip
  have hlen := congrArg List.length heq
  simp only [lcaNode_length] at hlen
  obtain ⟨_, hlow, hhigh, _⟩ := hsep
  omega


theorem event_tag_unique {H : Nat} {hierarchy : DepthTree 0 H} {history : List Key} {x y : Key}
    {tag₁ tag₂ : EventTag}
    (hvalid₁ : Valid hierarchy tag₁.gadget) (hvalid₂ : Valid hierarchy tag₂.gadget)
    (hrecord₁ : EventRecord history x tag₁ y) (hrecord₂ : EventRecord history x tag₂ y)
    (hleaves : OnLeaves H (history ++ [x])) (initial : Key → Bool)
    (hone : OneFlip initial H history x) : tag₁ = tag₂ := by
  cases tag₁ with
  | inl q =>
    cases tag₂ with
    | inl r =>
      obtain ⟨e⟩ := hrecord₁
      obtain ⟨f⟩ := hrecord₂
      exact congrArg Sum.inl (MultiSplay.IntervalLower.EntryEvent.gadget_unique e f hvalid₁ hvalid₂ hleaves)
    | inr pair =>
      obtain ⟨r, cell⟩ := pair
      obtain ⟨e⟩ := hrecord₁
      obtain ⟨_, ⟨f⟩⟩ := hrecord₂
      exact (entry_delayed_disjoint e f hvalid₁ hvalid₂ hleaves initial hone).elim
  | inr pair =>
    obtain ⟨q, cell⟩ := pair
    cases tag₂ with
    | inl r =>
      obtain ⟨_, ⟨e⟩⟩ := hrecord₁
      obtain ⟨f⟩ := hrecord₂
      exact (entry_delayed_disjoint f e hvalid₂ hvalid₁ hleaves initial hone).elim
    | inr pair =>
      obtain ⟨r, other⟩ := pair
      obtain ⟨hc, ⟨e⟩⟩ := hrecord₁
      obtain ⟨ho, ⟨f⟩⟩ := hrecord₂
      have hq := MultiSplay.IntervalLower.DelayedEvent.gadget_unique e f hvalid₁ hvalid₂ hleaves
      subst r
      have hcell : cell = other := hc.symm.trans ho
      exact congrArg Sum.inr (Prod.ext rfl hcell)


theorem joint_internal_budget {H : Nat} {hierarchy : DepthTree 0 H} {history : List Key} {x : Key}
    (tags : Finset EventTag) (witness : EventTag → Key)
    (valid : ∀ tag ∈ tags, Valid hierarchy tag.gadget)
    (records : ∀ tag ∈ tags, EventRecord history x tag (witness tag))
    (hleaves : OnLeaves H (history ++ [x])) (initial : Key → Bool)
    (hone : OneFlip initial H history x) (t : MTR.Tree Key)
    (success : MTR.Tree.Successful t history) (depth : Nat)
    (target_success : MTR.Tree.searchDepth x (MTR.run t history) = some depth) :
    tags.card ≤ depth - 1 := by
  classical
  have hcard : tags.card ≤ (MTR.Tree.internalSearchPath x (MTR.run t history)).toFinset.card := by
    apply Finset.card_le_card_of_injOn witness
    · intro tag htag
      exact List.mem_toFinset.mpr (event_record_internal (records tag htag) t success
        ⟨depth, target_success⟩)
    · intro a ha b hb heq
      have hr : EventRecord history x b (witness a) := by rw [heq]; exact records b hb
      exact event_tag_unique (valid a ha) (valid b hb) (records a ha) hr hleaves initial hone
  have hlength := List.toFinset_card_le (l := MTR.Tree.internalSearchPath x (MTR.run t history))
  have hexact := MTR.Tree.internalSearchPath_length x (MTR.run t history) depth target_success
  omega


theorem activeEvents_budget {H : Nat} {hierarchy : DepthTree 0 H} {history : List Key} {x : Key}
    (qs : Finset Gadget) (valid : ∀ q ∈ qs, Valid hierarchy q)
    (hleaves : OnLeaves H (history ++ [x])) (initial : Key → Bool)
    (hone : OneFlip initial H history x) (t : MTR.Tree Key)
    (success : MTR.Tree.Successful t history) (depth : Nat)
    (target_success : MTR.Tree.searchDepth x (MTR.run t history) = some depth) :
    (activeEvents H qs history x).card ≤ depth - 1 := by
  classical
  let witness : EventTag → Key := fun tag =>
    if h : ∃ y, EventRecord history x tag y then Classical.choose h else []
  apply joint_internal_budget (hierarchy := hierarchy) (activeEvents H qs history x) witness _ _
    hleaves initial hone t success depth target_success
  · intro tag htag
    have hcandidate := (Finset.mem_filter.mp htag).1
    cases tag with
    | inl q =>
      have hq : q ∈ qs := by simpa only [eventCandidates, Finset.inl_mem_disjSum] using hcandidate
      exact valid q hq
    | inr pair =>
      obtain ⟨q, cell⟩ := pair
      have hq : q ∈ qs := (by
        simpa only [eventCandidates, Finset.inr_mem_disjSum, Finset.mem_product] using
          hcandidate : q ∈ qs ∧ cell ∈ owners (H + 1)).1
      exact valid q hq
  · intro tag htag
    have hrecord := (Finset.mem_filter.mp htag).2
    simp only [witness, dif_pos hrecord]
    exact Classical.choose_spec hrecord


end MultiSplay.IntervalLower
