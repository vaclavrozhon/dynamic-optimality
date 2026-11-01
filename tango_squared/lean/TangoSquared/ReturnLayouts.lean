import TangoSquared.CyclicRuns
import TangoSquared.NormalizedWords
import TangoSquared.Monotonicity
import TangoSquared.BlockReturnMatching
import Mathlib.Data.List.Chain

/-! Normalized returns for actual filtered fine-cell words and cyclic layouts. -/

namespace TangoSquared
open Primary NormalizedWords CyclicRuns

theorem NormalizedWords.Normalized.prefix {initial : Key → Bool} {H : Nat}
    {xs ys : List Key} (h : Normalized initial H (xs ++ ys)) : Normalized initial H xs := by
  intro history x future heq
  apply h history x (future ++ ys)
  rw [heq]
  simp only [List.append_assoc, List.cons_append]

/-- Lift two selected occurrences through an actual partial projection,
retaining the exact projected word between them. -/
theorem filterMap_pair_lift {α β : Type*} (f : α → Option β)
    {xs : List α} {pre middle post : List β} {a b : β}
    (h : xs.filterMap f = pre ++ a :: (middle ++ b :: post)) :
    ∃ before p between q after,
      xs = before ++ p :: (between ++ q :: after) ∧
      f p = some a ∧ f q = some b ∧ between.filterMap f = middle := by
  obtain ⟨left, rest, hx, _, hrest⟩ := List.filterMap_eq_append_iff.mp h
  obtain ⟨skip, p, tail, hr, hskip, hp, htail⟩ := List.filterMap_eq_cons_iff.mp hrest
  obtain ⟨mid, rest', ht, hmid, hrest'⟩ := List.filterMap_eq_append_iff.mp htail
  obtain ⟨skip', q, after, hr', hskip', hq, _⟩ := List.filterMap_eq_cons_iff.mp hrest'
  refine ⟨left ++ skip, p, mid ++ skip', q, after, ?_, hp, hq, ?_⟩
  · simp only [hx, hr, ht, hr', List.append_assoc]
  · rw [List.filterMap_append, hmid, List.filterMap_eq_nil_iff.mpr hskip', List.append_nil]

def fineProjection (u : Key) (d : Nat) (x : Key) : Option Key :=
  if u.IsPrefix x then some (x.take d) else none

theorem fineProjection_word (u : Key) (d : Nat) (xs : List Key) :
    xs.filterMap (fineProjection u d) = (ownerWord u xs).map (List.take d) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ho : ownerWord u (x :: xs) =
        if u.IsPrefix x then x :: ownerWord u xs else ownerWord u xs := by
      by_cases h : u.IsPrefix x <;> simp [ownerWord, h]
    by_cases h : u.IsPrefix x
    · have hf : fineProjection u d x = some (x.take d) := by simp [fineProjection, h]
      simp [ho, h, hf, ih]
    · have hf : fineProjection u d x = none := by simp [fineProjection, h]
      simp [ho, h, hf, ih]

theorem fineProjection_some {u x a : Key} {d : Nat}
    (h : fineProjection u d x = some a) : u.IsPrefix x ∧ x.take d = a := by
  by_cases hp : u.IsPrefix x
  · simpa [fineProjection, hp] using h
  · simp [fineProjection, hp] at h

/-- A change of projected fine label at consecutive owner-local accesses has
an actual globally consecutive source pair in a normalized execution. -/
theorem projected_change_global_pair {H f : Nat} {u : Key} {xs : List Key}
    (initial : Key → Bool) (hl : OnLeaves H xs) (hn : Normalized initial H xs)
    {pre post : List Key} {a b : Key}
    (hw : (ownerWord u xs).map (List.take f) = pre ++ a :: b :: post) (hne : a ≠ b) :
    ∃ before p q after, xs = before ++ p :: q :: after ∧
      u.IsPrefix p ∧ u.IsPrefix q ∧ p.take f = a ∧ q.take f = b := by
  have hpairs : xs.filterMap (fineProjection u f) = pre ++ a :: ([] ++ b :: post) := by
    simpa only [fineProjection_word, List.nil_append] using hw
  obtain ⟨before, p, between, q, after, hx, hp, hq, hm⟩ :=
    filterMap_pair_lift (fineProjection u f) hpairs
  obtain ⟨hup, hpa⟩ := fineProjection_some hp
  obtain ⟨huq, hqb⟩ := fineProjection_some hq
  have haw : ∀ y ∈ between, ¬ u.IsPrefix y := by
    intro y hy hpre
    have hnone := List.filterMap_eq_nil_iff.mp hm y hy
    simp [fineProjection, hpre] at hnone
  have hpH := hl p (by simp [hx])
  have hqH := hl q (by simp [hx])
  have hmH : ∀ y ∈ between, y.length = H := fun y hy => hl y (by simp [hx, hy])
  have hpq : p ≠ q := by intro heq; subst q; exact hne (hpa.symm.trans hqb)
  have hb := local_change_is_global_step initial H before between after u p q
    hpH hqH hmH hup huq haw
    (by simpa only [List.append_assoc, List.singleton_append] using hx ▸ hn) hpq
  refine ⟨before, p, q, after, ?_, hup, huq, hpa, hqb⟩
  simpa only [hb, List.nil_append] using hx

/-- A normalized global word induces exact returns in any owner-filtered,
fine-projected word. The outside excursion must contain an actual local query. -/
theorem projected_return {H c f : Nat} {u : Key} {xs : List Key}
    (initial : Key → Bool) (huc : u.length ≤ c) (hcf : c ≤ f) (hfH : f ≤ H)
    (hl : OnLeaves H xs) (hn : Normalized initial H xs)
    {pre away post : List Key} {a b : Key}
    (hw : (ownerWord u xs).map (List.take f) = pre ++ a :: (away ++ b :: post))
    (hab : a.take c = b.take c) (ha : away ≠ [])
    (hout : ∀ y ∈ away, y.take c ≠ a.take c) : a = b := by
  have hw' : xs.filterMap (fineProjection u f) = pre ++ a :: (away ++ b :: post) := by
    rw [fineProjection_word]
    exact hw
  obtain ⟨before, p, between, q, after, hx, hp, hq, hm⟩ :=
    filterMap_pair_lift (fineProjection u f) hw'
  obtain ⟨hup, hpa⟩ := fineProjection_some hp
  obtain ⟨huq, hqb⟩ := fineProjection_some hq
  have htakep : p.take c = a.take c := by rw [← hpa, List.take_take, Nat.min_eq_left hcf]
  have htakeq : q.take c = b.take c := by rw [← hqb, List.take_take, Nat.min_eq_left hcf]
  have hcellq : (p.take c).IsPrefix q := by rw [htakep, hab, ← htakeq]; exact List.take_prefix _ _
  have hucell : u.IsPrefix (p.take c) := by
    apply List.prefix_iff_eq_take.mpr
    rw [List.take_take, Nat.min_eq_left huc]
    exact List.prefix_iff_eq_take.mp hup
  have hbetween : ∀ y ∈ between, ¬ (p.take c).IsPrefix y := by
    intro y hy hcell
    have huy : u.IsPrefix y := hucell.trans hcell
    have hyf : fineProjection u f y = some (y.take f) := by simp [fineProjection, huy]
    have hyaway : y.take f ∈ away := by
      rw [← hm]
      exact List.mem_filterMap.mpr ⟨y, hy, hyf⟩
    apply hout _ hyaway
    rw [List.take_take, Nat.min_eq_left hcf, ← htakep]
    have hpH := hl p (by simp [hx])
    have hlen : (p.take c).length = c := by simp [List.length_take, hpH, Nat.min_eq_left (by omega : c ≤ H)]
    have he := List.prefix_iff_eq_take.mp hcell
    rw [hlen] at he
    exact he.symm
  have hpH := hl p (by simp [hx])
  have hqH := hl q (by simp [hx])
  have hmH : ∀ y ∈ between, y.length = H := fun y hy => hl y (by simp [hx, hy])
  by_contra hneq
  have hpq : p ≠ q := by intro heq; subst q; exact hneq (hpa.symm.trans hqb)
  have hb := local_change_is_global_step initial H before between after (p.take c) p q
    hpH hqH hmH (List.take_prefix _ _) hcellq hbetween
    (by simpa only [List.append_assoc, List.singleton_append] using hx ▸ hn) hpq
  apply ha
  rw [← hm, hb]
  rfl

/-- The two rotated layout copies lie literally inside three original periods.
Thus every same-cell return in the layout has a genuine normalized history. -/
theorem cyclicLayout_return_word {H : Nat} {q : Gadget} {xs : List Key}
    (initial : Key → Bool)
    (hqs : q.split ∈ (DepthTree.midpoint 0 H (Nat.zero_le H)).nodes)
    (hql : q.owner.length = q.split.lo)
    (hl : OnLeaves H xs)
    (hn : Normalized initial H (xs ++ (xs ++ xs)))
    (layout : CyclicLayout (List.take (q.split.cut + 1))
      ((ownerWord q.owner xs).map (List.take (min (q.split.hi + 1) H)))) :
    ∀ (pre : List Key) (a : Key) (away : List Key) (b : Key) (post : List Key),
      ((layout.first :: layout.rest).map Block.word).flatten ++
        ((layout.first :: layout.rest).map Block.word).flatten =
          pre ++ a :: (away ++ b :: post) →
      a.take (q.split.cut + 1) = b.take (q.split.cut + 1) → away ≠ [] →
      (∀ y ∈ away, y.take (q.split.cut + 1) ≠ a.take (q.split.cut + 1)) → a = b := by
  intro pre a away b post hpair hab haw hout
  obtain ⟨_, hlo, hcut, hhi⟩ := DepthTree.node_bounds _ hqs
  have hl₃ : OnLeaves H (xs ++ (xs ++ xs)) := by
    intro y hy
    exact hl y (by simpa using hy)
  have hcopies : (ownerWord q.owner (xs ++ (xs ++ xs))).map
      (List.take (min (q.split.hi + 1) H)) =
      layout.cutBefore ++
        ((((layout.first :: layout.rest).map Block.word).flatten ++
          ((layout.first :: layout.rest).map Block.word).flatten) ++ layout.suffix) := by
    simp only [ownerWord_append, List.map_append]
    simp only [layout.rotation, layout.split, List.append_assoc]
  have hprojected : (ownerWord q.owner (xs ++ (xs ++ xs))).map
      (List.take (min (q.split.hi + 1) H)) =
      (layout.cutBefore ++ pre) ++ a :: (away ++ b :: (post ++ layout.suffix)) := by
    rw [hcopies, hpair]
    simp only [List.append_assoc, List.cons_append]
  exact projected_return initial (by omega) (by omega) (Nat.min_le_right _ _)
    hl₃ hn hprojected hab haw hout

/-- Full cyclic endpoint matching for the concrete gadget's actual fine-word
layout, derived from the original global normalized history. -/
theorem cyclicLayout_returnsMatch {H : Nat} {q : Gadget} {xs : List Key}
    (initial : Key → Bool)
    (hqs : q.split ∈ (DepthTree.midpoint 0 H (Nat.zero_le H)).nodes)
    (hql : q.owner.length = q.split.lo)
    (hl : OnLeaves H xs)
    (hn : Normalized initial H (xs ++ (xs ++ xs)))
    (layout : CyclicLayout (List.take (q.split.cut + 1))
      ((ownerWord q.owner xs).map (List.take (min (q.split.hi + 1) H)))) :
    ReturnsMatch (List.take (q.split.cut + 1)) (layout.first :: layout.rest) :=
  returnsMatch_of_returnWord _ _ _ layout.homogeneous layout.boundaries
    (cyclicLayout_return_word initial hqs hql hl hn layout)

end TangoSquared
