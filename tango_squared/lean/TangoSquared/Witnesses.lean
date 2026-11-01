import TangoSquared.Monotonicity
import TangoSquared.NormalizedWords
import TangoSquared.Recency
import TangoSquared.PrefixOrder
import Mathlib.Data.Finset.Sum

/-!
# Actual entry and delayed witness records

An event stores the source's occurrence in the actual query history and the
coarse/fine conditions that retain the record. Search-path membership and
uniqueness are derived below; they are not fields of an event.
-/

namespace TangoSquared.Witnesses

open Primary NormalizedWords

/-- Auxiliary terminal fragments are allowed in the cyclic potential telescope. -/
def Valid (H : Nat) (q : Gadget) : Prop :=
  q.split ∈ (DepthTree.midpoint 0 H (Nat.zero_le H)).nodes ∧ q.owner.length = q.split.lo

/-- An entry witness is the latest coarse-entry source. Every later owner-local
query before the first micro change remains in the initial fine cell. -/
structure EntryEvent (history : List Key) (x : Key) (q : Gadget) (source : Key) where
  before : List Key
  middle : List Key
  previous : Key
  history_eq : history = before ++ source :: (middle ++ [previous])
  owner_source : q.owner.IsPrefix source
  owner_target : q.owner.IsPrefix x
  owner_previous : q.owner.IsPrefix previous
  coarse_same : q.coarse previous = q.coarse x
  coarse_other : q.coarse source ≠ q.coarse x
  fine_change : q.fine previous ≠ q.fine x
  reversal : (source < x ∧ x < previous) ∨ (previous < x ∧ x < source)
  first_fine : ∀ z ∈ middle ++ [previous],
    q.owner.IsPrefix z → q.fine z = q.fine previous

/-- A delayed event retains the latest globally consecutive fine change until
the first exit on its opposite side. Owner-local accesses in the meantime are
in the new fine cell or outside the coarse cell on the original micro side. -/
structure DelayedEvent (history : List Key) (x : Key) (q : Gadget) (source : Key) where
  before : List Key
  later : List Key
  next : Key
  history_eq : history = before ++ source :: next :: later
  owner_source : q.owner.IsPrefix source
  owner_target : q.owner.IsPrefix x
  owner_next : q.owner.IsPrefix next
  coarse_same : q.coarse source = q.coarse next
  coarse_other : q.coarse source ≠ q.coarse x
  fine_change : q.fine source ≠ q.fine next
  reversal : (x < source ∧ source < next) ∨ (next < source ∧ source < x)
  retained : ∀ z ∈ next :: later, q.owner.IsPrefix z →
    q.fine z = q.fine next ∨
      (q.coarse z ≠ q.coarse source ∧
        ((source < next ∧ source < z) ∨ (next < source ∧ z < source)))

/-- Equal prefix cells preserve every strict comparison with a different cell. -/
theorem lt_of_take_eq {p z x : Key} {d : Nat}
    (heq : z.take d = p.take d) (hne : p.take d ≠ x.take d) (hlt : p < x) : z < x := by
  by_contra hn
  have hp := take_mono_lex (le_of_lt hlt) d
  have hz := take_mono_lex (le_of_not_gt hn) d
  rw [heq] at hz
  exact hne (le_antisymm hp hz)

theorem gt_of_take_eq {p z x : Key} {d : Nat}
    (heq : z.take d = p.take d) (hne : p.take d ≠ x.take d) (hlt : x < p) : x < z := by
  by_contra hn
  have hp := take_mono_lex (le_of_lt hlt) d
  have hz := take_mono_lex (le_of_not_gt hn) d
  rw [heq] at hz
  exact hne (le_antisymm hz hp)

/-- No query outside an owner can lie between two keys inside it. -/
theorem outside_owner_interval {u x y z : Key}
    (hx : u.IsPrefix x) (hy : u.IsPrefix y) (hz : ¬ u.IsPrefix z) :
    ¬ MTR.Tree.InInterval (min x y) (max x y) z := by
  intro hin
  rcases le_total x y with hxy | hyx
  · have hlo : x ≤ z := by simpa [min_eq_left hxy] using hin.1
    have hhi : z ≤ y := by simpa [max_eq_right hxy] using hin.2
    exact hz (prefix_convex hx hy hlo hhi)
  · have hlo : y ≤ z := by simpa [min_eq_right hyx] using hin.1
    have hhi : z ≤ x := by simpa [max_eq_left hyx] using hin.2
    exact hz (prefix_convex hy hx hlo hhi)

/-- The entry record's history conditions exclude every later query from the
closed interval between its source and the current request. -/
theorem EntryEvent.interval_empty {history : List Key} {x y : Key} {q : Gadget}
    (e : EntryEvent history x q y) :
    ∀ z ∈ e.middle ++ [e.previous],
      ¬ MTR.Tree.InInterval (min x y) (max x y) z := by
  intro z hz
  by_cases howner : q.owner.IsPrefix z
  · have hf := e.first_fine z hz howner
    rcases e.reversal with ⟨hyx, hxp⟩ | ⟨hpx, hxy⟩
    · have hxz : x < z := gt_of_take_eq hf e.fine_change hxp
      intro hin
      have hzx : z ≤ x := by simpa [max_eq_left (le_of_lt hyx)] using hin.2
      exact (not_lt_of_ge hzx) hxz
    · have hzx : z < x := lt_of_take_eq hf e.fine_change hpx
      intro hin
      have hxz : x ≤ z := by simpa [min_eq_left (le_of_lt hxy)] using hin.1
      exact (not_lt_of_ge hxz) hzx
  · exact outside_owner_interval e.owner_target e.owner_source howner

/-- The delayed record's retention and first-opposite-exit conditions imply
exactly the interval exclusion used by actual MTR recency. -/
theorem DelayedEvent.interval_empty {history : List Key} {x y : Key} {q : Gadget}
    (e : DelayedEvent history x q y) :
    ∀ z ∈ e.next :: e.later,
      ¬ MTR.Tree.InInterval (min x y) (max x y) z := by
  intro z hz
  by_cases howner : q.owner.IsPrefix z
  · rcases e.retained z hz howner with hf | ⟨_, hside⟩
    · rcases e.reversal with ⟨hxy, hyp⟩ | ⟨hpy, hyx⟩
      · have hyz : y < z := gt_of_take_eq hf (Ne.symm e.fine_change) hyp
        intro hin
        have hzy : z ≤ y := by simpa [max_eq_right (le_of_lt hxy)] using hin.2
        exact (not_lt_of_ge hzy) hyz
      · have hzy : z < y := lt_of_take_eq hf (Ne.symm e.fine_change) hpy
        intro hin
        have hyz : y ≤ z := by simpa [min_eq_right (le_of_lt hyx)] using hin.1
        exact (not_lt_of_ge hyz) hzy
    · rcases e.reversal with ⟨hxy, hyp⟩ | ⟨hpy, hyx⟩
      · have hyz : y < z := by rcases hside with h | h; exact h.2; exact (not_lt_of_gt hyp h.1).elim
        intro hin
        have hzy : z ≤ y := by simpa [max_eq_right (le_of_lt hxy)] using hin.2
        exact (not_lt_of_ge hzy) hyz
      · have hzy : z < y := by rcases hside with h | h; exact (not_lt_of_gt hpy h.1).elim; exact h.2
        intro hin
        have hyz : y ≤ z := by simpa [min_eq_right (le_of_lt hyx)] using hin.1
        exact (not_lt_of_ge hyz) hzy
  · exact outside_owner_interval e.owner_target e.owner_source howner

/-- The source of a delayed record is its latest occurrence in the history. -/
theorem DelayedEvent.source_not_later {history : List Key} {x y : Key} {q : Gadget}
    (e : DelayedEvent history x q y) : y ∉ e.next :: e.later := by
  intro hy
  exact e.interval_empty y hy ⟨min_le_right _ _, le_max_right _ _⟩

/-- A last-occurrence decomposition has a unique suffix. -/
theorem last_source_suffix_unique {α : Type*} (y : α)
    (before₁ before₂ after₁ after₂ : List α)
    (heq : before₁ ++ y :: after₁ = before₂ ++ y :: after₂)
    (hn₁ : y ∉ after₁) (hn₂ : y ∉ after₂) : after₁ = after₂ := by
  induction before₁ generalizing before₂ with
  | nil =>
    cases before₂ with
    | nil => exact (List.cons.inj heq).2
    | cons b bs =>
      have ht : after₁ = bs ++ y :: after₂ := (List.cons.inj heq).2
      apply False.elim
      apply hn₁
      rw [ht]
      simp
  | cons a as ih =>
    cases before₂ with
    | nil =>
      have ht : as ++ y :: after₁ = after₂ := (List.cons.inj heq).2
      apply False.elim
      apply hn₂
      rw [← ht]
      simp
    | cons b bs => exact ih bs (List.cons.inj heq).2

/-- Two delayed records using the same witness have the same source successor. -/
theorem DelayedEvent.next_unique {history : List Key} {x y : Key} {q r : Gadget}
    (e : DelayedEvent history x q y) (f : DelayedEvent history x r y) : e.next = f.next := by
  have h := last_source_suffix_unique y e.before f.before (e.next :: e.later)
    (f.next :: f.later) (e.history_eq.symm.trans f.history_eq)
    e.source_not_later f.source_not_later
  exact (List.cons.inj h).1

/-- The previous global query is independent of the entry gadget. -/
theorem EntryEvent.previous_unique {history : List Key} {x y : Key} {q r : Gadget}
    (e : EntryEvent history x q y) (f : EntryEvent history x r y) :
    e.previous = f.previous := by
  have hlast := congrArg List.getLast? (e.history_eq.symm.trans f.history_eq)
  simpa only [← List.cons_append, ← List.append_assoc, List.getLast?_concat,
    Option.some.injEq] using hlast

/-- Successful actual executions split at every prefix. -/
theorem successful_history_append {α : Type*} [LinearOrder α] (t : MTR.Tree α)
    (before after : List α) :
    MTR.Tree.Successful t (before ++ after) ↔
      MTR.Tree.Successful t before ∧ MTR.Tree.Successful (MTR.run t before) after := by
  induction before generalizing t with
  | nil => simp [MTR.Tree.Successful, MTR.run]
  | cons a as ih =>
    simp only [List.cons_append, MTR.Tree.Successful]
    rw [ih]
    simp [MTR.run, and_assoc]

/-- Put the actual recency theorem after an arbitrary earlier execution prefix. -/
theorem source_interval_internal (t : MTR.Tree Key) (history before after : List Key)
    (x y : Key) (heq : history = before ++ y :: after) (hnonempty : after ≠ [])
    (success : MTR.Tree.Successful t history)
    (target_success : ∃ d, MTR.Tree.searchDepth x (MTR.run t history) = some d)
    (different : x ≠ y)
    (outside : ∀ z ∈ after, ¬ MTR.Tree.InInterval (min x y) (max x y) z) :
    y ∈ MTR.Tree.internalSearchPath x (MTR.run t history) := by
  subst history
  obtain ⟨_, hs⟩ := (successful_history_append t before (y :: after)).1 success
  cases after with
  | nil => exact (hnonempty rfl).elim
  | cons p later =>
    have hrun : MTR.run t (before ++ y :: p :: later) =
        MTR.run (MTR.run t before) (y :: p :: later) := by
      simp [MTR.run, List.foldl_append]
    rw [hrun] at target_success ⊢
    exact MTR.Tree.last_interval_query_internal (min x y) (max x y) x y p
      (MTR.run t before) later hs target_success
      ⟨min_le_right _ _, le_max_right _ _⟩ ⟨min_le_left _ _, le_max_left _ _⟩
      different outside

/-- Every entry witness occupies an actual internal search-path slot. -/
theorem EntryEvent.internal_visit {history : List Key} {x y : Key} {q : Gadget}
    (e : EntryEvent history x q y) (t : MTR.Tree Key)
    (success : MTR.Tree.Successful t history)
    (target_success : ∃ d, MTR.Tree.searchDepth x (MTR.run t history) = some d) :
    y ∈ MTR.Tree.internalSearchPath x (MTR.run t history) := by
  apply source_interval_internal t history e.before (e.middle ++ [e.previous]) x y
    e.history_eq (by simp) success target_success _ e.interval_empty
  rcases e.reversal with h | h
  · exact Ne.symm (ne_of_lt h.1)
  · exact ne_of_lt h.2

/-- Every delayed witness occupies an actual internal search-path slot. -/
theorem DelayedEvent.internal_visit {history : List Key} {x y : Key} {q : Gadget}
    (e : DelayedEvent history x q y) (t : MTR.Tree Key)
    (success : MTR.Tree.Successful t history)
    (target_success : ∃ d, MTR.Tree.searchDepth x (MTR.run t history) = some d) :
    y ∈ MTR.Tree.internalSearchPath x (MTR.run t history) := by
  apply source_interval_internal t history e.before (e.next :: e.later) x y
    e.history_eq (by simp) success target_success _ e.interval_empty
  rcases e.reversal with h | h
  · exact ne_of_lt h.1
  · exact Ne.symm (ne_of_lt h.2)

/-- Actual coarse and fine changes locate the unique secondary split. Terminal
auxiliary splits are included; their fine prefixes are already entire leaves. -/
theorem separates_of_changes {H : Nat} {q : Gadget} (hq : Valid H q)
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

/-- A shared target and shared separating depth pair uniquely identify a gadget. -/
theorem gadget_unique_of_separates {H : Nat} {q r : Gadget} {x : Key} {e f : Nat}
    (hq : Valid H q) (hr : Valid H r) (hxq : q.owner.IsPrefix x) (hxr : r.owner.IsPrefix x)
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

/-- The source-to-target macro LCA and first micro LCA separate at this entry gadget. -/
theorem EntryEvent.separated {H : Nat} {history : List Key} {x y : Key} {q : Gadget}
    (e : EntryEvent history x q y) (hq : Valid H q) (hleaves : OnLeaves H (history ++ [x])) :
    q.split.Separates (lcaDepth y x) (lcaDepth e.previous x) := by
  have hyH : y.length = H := hleaves y (by simp [e.history_eq])
  have hxH : x.length = H := hleaves x (by simp)
  have hpH : e.previous.length = H := hleaves e.previous (by simp [e.history_eq])
  exact separates_of_changes hq hyH hxH hpH hxH e.owner_source e.owner_target
    e.coarse_other e.coarse_same e.fine_change

/-- The macro trigger and source micro step separate at this delayed gadget. -/
theorem DelayedEvent.separated {H : Nat} {history : List Key} {x y : Key} {q : Gadget}
    (e : DelayedEvent history x q y) (hq : Valid H q) (hleaves : OnLeaves H (history ++ [x])) :
    q.split.Separates (lcaDepth y x) (lcaDepth y e.next) := by
  have hyH : y.length = H := hleaves y (by simp [e.history_eq])
  have hxH : x.length = H := hleaves x (by simp)
  have hpH : e.next.length = H := hleaves e.next (by simp [e.history_eq])
  exact separates_of_changes hq hyH hxH hyH hpH e.owner_source e.owner_target
    e.coarse_other e.coarse_same e.fine_change

/-- Distinct entry gadgets cannot use the same visited witness key at one query. -/
theorem EntryEvent.gadget_unique {H : Nat} {history : List Key} {x y : Key} {q r : Gadget}
    (e : EntryEvent history x q y) (f : EntryEvent history x r y)
    (hq : Valid H q) (hr : Valid H r) (hleaves : OnLeaves H (history ++ [x])) : q = r := by
  have hs := f.separated hr hleaves
  rw [← e.previous_unique f] at hs
  exact gadget_unique_of_separates hq hr e.owner_target f.owner_target (e.separated hq hleaves) hs

/-- Distinct delayed gadgets cannot use the same visited witness key at one query. -/
theorem DelayedEvent.gadget_unique {H : Nat} {history : List Key} {x y : Key} {q r : Gadget}
    (e : DelayedEvent history x q y) (f : DelayedEvent history x r y)
    (hq : Valid H q) (hr : Valid H r) (hleaves : OnLeaves H (history ++ [x])) : q = r := by
  have hs := f.separated hr hleaves
  rw [← e.next_unique f] at hs
  exact gadget_unique_of_separates hq hr e.owner_target f.owner_target (e.separated hq hleaves) hs

/-- Agreement on a prefix below a node determines the same visited child. -/
theorem branch_eq_of_take_eq {u p z : Key} {d : Nat} {a : Bool}
    (hdepth : u.length < d) (heq : p.take d = z.take d)
    (hp : branch u p = some a) : branch u z = some a := by
  have hup := prefix_of_branch_some hp
  have htake := congrArg (fun word : Key => word.take u.length) heq
  simp only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hdepth)] at htake
  have huz : u.IsPrefix z := List.prefix_iff_eq_take.mpr
    ((List.prefix_iff_eq_take.mp hup).trans htake)
  have hbits := congrArg (fun word : Key => word[u.length]?) heq
  simp only [List.getElem?_take_of_lt hdepth] at hbits
  simp only [branch, if_pos hup] at hp
  simp only [branch, if_pos huz]
  exact hbits.symm.trans hp

/-- Every key in the left child precedes every same-depth key in the right child. -/
theorem branch_false_lt_true {u z y : Key} (hlen : z.length = y.length)
    (hz : branch u z = some false) (hy : branch u y = some true) : z < y := by
  by_contra hn
  rcases lt_or_eq_of_le (le_of_not_gt hn) with hlt | heq
  · have hu := owner_eq_lcaNode_of_branch_ne hy hz (by decide)
    have hbits := (branches_lca_of_lt hlt hlen.symm).1
    rw [← hu, hy] at hbits
    contradiction
  · subst y
    rw [hz] at hy
    contradiction

/-- Moving farther right from a right-child key cannot enter the left child. -/
theorem branch_stays_right {u y z : Key} (hlen : z.length = y.length)
    (hy : branch u y = some true) (hyz : y < z) :
    branch u z = none ∨ branch u z = some true := by
  cases h : branch u z with
  | none => exact Or.inl rfl
  | some b =>
    cases b with
    | true => exact Or.inr rfl
    | false => exact (not_lt_of_gt hyz (branch_false_lt_true hlen h hy)).elim

/-- Moving farther left from a left-child key cannot enter the right child. -/
theorem branch_stays_left {u y z : Key} (hlen : z.length = y.length)
    (hy : branch u y = some false) (hzy : z < y) :
    branch u z = none ∨ branch u z = some false := by
  cases h : branch u z with
  | none => exact Or.inl rfl
  | some b =>
    cases b with
    | false => exact Or.inr rfl
    | true => exact (not_lt_of_gt hzy (branch_false_lt_true hlen.symm hy h)).elim

/-- Retention of a delayed record preserves the source-side preference at its
macro LCA. This is derived from actual history updates and retained cells. -/
theorem DelayedEvent.preference_retained {H : Nat} {history : List Key} {x y : Key} {q : Gadget}
    (e : DelayedEvent history x q y) (hq : Valid H q) (hleaves : OnLeaves H (history ++ [x]))
    (initial : Key → Bool) {a : Bool}
    (hsource : branch (lcaNode y x) y = some a)
    (hside : ∀ z, z.length = H →
      ((y < e.next ∧ y < z) ∨ (e.next < y ∧ z < y)) →
      branch (lcaNode y x) z = none ∨ branch (lcaNode y x) z = some a) :
    preference initial history (lcaNode y x) = a := by
  have hsep := e.separated hq hleaves
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

/-- The first opposite-side delayed trigger changes its macro-LCA preference. -/
theorem DelayedEvent.flips_lca {H : Nat} {history : List Key} {x y : Key} {q : Gadget}
    (e : DelayedEvent history x q y) (hq : Valid H q) (hleaves : OnLeaves H (history ++ [x]))
    (initial : Key → Bool) : Flips initial history x (lcaNode y x) := by
  have hyH : y.length = H := hleaves y (by simp [e.history_eq])
  have hxH : x.length = H := hleaves x (by simp)
  rcases e.reversal with ⟨hxy, hyp⟩ | ⟨hpy, hyx⟩
  · obtain ⟨hxf, hyt⟩ := branches_lca_of_lt hxy (hxH.trans hyH.symm)
    rw [lcaNode_comm x y] at hxf hyt
    have hpref : preference initial history (lcaNode y x) = true := by
      apply e.preference_retained hq hleaves initial hyt
      intro z hz hside
      apply branch_stays_right (hz.trans hyH.symm) hyt
      rcases hside with h | h
      · exact h.2
      · exact (not_lt_of_gt hyp h.1).elim
    exact ⟨false, hxf, by simp [hpref]⟩
  · obtain ⟨hyf, hxt⟩ := branches_lca_of_lt hyx (hyH.trans hxH.symm)
    have hpref : preference initial history (lcaNode y x) = false := by
      apply e.preference_retained hq hleaves initial hyf
      intro z hz hside
      apply branch_stays_left (hz.trans hyH.symm) hyf
      rcases hside with h | h
      · exact (not_lt_of_gt hpy h.1).elim
      · exact h.2
    exact ⟨true, hxt, by simp [hpref]⟩

/-- Entry and delayed events cannot use the same physical witness at one
normalized query: their required changed primary nodes have different depths. -/
theorem entry_delayed_disjoint {H : Nat} {history : List Key} {x y : Key} {q r : Gadget}
    (e : EntryEvent history x q y) (f : DelayedEvent history x r y)
    (hq : Valid H q) (hr : Valid H r) (hleaves : OnLeaves H (history ++ [x]))
    (initial : Key → Bool) (hone : OneFlip initial H history x) : False := by
  have hsep := e.separated hq hleaves
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
  have hf_flip := f.flips_lca hr hleaves initial
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

/-- Entry events are indexed by a gadget; delayed records additionally need the
coarse cell whose last micro step is retained. -/
abbrev EventTag := Gadget ⊕ (Gadget × Key)

def EventTag.gadget : EventTag → Gadget
  | .inl q => q
  | .inr (q, _) => q

/-- An actual event record supplying the named physical witness. -/
def EventRecord (history : List Key) (x : Key) (tag : EventTag) (y : Key) : Prop :=
  match tag with
  | .inl q => Nonempty (EntryEvent history x q y)
  | .inr (q, cell) => q.coarse y = cell ∧ Nonempty (DelayedEvent history x q y)

/-- Shared physical witnesses identify the entire event tag, including its class
and retained coarse cell. This is the joint injection used in the lower bound. -/
theorem event_tag_unique {H : Nat} {history : List Key} {x y : Key}
    {tag₁ tag₂ : EventTag}
    (hvalid₁ : Valid H tag₁.gadget) (hvalid₂ : Valid H tag₂.gadget)
    (hrecord₁ : EventRecord history x tag₁ y) (hrecord₂ : EventRecord history x tag₂ y)
    (hleaves : OnLeaves H (history ++ [x])) (initial : Key → Bool)
    (hone : OneFlip initial H history x) : tag₁ = tag₂ := by
  cases tag₁ with
  | inl q =>
    cases tag₂ with
    | inl r =>
      obtain ⟨e⟩ := hrecord₁
      obtain ⟨f⟩ := hrecord₂
      exact congrArg Sum.inl (e.gadget_unique f hvalid₁ hvalid₂ hleaves)
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
      have hq := e.gadget_unique f hvalid₁ hvalid₂ hleaves
      subst r
      have hcell : cell = other := hc.symm.trans ho
      exact congrArg Sum.inr (Prod.ext rfl hcell)

/-- Every actual event record supplies an internal search-path witness. -/
theorem event_record_internal {history : List Key} {x y : Key} {tag : EventTag}
    (record : EventRecord history x tag y) (t : MTR.Tree Key)
    (success : MTR.Tree.Successful t history)
    (target_success : ∃ d, MTR.Tree.searchDepth x (MTR.run t history) = some d) :
    y ∈ MTR.Tree.internalSearchPath x (MTR.run t history) := by
  cases tag with
  | inl q => obtain ⟨e⟩ := record; exact e.internal_visit t success target_success
  | inr pair =>
    obtain ⟨q, cell⟩ := pair
    obtain ⟨_, ⟨e⟩⟩ := record
    exact e.internal_visit t success target_success

/-- Joint entry/delayed accounting against the actual MTR depth at one query.
No injection or search-path membership is assumed: both are derived from the
concrete records and the concrete one-flip history property. -/
theorem joint_internal_budget {H : Nat} {history : List Key} {x : Key}
    (tags : Finset EventTag) (witness : EventTag → Key)
    (valid : ∀ tag ∈ tags, Valid H tag.gadget)
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

/-- A finite candidate universe contains every coarse prefix at depth at most H. -/
def eventCandidates (H : Nat) (qs : Finset Gadget) : Finset EventTag :=
  qs.disjSum (qs ×ˢ owners (H + 1))

/-- All actual record events at this query; witnesses are not supplied externally. -/
noncomputable def activeEvents (H : Nat) (qs : Finset Gadget)
    (history : List Key) (x : Key) : Finset EventTag := by
  classical
  exact (eventCandidates H qs).filter (fun tag => ∃ y, EventRecord history x tag y)

/-- The budget also applies directly to the complete set of active records. -/
theorem activeEvents_budget {H : Nat} {history : List Key} {x : Key}
    (qs : Finset Gadget) (valid : ∀ q ∈ qs, Valid H q)
    (hleaves : OnLeaves H (history ++ [x])) (initial : Key → Bool)
    (hone : OneFlip initial H history x) (t : MTR.Tree Key)
    (success : MTR.Tree.Successful t history) (depth : Nat)
    (target_success : MTR.Tree.searchDepth x (MTR.run t history) = some depth) :
    (activeEvents H qs history x).card ≤ depth - 1 := by
  classical
  let witness : EventTag → Key := fun tag =>
    if h : ∃ y, EventRecord history x tag y then Classical.choose h else []
  apply joint_internal_budget (activeEvents H qs history x) witness _ _
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

/-- Every entry record of a listed gadget belongs to the complete active set. -/
theorem entry_mem_activeEvents {H : Nat} {qs : Finset Gadget} {history : List Key}
    {x y : Key} {q : Gadget} (hq : q ∈ qs) (e : EntryEvent history x q y) :
    Sum.inl q ∈ activeEvents H qs history x := by
  classical
  apply Finset.mem_filter.mpr
  exact ⟨by simpa [eventCandidates] using hq, y, ⟨e⟩⟩

/-- Every retained coarse-cell record of a listed gadget belongs to the active
set; its source occurrence supplies the required bounded-depth coarse prefix. -/
theorem delayed_mem_activeEvents {H : Nat} {qs : Finset Gadget} {history : List Key}
    {x y : Key} {q : Gadget} (hq : q ∈ qs) (e : DelayedEvent history x q y)
    (hleaves : OnLeaves H (history ++ [x])) :
    Sum.inr (q, q.coarse y) ∈ activeEvents H qs history x := by
  classical
  have hyH : y.length = H := hleaves y (by simp [e.history_eq])
  have hcell : q.coarse y ∈ owners (H + 1) := by
    apply (mem_owners _ _).2
    change (y.take (q.split.cut + 1)).length < H + 1
    simp only [List.length_take]
    have hlen := Nat.min_le_right (q.split.cut + 1) y.length
    omega
  apply Finset.mem_filter.mpr
  exact ⟨by simp [eventCandidates, hq, hcell], y, rfl, ⟨e⟩⟩

end TangoSquared.Witnesses
