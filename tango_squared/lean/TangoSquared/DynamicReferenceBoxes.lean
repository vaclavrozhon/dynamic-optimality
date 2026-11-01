import TangoSquared.Reference

/-!
# Rectangle certificates for changing ordered references

Permanent separators have time-varying subtree intervals and timestamps.
The certificate records the interval geometry and timestamp heap law of
an ordered reference, monotone separator timestamps, and original-query
writes. Every genuine flip then determines a box, and distinct flip boxes
are nonconflicting in the sense of the rectangle-cover lower bound.

This is an abstract, general certificate theorem. It does not yet build
the certificate from concrete reference-tree edits, formalize the
rectangle-cover theorem relating boxes to BST rotations, or connect
tertiary artificial probes to original-query witnesses.
-/

namespace TangoSquared.DynamicReferenceBoxes

variable {Key Sep : Type*} [LinearOrder Key]

/-- The divider lies strictly between the two endpoint keys. -/
def Spans (u v d : Key) : Prop := (u < d ∧ d < v) ∨ (v < d ∧ d < u)

theorem spans_symm {u v d : Key} : Spans u v d ↔ Spans v u d := or_comm

structure State (Key Sep : Type*) where
  lo : Sep → Key
  hi : Sep → Key
  stamp : Sep → Nat

def State.Contains (s : State Key Sep) (c : Sep) (x : Key) : Prop :=
  s.lo c ≤ x ∧ x ≤ s.hi c

/-- These are the ordered-subtree and timestamp-heap parts of the invariant.
The interior-divider law combines the fact that an interior separator is
a descendant with timestamp heap order. -/
structure Certificate (query : Nat → Key) (divider : Sep → Key)
    (state : Nat → State Key Sep) : Prop where
  no_mutual_interior : ∀ t c d, c ≠ d →
    ¬ ((state t).lo c < divider d ∧ divider d < (state t).hi c ∧
       (state t).lo d < divider c ∧ divider c < (state t).hi d)
  heap_interior : ∀ t c d,
    (state t).lo c < divider d → divider d < (state t).hi c →
    (state t).stamp d ≤ (state t).stamp c
  monotone_stamp : ∀ c, Monotone (fun t => (state t).stamp c)
  query_write : ∀ t c, (state t).Contains c (query t) →
    (state (t + 1)).stamp c = t

structure Event (Sep : Type*) where
  finish : Nat
  separator : Sep

def Event.start (state : Nat → State Key Sep) (e : Event Sep) : Nat :=
  (state e.finish).stamp e.separator

def Event.source (query : Nat → Key) (state : Nat → State Key Sep)
    (e : Event Sep) : Key := query (e.start state)

def Event.target (query : Nat → Key) (e : Event Sep) : Key := query e.finish

/-- First initialization changes have no preceding real witness and are
excluded by `earlier`. All endpoints below are original query keys. -/
structure Genuine (query : Nat → Key) (divider : Sep → Key)
    (state : Nat → State Key Sep) (e : Event Sep) : Prop where
  earlier : e.start state < e.finish
  source_mem : (state e.finish).Contains e.separator (e.source query state)
  target_mem : (state e.finish).Contains e.separator (e.target query)
  crosses : Spans (e.source query state) (e.target query) (divider e.separator)

def SameOrientation (query : Nat → Key) (state : Nat → State Key Sep)
    (e f : Event Sep) : Prop :=
  (e.source query state < e.target query ↔ f.source query state < f.target query)

/-- Closed temporal overlap and containment of both dividers in both key
spans. Strict key containment is appropriate because dividers are not keys. -/
def Conflict (query : Nat → Key) (divider : Sep → Key)
    (state : Nat → State Key Sep) (e f : Event Sep) : Prop :=
  SameOrientation query state e f ∧
  e.start state ≤ f.finish ∧ f.start state ≤ e.finish ∧
  Spans (e.source query state) (e.target query) (divider f.separator) ∧
  Spans (f.source query state) (f.target query) (divider e.separator)

theorem conflict_symm {query : Nat → Key} {divider : Sep → Key}
    {state : Nat → State Key Sep} {e f : Event Sep}
    (h : Conflict query divider state e f) : Conflict query divider state f e := by
  rcases h with ⟨ho, htime, htime', hspan, hspan'⟩
  exact ⟨ho.symm, htime', htime, hspan', hspan⟩

theorem spans_inside {s : State Key Sep} {c : Sep} {u v d : Key}
    (hu : s.Contains c u) (hv : s.Contains c v) (hd : Spans u v d) :
    s.lo c < d ∧ d < s.hi c := by
  rcases hd with ⟨hud, hdv⟩ | ⟨hvd, hdu⟩
  · exact ⟨lt_of_le_of_lt hu.1 hud, lt_of_lt_of_le hdv hv.2⟩
  · exact ⟨lt_of_le_of_lt hv.1 hvd, lt_of_lt_of_le hdu hu.2⟩

variable {query : Nat → Key} {divider : Sep → Key}
    {state : Nat → State Key Sep}

/-- The central temporal argument: once an earlier event has written its
timestamp, its divider cannot lie inside a later overlapping event's span. -/
theorem earlier_end_divider_excluded (cert : Certificate query divider state)
    {e f : Event Sep} (he : Genuine query divider state e)
    (hf : Genuine query divider state f) (hend : e.finish < f.finish)
    (hoverlap : f.start state < e.finish) :
    ¬ Spans (f.source query state) (f.target query) (divider e.separator) := by
  intro hspan
  obtain ⟨hlo, hhi⟩ := spans_inside hf.source_mem hf.target_mem hspan
  have hheap := cert.heap_interior f.finish f.separator e.separator hlo hhi
  have hmono := cert.monotone_stamp e.separator (show e.finish + 1 ≤ f.finish by omega)
  have hw := cert.query_write e.finish e.separator he.target_mem
  change (state (e.finish + 1)).stamp e.separator ≤
    (state f.finish).stamp e.separator at hmono
  rw [hw] at hmono
  change e.finish ≤ (state f.finish).stamp e.separator at hmono
  change (state f.finish).stamp e.separator ≤ f.start state at hheap
  omega

/-- Same-oriented boxes sharing only an ending/starting query cannot
contain each other's divider, even with closed temporal overlap. -/
theorem touching_nonconflict {e f : Event Sep}
    (he : Genuine query divider state e) (hf : Genuine query divider state f)
    (htouch : e.finish = f.start state) : ¬ Conflict query divider state e f := by
  intro hconf
  rcases hconf with ⟨horient, _, _, _, hspan⟩
  have hkey : e.target query = f.source query state := congrArg query htouch
  rcases he.crosses with ⟨hes, het⟩ | ⟨het, hes⟩
  · have heup : e.source query state < e.target query := lt_trans hes het
    have hfup : f.source query state < f.target query := horient.mp heup
    rcases hspan with ⟨hfs, _⟩ | ⟨hft, hfs⟩
    · exact (lt_irrefl _ (lt_trans het (hkey ▸ hfs)))
    · exact (not_lt_of_gt hfup (lt_trans hft hfs))
  · have hfnup : ¬ f.source query state < f.target query := by
      intro hup
      exact (not_lt_of_gt (lt_trans het hes)) (horient.mpr hup)
    rcases hf.crosses with ⟨hfs, hft⟩ | ⟨hft, hfs⟩
    · exact hfnup (lt_trans hfs hft)
    · rcases hspan with ⟨hfs', hft'⟩ | ⟨_, hfs'⟩
      · exact (not_lt_of_gt (lt_trans hft hfs)) (lt_trans hfs' hft')
      · exact (lt_irrefl _ (lt_trans (hkey ▸ het) hfs'))

theorem equal_end_nonconflict (cert : Certificate query divider state)
    {e f : Event Sep} (he : Genuine query divider state e)
    (hf : Genuine query divider state f) (hne : e ≠ f)
    (hend : e.finish = f.finish) : ¬ Conflict query divider state e f := by
  intro hconf
  have hsep : e.separator ≠ f.separator := by
    intro h
    apply hne
    cases e
    cases f
    simp_all
  obtain ⟨helo, hehi⟩ := spans_inside he.source_mem he.target_mem hconf.2.2.2.1
  obtain ⟨hflo, hfhi⟩ := spans_inside hf.source_mem hf.target_mem hconf.2.2.2.2
  rw [← hend] at hflo hfhi
  exact cert.no_mutual_interior e.finish e.separator f.separator hsep
    ⟨helo, hehi, hflo, hfhi⟩

/-- General nonconflict, including nested time intervals, equal starts,
equal finishes, touching times, and arbitrary allowed reference changes. -/
theorem genuine_events_nonconflicting (cert : Certificate query divider state)
    {e f : Event Sep} (he : Genuine query divider state e)
    (hf : Genuine query divider state f) (hne : e ≠ f) :
    ¬ Conflict query divider state e f := by
  intro hconf
  rcases lt_trichotomy e.finish f.finish with hlt | heq | hgt
  · rcases lt_or_eq_of_le hconf.2.2.1 with hbefore | htouch
    · exact earlier_end_divider_excluded cert he hf hlt hbefore hconf.2.2.2.2
    · exact touching_nonconflict he hf htouch.symm hconf
  · exact equal_end_nonconflict cert he hf hne heq hconf
  · have hconf' := conflict_symm hconf
    rcases lt_or_eq_of_le hconf'.2.2.1 with hbefore | htouch
    · exact earlier_end_divider_excluded cert hf he hgt hbefore hconf'.2.2.2.2
    · exact touching_nonconflict hf he htouch.symm hconf'

end TangoSquared.DynamicReferenceBoxes
