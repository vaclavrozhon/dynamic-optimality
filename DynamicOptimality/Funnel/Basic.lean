import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases

/-!
# Closed-rectangle funnels, with repeated keys

An occurrence is its time index, not its key. A restriction keeps a set of
occurrences and their original times. Thus two restrictions may have
overlapping key alphabets. `Visible` uses closed key intervals: an intervening
occurrence of either endpoint key blocks visibility.

`Switch` describes consecutive opposite-side members of the chronological
past funnel. Counting these triples is the switch convention without a
per-request baseline. `edgeCount` counts each empty rectangle once, toward
its later endpoint. No tree model or lower-bound assumption enters either
definition.
-/

namespace DynamicOptimality.Funnel

variable {α : Type*} [LinearOrder α] {m : Nat}

/-- Closed betweenness in key order, allowing either orientation. -/
def Between (a b x : α) : Prop :=
  (a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a)

instance (a b x : α) : Decidable (Between a b x) := inferInstanceAs
  (Decidable ((a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a)))

theorem between_comm (a b x : α) : Between a b x ↔ Between b a x := by
  exact or_comm

theorem Between.dual {a b x : α} (h : Between a b x) :
    Between (α := OrderDual α) a b x :=
  h.elim (fun hx => Or.inr ⟨hx.2,hx.1⟩) (fun hx => Or.inl ⟨hx.2,hx.1⟩)

theorem between_of_le {a b x : α} (h : a ≤ b) :
    Between a b x ↔ a ≤ x ∧ x ≤ b := by
  unfold Between
  constructor
  · rintro (hx | hx)
    · exact hx
    · exact ⟨h.trans hx.1, hx.2.trans h⟩
  · exact Or.inl

theorem between_iff_min_max (a b x : α) :
    Between a b x ↔ min a b ≤ x ∧ x ≤ max a b := by
  rcases le_total a b with h | h
  · simpa only [min_eq_left h,max_eq_right h] using (between_of_le h (x := x))
  · simpa only [min_eq_right h,max_eq_left h] using
      (between_comm a b x).trans (between_of_le h)

theorem between_left (a b : α) : Between a b a := by
  rcases le_total a b with h | h
  · exact Or.inl ⟨le_rfl,h⟩
  · exact Or.inr ⟨h,le_rfl⟩

theorem between_right (a b : α) : Between a b b := by
  exact (between_comm b a b).mp (between_left b a)

theorem Between.trans {a b x y z : α} (hx : Between a b x) (hy : Between a b y)
    (hz : Between x y z) : Between a b z := by
  rcases le_total a b with h | h
  · obtain ⟨ax,xb⟩ := (between_of_le h).mp hx
    obtain ⟨ay,yb⟩ := (between_of_le h).mp hy
    rcases hz with ⟨xz,zy⟩ | ⟨yz,zx⟩
    · exact Or.inl ⟨ax.trans xz,zy.trans yb⟩
    · exact Or.inl ⟨ay.trans yz,zx.trans xb⟩
  · obtain ⟨bx,xa⟩ := (between_of_le h).mp ((between_comm _ _ _).mp hx)
    obtain ⟨by',ya⟩ := (between_of_le h).mp ((between_comm _ _ _).mp hy)
    rcases hz with ⟨xz,zy⟩ | ⟨yz,zx⟩
    · exact Or.inr ⟨bx.trans xz,zy.trans ya⟩
    · exact Or.inr ⟨by'.trans yz,zx.trans xa⟩

/-- The earlier occurrence `q` sees `p` through an empty closed rectangle. -/
def Visible (word : Fin m → α) (active : Finset (Fin m)) (p q : Fin m) : Prop :=
  p ∈ active ∧ q ∈ active ∧ q < p ∧ word q ≠ word p ∧
    ∀ r ∈ active, q < r → r < p → ¬ Between (word q) (word p) (word r)

instance (word : Fin m → α) (active : Finset (Fin m)) (p q : Fin m) :
    Decidable (Visible word active p q) := by unfold Visible; infer_instance

/-- Two keys lie strictly on opposite sides of the current query. -/
def Opposite (x a b : α) : Prop := (a < x ∧ x < b) ∨ (b < x ∧ x < a)

instance (x a b : α) : Decidable (Opposite x a b) := by unfold Opposite; infer_instance

theorem Opposite.between {x a b : α} (h : Opposite x a b) : Between a b x :=
  h.elim (fun h => Or.inl ⟨h.1.le,h.2.le⟩) (fun h => Or.inr ⟨h.1.le,h.2.le⟩)

theorem Opposite.ne {x a b : α} (h : Opposite x a b) : a ≠ b := by
  rcases h with h | h
  · exact ne_of_lt (h.1.trans h.2)
  · exact ne_of_gt (h.1.trans h.2)

/-- One adjacent change of side in the chronological past funnel of `p`. -/
def Switch (word : Fin m → α) (active : Finset (Fin m)) (p q r : Fin m) : Prop :=
  Visible word active p q ∧ Visible word active p r ∧ q < r ∧
    Opposite (word p) (word q) (word r) ∧
    ∀ s ∈ active, q < s → s < r → ¬ Visible word active p s

instance (word : Fin m → α) (active : Finset (Fin m)) (p q r : Fin m) :
    Decidable (Switch word active p q r) := by unfold Switch; infer_instance

theorem Visible.dual {word : Fin m → α} {active : Finset (Fin m)}
    {p q : Fin m} (h : Visible word active p q) :
    Visible (α := OrderDual α) word active p q := by
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,?_⟩
  intro r hr qr rp between
  exact h.2.2.2.2 r hr qr rp between.dual

theorem Switch.dual {word : Fin m → α} {active : Finset (Fin m)}
    {p q r : Fin m} (h : Switch word active p q r) :
    Switch (α := OrderDual α) word active p q r := by
  refine ⟨h.1.dual,h.2.1.dual,h.2.2.1,?_,?_⟩
  · exact h.2.2.2.1.elim (fun sides => Or.inr ⟨sides.2,sides.1⟩)
      (fun sides => Or.inl ⟨sides.2,sides.1⟩)
  · intro s hs qs sr hvisible
    exact h.2.2.2.2 s hs qs sr hvisible.dual

def switches (word : Fin m → α) (active : Finset (Fin m)) :
    Finset (Fin m × Fin m × Fin m) :=
  Finset.univ.filter (fun t => Switch word active t.1 t.2.1 t.2.2)

def count (word : Fin m → α) (active : Finset (Fin m)) : Nat :=
  (switches word active).card

def edges (word : Fin m → α) (active : Finset (Fin m)) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun pair => Visible word active pair.2 pair.1)

def edgeCount (word : Fin m → α) (active : Finset (Fin m)) : Nat :=
  (edges word active).card

/-- Funnel switch count of an ordinary access word. Repeated keys are allowed. -/
def wordCount (word : List α) : Nat := count word.get Finset.univ

def wordEdgeCount (word : List α) : Nat := edgeCount word.get Finset.univ

@[simp] theorem mem_switches {word : Fin m → α} {active : Finset (Fin m)}
    {p q r : Fin m} :
    (p,q,r) ∈ switches word active ↔ Switch word active p q r := by
  simp [switches]

@[simp] theorem mem_edges {word : Fin m → α} {active : Finset (Fin m)}
    {p q : Fin m} : (q,p) ∈ edges word active ↔ Visible word active p q := by
  simp [edges]

theorem Visible.restrict {word : Fin m → α} {small large : Finset (Fin m)}
    {p q : Fin m} (visible : Visible word large p q) (subset : small ⊆ large)
    (hp : p ∈ small) (hq : q ∈ small) : Visible word small p q := by
  exact ⟨hp, hq, visible.2.2.1, visible.2.2.2.1,
    fun r hr => visible.2.2.2.2 r (subset hr)⟩

/-- Only the latest occurrence on a column can be visible from an apex. -/
theorem Visible.column_unique {word : Fin m → α} {active : Finset (Fin m)}
    {p q r : Fin m} (hq : Visible word active p q) (hr : Visible word active p r)
    (same : word q = word r) : q = r := by
  rcases lt_trichotomy q r with h | h | h
  · apply False.elim
    apply hq.2.2.2.2 r hr.2.1 h hr.2.2.1
    rcases le_total (word q) (word p) with h | h
    · exact Or.inl ⟨same.le,same.ge.trans h⟩
    · exact Or.inr ⟨h.trans same.le,same.ge⟩
  · exact h
  · apply False.elim
    apply hr.2.2.2.2 q hq.2.1 h hq.2.2.1
    rcases le_total (word r) (word p) with h | h
    · exact Or.inl ⟨same.ge,same.le.trans h⟩
    · exact Or.inr ⟨h.trans same.ge,same.le⟩

theorem Switch.next_unique {word : Fin m → α} {active : Finset (Fin m)}
    {p q r s : Fin m} (hr : Switch word active p q r)
    (hs : Switch word active p q s) : r = s := by
  rcases lt_trichotomy r s with h | h | h
  · exact False.elim (hs.2.2.2.2 r hr.2.1.2.1 hr.2.2.1 h hr.2.1)
  · exact h
  · exact False.elim (hr.2.2.2.2 s hs.2.1.2.1 hs.2.2.1 h hs.2.1)

theorem Switch.prev_unique {word : Fin m → α} {active : Finset (Fin m)}
    {p q r s : Fin m} (hq : Switch word active p q r)
    (hs : Switch word active p s r) : q = s := by
  rcases lt_trichotomy q s with h | h | h
  · exact False.elim (hq.2.2.2.2 s hs.1.2.1 h hs.2.2.1 hs.1)
  · exact h
  · exact False.elim (hs.2.2.2.2 q hq.1.2.1 h hq.2.2.1 hq.1)

/-- Every switch has a different first edge in its apex's past funnel. -/
theorem count_le_edgeCount (word : Fin m → α) (active : Finset (Fin m)) :
    count word active ≤ edgeCount word active := by
  unfold count edgeCount
  apply Finset.card_le_card_of_injOn (fun t => (t.2.1,t.1))
  · intro t ht
    exact mem_edges.mpr (mem_switches.mp ht).1
  · intro a ha b hb hab
    change (a.2.1,a.1) = (b.2.1,b.1) at hab
    have first : a.2.1 = b.2.1 := (Prod.mk.inj hab).1
    have apex : a.1 = b.1 := (Prod.mk.inj hab).2
    have later : a.2.2 = b.2.2 := by
      apply Switch.next_unique (mem_switches.mp ha)
      simpa only [apex, first] using mem_switches.mp hb
    exact Prod.ext apex (Prod.ext first later)

@[simp] theorem wordCount_nil : wordCount ([] : List α) = 0 := by
  simp [wordCount, count, switches]

end DynamicOptimality.Funnel
