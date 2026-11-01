import Mathlib

/-!
Shrinking block families are represented by finite collections of finite
member sets. Splits, deletions, and transfers refine this partition: they
never merge blocks or introduce a new family member. A complete phase
collapses a processed source block to singleton descendants.
-/
namespace GreedyForest

variable {Record : Type*}

abbrev Family (Record : Type*) := Finset (Finset Record)

def Refines (after before : Family Record) : Prop :=
  ∀ b ∈ after, ∃ a ∈ before, b ⊆ a

def Partitioned (blocks : Family Record) : Prop :=
  ∀ a ∈ blocks, ∀ b ∈ blocks, ∀ v ∈ a, v ∈ b → a = b

def Isolated (v : Record) (blocks : Family Record) : Prop :=
  ∀ b ∈ blocks, v ∈ b → b ⊆ {v}

theorem isolated_of_refines (v : Record) (before after : Family Record)
    (href : Refines after before) (hiso : Isolated v before) :
    Isolated v after := by
  intro b hb hv
  obtain ⟨a, ha, hba⟩ := href b hb
  exact hba.trans (hiso a ha (hba hv))

/-- Every final block comes from one original block. Descendants of the
processed source have cardinality at most one. Other blocks may also have
been split or shrunk. -/
def Collapses (source : Finset Record) (before after : Family Record) : Prop :=
  ∀ b ∈ after, ∃ a ∈ before, b ⊆ a ∧ (a = source → b.card ≤ 1)

theorem collapse_refines (source : Finset Record) (before after : Family Record)
    (h : Collapses source before after) : Refines after before := by
  intro b hb
  obtain ⟨a, ha, hba, _⟩ := h b hb
  exact ⟨a, ha, hba⟩

/-- Complete consolidation permanently isolates each surviving member
of its source block. This derives the key lifetime fact from partition and
collapse conditions, rather than assuming a global bound on future wins. -/
theorem isolated_after_collapse (v : Record) (source : Finset Record)
    (before after : Family Record) (hp : Partitioned before)
    (hs : source ∈ before) (hv : v ∈ source)
    (hc : Collapses source before after) : Isolated v after := by
  intro b hb hvb
  obtain ⟨a, ha, hba, hsmall⟩ := hc b hb
  have heq : a = source := hp a ha source hs v (hba hvb) hv
  have hcard := hsmall heq
  intro w hw
  have hwv : w = v := Finset.card_le_one.mp hcard w hw v hvb
  simp [hwv]

def runActivity : List (Family Record × ℕ) → ℕ
  | [] => 0
  | (_, wins) :: rest => wins + runActivity rest

/-- Local post-conversion history conditions. A positive internal-win
phase is permitted only before isolation, has bounded phase degree, and
collapses the unique source containing the winner. -/
def ValidFamilyRun (v : Record) (D : ℕ) (before : Family Record) :
    List (Family Record × ℕ) → Prop
  | [] => True
  | (after, wins) :: rest =>
      Partitioned before ∧ Refines after before ∧ wins ≤ D ∧
      (0 < wins → ¬ Isolated v before ∧
        ∃ source ∈ before, v ∈ source ∧ Collapses source before after) ∧
      ValidFamilyRun v D after rest

theorem isolated_run_activity_eq_zero (v : Record) (D : ℕ)
    (before : Family Record) (steps : List (Family Record × ℕ))
    (hiso : Isolated v before) (hvalid : ValidFamilyRun v D before steps) :
    runActivity steps = 0 := by
  induction steps generalizing before with
  | nil => rfl
  | cons step rest ih =>
      rcases step with ⟨after, wins⟩
      rcases hvalid with ⟨_, href, _, hpositive, htail⟩
      have hw : wins = 0 := by
        by_contra hn
        have hp : 0 < wins := Nat.pos_of_ne_zero hn
        exact (hpositive hp).1 hiso
      have ha := isolated_of_refines v before after href hiso
      have hrest := ih after ha htail
      simp [runActivity, hw, hrest]

/-- A member wins at most one phase's degree bound over its entire
shrinking family lifetime, despite arbitrarily many splits and transfers. -/
theorem family_activity_le_degree (v : Record) (D : ℕ)
    (before : Family Record) (steps : List (Family Record × ℕ))
    (hvalid : ValidFamilyRun v D before steps) : runActivity steps ≤ D := by
  induction steps generalizing before with
  | nil => simp [runActivity]
  | cons step rest ih =>
      rcases step with ⟨after, wins⟩
      rcases hvalid with ⟨hpartition, href, hwD, hpositive, htail⟩
      by_cases hw : wins = 0
      · have hrest := ih after htail
        simpa [runActivity, hw] using hrest
      · have hp : 0 < wins := Nat.pos_of_ne_zero hw
        obtain ⟨_, source, hs, hv, hc⟩ := hpositive hp
        have hiso := isolated_after_collapse v source before after hpartition hs hv hc
        have hrest := isolated_run_activity_eq_zero v D after rest hiso htail
        simpa [runActivity, hrest] using hwD

def Straddles (side : Record → Bool) (block : Finset Record) : Prop :=
  ∃ v ∈ block, ∃ w ∈ block, side v ≠ side w

def CutSeparated (side : Record → Bool) (blocks : Family Record) : Prop :=
  ∀ b ∈ blocks, ¬ Straddles side b

def UniqueStraddler (side : Record → Bool) (blocks : Family Record) : Prop :=
  ∀ a ∈ blocks, ∀ b ∈ blocks, Straddles side a → Straddles side b → a = b

theorem straddles_of_subset (side : Record → Bool) (a b : Finset Record)
    (hab : a ⊆ b) (ha : Straddles side a) : Straddles side b := by
  obtain ⟨v, hv, w, hw, hne⟩ := ha
  exact ⟨v, hab hv, w, hab hw, hne⟩

theorem not_straddles_small (side : Record → Bool) (a : Finset Record)
    (ha : a.card ≤ 1) : ¬ Straddles side a := by
  rintro ⟨v, hv, w, hw, hne⟩
  have heq : v = w := Finset.card_le_one.mp ha v hv w hw
  exact hne (congrArg side heq)

theorem cutSeparated_of_refines (side : Record → Bool) (before after : Family Record)
    (href : Refines after before) (hsep : CutSeparated side before) :
    CutSeparated side after := by
  intro b hb hstrad
  obtain ⟨a, ha, hba⟩ := href b hb
  exact hsep a ha (straddles_of_subset side b a hba hstrad)

/-- One spatial cut has at most one straddling split descendant. A
complete phase on it eliminates every possible future internal crossing. -/
theorem cutSeparated_after_collapse (side : Record → Bool) (source : Finset Record)
    (before after : Family Record) (hu : UniqueStraddler side before)
    (hs : source ∈ before) (hstrad : Straddles side source)
    (hc : Collapses source before after) : CutSeparated side after := by
  intro b hb hbstrad
  obtain ⟨a, ha, hba, hsmall⟩ := hc b hb
  have hastrad := straddles_of_subset side b a hba hbstrad
  have heq : a = source := hu a ha source hs hastrad hstrad
  exact not_straddles_small side b (hsmall heq) hbstrad

def ValidCutRun (side : Record → Bool) (capacity : ℕ) (before : Family Record) :
    List (Family Record × ℕ) → Prop
  | [] => True
  | (after, crossings) :: rest =>
      UniqueStraddler side before ∧ Refines after before ∧ crossings ≤ capacity ∧
      (0 < crossings → ∃ source ∈ before,
        Straddles side source ∧ Collapses source before after) ∧
      ValidCutRun side capacity after rest

theorem cutSeparated_run_activity_eq_zero (side : Record → Bool) (capacity : ℕ)
    (before : Family Record) (steps : List (Family Record × ℕ))
    (hsep : CutSeparated side before) (hvalid : ValidCutRun side capacity before steps) :
    runActivity steps = 0 := by
  induction steps generalizing before with
  | nil => rfl
  | cons step rest ih =>
      rcases step with ⟨after, crossings⟩
      rcases hvalid with ⟨_, href, _, hpositive, htail⟩
      have hw : crossings = 0 := by
        by_contra hn
        have hp : 0 < crossings := Nat.pos_of_ne_zero hn
        obtain ⟨source, hs, hstrad, _⟩ := hpositive hp
        exact hsep source hs hstrad
      have ha := cutSeparated_of_refines side before after href hsep
      have hrest := ih after ha htail
      simp [runActivity, hw, hrest]

theorem cut_activity_le_capacity (side : Record → Bool) (capacity : ℕ)
    (before : Family Record) (steps : List (Family Record × ℕ))
    (hvalid : ValidCutRun side capacity before steps) : runActivity steps ≤ capacity := by
  induction steps generalizing before with
  | nil => simp [runActivity]
  | cons step rest ih =>
      rcases step with ⟨after, crossings⟩
      rcases hvalid with ⟨hunique, href, hwD, hpositive, htail⟩
      by_cases hw : crossings = 0
      · have hrest := ih after htail
        simpa [runActivity, hw] using hrest
      · have hp : 0 < crossings := Nat.pos_of_ne_zero hw
        obtain ⟨source, hs, hstrad, hc⟩ := hpositive hp
        have hsep := cutSeparated_after_collapse side source before after hunique hs hstrad hc
        have hrest := cutSeparated_run_activity_eq_zero side capacity after rest hsep htail
        simpa [runActivity, hrest] using hwD

def BeforeInOrder (a b : Finset ℕ) : Prop :=
  ∀ x ∈ a, ∀ y ∈ b, x < y

def OrderedFamily (blocks : Family ℕ) : Prop :=
  ∀ a ∈ blocks, ∀ b ∈ blocks, a ≠ b → BeforeInOrder a b ∨ BeforeInOrder b a

theorem straddles_nat_cut_iff (cut : ℕ) (a : Finset ℕ) :
    Straddles (fun x => decide (cut ≤ x)) a ↔
      ∃ x ∈ a, ∃ y ∈ a, x < cut ∧ cut ≤ y := by
  constructor
  · rintro ⟨x, hx, y, hy, hdiff⟩
    by_cases hcx : cut ≤ x <;> by_cases hcy : cut ≤ y
    · simp [hcx, hcy] at hdiff
    · exact ⟨y, hy, x, hx, by omega, hcx⟩
    · exact ⟨x, hx, y, hy, by omega, hcy⟩
    · simp [hcx, hcy] at hdiff
  · rintro ⟨x, hx, y, hy, hxc, hcy⟩
    exact ⟨x, hx, y, hy, by simp [hcy, show ¬cut ≤ x by omega]⟩

/-- Disjoint ordered fragments have at most one fragment straddling a
fixed historical join cut, even after arbitrary deletions leave holes. -/
theorem orderedFamily_uniqueStraddler (cut : ℕ) (blocks : Family ℕ)
    (horder : OrderedFamily blocks) :
    UniqueStraddler (fun x => decide (cut ≤ x)) blocks := by
  intro a ha b hb has hbs
  by_contra hne
  obtain ⟨al, hal, ar, har, halc, hcar⟩ := (straddles_nat_cut_iff cut a).mp has
  obtain ⟨bl, hbl, br, hbr, hblc, hcbr⟩ := (straddles_nat_cut_iff cut b).mp hbs
  rcases horder a ha b hb hne with hab | hba
  · have h := hab ar har bl hbl
    omega
  · have h := hba br hbr al hal
    omega

theorem beforeInOrder_of_subsets (a b a' b' : Finset ℕ)
    (haa : a' ⊆ a) (hbb : b' ⊆ b) (hab : BeforeInOrder a b) :
    BeforeInOrder a' b' := by
  intro x hx y hy
  exact hab x (haa hx) y (hbb hy)

/-- Local interval splits preserve the order of an entire historical
family. Whole-block transfers require no additional condition because
owner and outward orientation do not occur in this historical order. -/
theorem orderedFamily_of_ordered_refinement (before after : Family ℕ)
    (ancestor : Finset ℕ → Finset ℕ) (hbefore : OrderedFamily before)
    (hancestor : ∀ b ∈ after, ancestor b ∈ before ∧ b ⊆ ancestor b)
    (hsiblings : ∀ a ∈ after, ∀ b ∈ after, a ≠ b → ancestor a = ancestor b →
      BeforeInOrder a b ∨ BeforeInOrder b a) : OrderedFamily after := by
  intro a ha b hb hne
  have haa := hancestor a ha
  have hbb := hancestor b hb
  by_cases hsame : ancestor a = ancestor b
  · exact hsiblings a ha b hb hne hsame
  · rcases hbefore (ancestor a) haa.1 (ancestor b) hbb.1 hsame with hab | hba
    · exact Or.inl (beforeInOrder_of_subsets _ _ _ _ haa.2 hbb.2 hab)
    · exact Or.inr (beforeInOrder_of_subsets _ _ _ _ hbb.2 haa.2 hba)

end GreedyForest
