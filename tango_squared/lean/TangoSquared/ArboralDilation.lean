import Mathlib.Data.Set.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Harmless nearby-port augmentation: the geometric kernel

Horizontal interval dilation and replication of time rows preserve arboral
satisfaction. These are statements about actual integer point sets, with no
assumed witness transport. The geometric correspondence with BST executions
and the resulting competitive wrapper remain external hand arguments.
-/

namespace TangoSquared.ArboralDilation

abbrev Point := Int × Int

/-- Closed rectangle membership. Only the horizontal corners are ordered;
the time coordinates may occur in either order. -/
def InRectangle (a t b u : Int) (p : Point) : Prop :=
  a ≤ p.1 ∧ p.1 ≤ b ∧ min t u ≤ p.2 ∧ p.2 ≤ max t u

/-- Ordering the two different columns loses no nondegenerate rectangle. -/
def Satisfied (P : Set Point) : Prop :=
  ∀ a t b u, (a, t) ∈ P → (b, u) ∈ P → a < b → t ≠ u →
    ∃ p ∈ P, InRectangle a t b u p ∧ p ≠ (a, t) ∧ p ≠ (b, u)

def dilate (d : Int) (P : Set Point) : Set Point :=
  {p | ∃ x, (x, p.2) ∈ P ∧ x - d ≤ p.1 ∧ p.1 ≤ x + d}

theorem mem_dilate {d a t : Int} {P : Set Point} :
    (a, t) ∈ dilate d P ↔ ∃ x, (x, t) ∈ P ∧ x - d ≤ a ∧ a ≤ x + d := Iff.rfl

theorem satisfied_dilate {P : Set Point} (hP : Satisfied P)
    {d : Int} (hd : 0 ≤ d) : Satisfied (dilate d P) := by
  intro a t b u ha hb hab htu
  obtain ⟨x, hx, hxa, hax⟩ := ha
  obtain ⟨y, hy, hyb, hby⟩ := hb
  by_cases hnext : a + 1 ≤ x + d
  · refine ⟨(a + 1, t), ⟨x, hx, by omega, hnext⟩, ?_, ?_, ?_⟩
    · simp only [InRectangle]
      constructor
      · omega
      constructor
      · omega
      exact ⟨min_le_left _ _, le_max_left _ _⟩
    · intro he; have := congrArg Prod.fst he; omega
    · intro he; exact htu (congrArg Prod.snd he)
  by_cases hprev : y - d ≤ b - 1
  · refine ⟨(b - 1, u), ⟨y, hy, hprev, by omega⟩, ?_, ?_, ?_⟩
    · simp only [InRectangle]
      constructor
      · omega
      constructor
      · omega
      exact ⟨min_le_right _ _, le_max_right _ _⟩
    · intro he; exact htu (congrArg Prod.snd he).symm
    · intro he; have := congrArg Prod.fst he; omega
  have haedge : a = x + d := by omega
  have hbedge : b = y - d := by omega
  have hxy : x < y := by omega
  obtain ⟨⟨z, v⟩, hz, hrect, hzx, hzy⟩ := hP x t y u hx hy hxy htu
  rcases hrect with ⟨hxz, hzy', htv, hvu⟩
  by_cases hvt : v = t
  · subst v
    have hxz' : x < z := by
      by_contra h
      have he : z = x := by omega
      exact hzx (by simp [he])
    let z' := min b (z + d)
    have hza : a < z' := by dsimp [z']; omega
    have hzb : z' ≤ b := min_le_left _ _
    have hshiftlo : z - d ≤ z' := by dsimp [z']; omega
    have hshifthi : z' ≤ z + d := min_le_right _ _
    refine ⟨(z', t), ⟨z, hz, hshiftlo, hshifthi⟩,
      ⟨by omega, hzb, min_le_left _ _, le_max_left _ _⟩, ?_, ?_⟩
    · intro he; have := congrArg Prod.fst he; omega
    · intro he; exact htu (congrArg Prod.snd he)
  by_cases hvu' : v = u
  · subst v
    have hzylt : z < y := by
      by_contra h
      have he : z = y := by omega
      exact hzy (by simp [he])
    let z' := max a (z - d)
    have hza : a ≤ z' := le_max_left _ _
    have hzb : z' < b := by dsimp [z']; omega
    have hshiftlo : z - d ≤ z' := le_max_right _ _
    have hshifthi : z' ≤ z + d := by dsimp [z']; omega
    refine ⟨(z', u), ⟨z, hz, hshiftlo, hshifthi⟩,
      ⟨hza, by omega, min_le_right _ _, le_max_right _ _⟩, ?_, ?_⟩
    · intro he; exact htu (congrArg Prod.snd he).symm
    · intro he; have := congrArg Prod.fst he; omega
  · let z' := max a (min b z)
    have hza : a ≤ z' := le_max_left _ _
    have hzb : z' ≤ b := by dsimp [z']; omega
    have hshiftlo : z - d ≤ z' := by dsimp [z']; omega
    have hshifthi : z' ≤ z + d := by dsimp [z']; omega
    refine ⟨(z', v), ⟨z, hz, hshiftlo, hshifthi⟩,
      ⟨hza, hzb, htv, hvu⟩, ?_, ?_⟩
    · intro he; exact hvt (congrArg Prod.snd he)
    · intro he; exact hvu' (congrArg Prod.snd he)

/-- Clipping columns to the fixed finite key universe loses no witness. -/
theorem satisfied_clip {P : Set Point} (hP : Satisfied P) (lo hi : Int) :
    Satisfied {p ∈ P | lo ≤ p.1 ∧ p.1 ≤ hi} := by
  intro a t b u ha hb hab htu
  obtain ⟨p, hp, hr, hpa, hpb⟩ := hP a t b u ha.1 hb.1 hab htu
  exact ⟨p, ⟨hp, le_trans ha.2.1 hr.1, le_trans hr.2.1 hb.2.2⟩,
    hr, hpa, hpb⟩

/-- Replace row t by the k integer rows beginning at k*t. -/
def replicateRows (k : Int) (P : Set Point) : Set Point :=
  {p | ∃ t, (p.1, t) ∈ P ∧ k * t ≤ p.2 ∧ p.2 < k * (t + 1)}

theorem satisfied_replicateRows {P : Set Point} (hP : Satisfied P)
    {k : Int} (hk : 0 < k) : Satisfied (replicateRows k P) := by
  intro a A b B ha hb hab hAB
  obtain ⟨t, ht, htA, hAt⟩ := ha
  obtain ⟨u, hu, huB, hBu⟩ := hb
  by_cases htu : t = u
  · subst u
    refine ⟨(b, A), ⟨t, hu, htA, hAt⟩,
      ⟨le_of_lt hab, le_rfl, min_le_left _ _, le_max_left _ _⟩, ?_, ?_⟩
    · intro he; have := congrArg Prod.fst he; omega
    · intro he; exact hAB (congrArg Prod.snd he)
  obtain ⟨⟨z, v⟩, hz, hr, hza, hzb⟩ := hP a t b u ht hu hab htu
  rcases hr with ⟨haz, hzb', htv, hvu⟩
  by_cases hvt : v = t
  · subst v
    have hne : z ≠ a := by intro h; exact hza (by simp [h])
    refine ⟨(z, A), ⟨t, hz, htA, hAt⟩,
      ⟨haz, hzb', min_le_left _ _, le_max_left _ _⟩, ?_, ?_⟩
    · intro he; exact hne (congrArg Prod.fst he)
    · intro he; exact hAB (congrArg Prod.snd he)
  by_cases hvu' : v = u
  · subst v
    have hne : z ≠ b := by intro h; exact hzb (by simp [h])
    refine ⟨(z, B), ⟨u, hz, huB, hBu⟩,
      ⟨haz, hzb', min_le_right _ _, le_max_right _ _⟩, ?_, ?_⟩
    · intro he; exact hAB (congrArg Prod.snd he).symm
    · intro he; exact hne (congrArg Prod.fst he)
  · have hbetween : min A B < k * v ∧ k * v < max A B := by
      rcases lt_or_gt_of_ne htu with hlt | hgt
      · have h1 : t + 1 ≤ v := by omega
        have h2 : v + 1 ≤ u := by omega
        have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt hk)
        have h4 := mul_le_mul_of_nonneg_left h2 (le_of_lt hk)
        have ha' : A < k * v := by nlinarith
        have hb' : k * v < B := by nlinarith
        exact ⟨lt_of_le_of_lt (min_le_left _ _) ha',
          lt_of_lt_of_le hb' (le_max_right _ _)⟩
      · have h1 : u + 1 ≤ v := by omega
        have h2 : v + 1 ≤ t := by omega
        have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt hk)
        have h4 := mul_le_mul_of_nonneg_left h2 (le_of_lt hk)
        have hb' : B < k * v := by nlinarith
        have ha' : k * v < A := by nlinarith
        exact ⟨lt_of_le_of_lt (min_le_right _ _) hb',
          lt_of_lt_of_le ha' (le_max_left _ _)⟩
    refine ⟨(z, k * v), ⟨v, hz, le_rfl, by nlinarith⟩,
      ⟨haz, hzb', le_of_lt hbetween.1, le_of_lt hbetween.2⟩, ?_, ?_⟩
    · intro he
      have he' := congrArg Prod.snd he
      have h1 := min_le_left A B
      have h2 := le_max_left A B
      by_cases hlt : t < u
      · have h1' : t + 1 ≤ v := by omega
        have h2' := mul_le_mul_of_nonneg_left h1' (le_of_lt hk)
        nlinarith
      · have h1' : v + 1 ≤ t := by omega
        have h2' := mul_le_mul_of_nonneg_left h1' (le_of_lt hk)
        nlinarith
    · intro he
      have he' := congrArg Prod.snd he
      by_cases hlt : t < u
      · have h1' : v + 1 ≤ u := by omega
        have h2' := mul_le_mul_of_nonneg_left h1' (le_of_lt hk)
        nlinarith
      · have h1' : u + 1 ≤ v := by omega
        have h2' := mul_le_mul_of_nonneg_left h1' (le_of_lt hk)
        nlinarith

def finiteDilation (d : Nat) (P : Finset Point) : Finset Point :=
  (P ×ˢ Finset.range (2 * d + 1)).image
    (fun pi => (pi.1.1 + (pi.2 : Int) - (d : Int), pi.1.2))

theorem mem_finiteDilation (d : Nat) (P : Finset Point) (p : Point) :
    p ∈ finiteDilation d P ↔ p ∈ dilate (d : Int) (P : Set Point) := by
  rcases p with ⟨a, t⟩
  constructor
  · intro hp
    obtain ⟨⟨⟨x, v⟩, i⟩, hxi, he⟩ := Finset.mem_image.mp hp
    rcases Finset.mem_product.mp hxi with ⟨hx, hi⟩
    have hi' := Finset.mem_range.mp hi
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    dsimp at h1 h2
    subst v
    exact ⟨x, hx, by omega, by omega⟩
  · rintro ⟨x, hx, h1, h2⟩
    apply Finset.mem_image.mpr
    refine ⟨((x, t), (a - x + (d : Int)).toNat),
      Finset.mem_product.mpr ⟨hx, Finset.mem_range.mpr (by omega)⟩, ?_⟩
    apply Prod.ext <;> (try dsimp; try omega)

theorem finiteDilation_card_le (d : Nat) (P : Finset Point) :
    (finiteDilation d P).card ≤ P.card * (2 * d + 1) := by
  apply Finset.card_image_le.trans
  simp [Finset.card_product]

def finiteRows (k : Nat) (P : Finset Point) : Finset Point :=
  (P ×ˢ Finset.range k).image
    (fun pi => (pi.1.1, (k : Int) * pi.1.2 + (pi.2 : Int)))

theorem mem_finiteRows (k : Nat) (P : Finset Point) (p : Point) :
    p ∈ finiteRows k P ↔ p ∈ replicateRows (k : Int) (P : Set Point) := by
  rcases p with ⟨a, A⟩
  constructor
  · intro hp
    obtain ⟨⟨⟨x, t⟩, i⟩, hxi, he⟩ := Finset.mem_image.mp hp
    rcases Finset.mem_product.mp hxi with ⟨hx, hi⟩
    have hi' := Finset.mem_range.mp hi
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    dsimp at h1 h2
    subst x
    refine ⟨t, hx, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨t, ht, h1, h2⟩
    apply Finset.mem_image.mpr
    refine ⟨((a, t), (A - (k : Int) * t).toNat),
      Finset.mem_product.mpr ⟨ht, Finset.mem_range.mpr ?_⟩, ?_⟩
    · have hlt : A - (k : Int) * t < (k : Int) := by nlinarith
      omega
    · apply Prod.ext <;> (try dsimp; try omega)

theorem finiteRows_card_le (k : Nat) (P : Finset Point) :
    (finiteRows k P).card ≤ P.card * k := by
  apply Finset.card_image_le.trans
  simp [Finset.card_product]

/-- A concrete finite witness set of the required constant-factor size. -/
theorem finite_augmentation {P : Finset Point} (hP : Satisfied (P : Set Point))
    (d k : Nat) (hk : 0 < k) :
    Satisfied (finiteRows k (finiteDilation d P) : Set Point) ∧
      (finiteRows k (finiteDilation d P)).card ≤ P.card * (2 * d + 1) * k := by
  have hD : (finiteDilation d P : Set Point) = dilate (d : Int) (P : Set Point) := by
    ext p
    exact mem_finiteDilation d P p
  have hR : (finiteRows k (finiteDilation d P) : Set Point) =
      replicateRows (k : Int) (finiteDilation d P : Set Point) := by
    ext p
    exact mem_finiteRows k (finiteDilation d P) p
  constructor
  · rw [hR, hD]
    exact satisfied_replicateRows (satisfied_dilate hP (by omega)) (by omega)
  · exact (finiteRows_card_le _ _).trans
      (Nat.mul_le_mul_right k (finiteDilation_card_le d P))

/-- Every requested nearby port occurs in any chosen copy of its original
query row. Together with `finite_augmentation`, this is the finite geometric
certificate used by the neighborhood-augmentation comparison. -/
theorem nearby_port_mem (P : Finset Point) (d k : Nat)
    {x t a : Int} (hx : (x, t) ∈ P)
    (hlo : x - (d : Int) ≤ a) (hhi : a ≤ x + (d : Int))
    {i : Nat} (hi : i < k) :
    (a, (k : Int) * t + (i : Int)) ∈ finiteRows k (finiteDilation d P) := by
  rw [mem_finiteRows]
  refine ⟨t, ?_, ?_, ?_⟩
  · change (a, t) ∈ finiteDilation d P
    rw [mem_finiteDilation]
    exact ⟨x, hx, hlo, hhi⟩
  · omega
  · nlinarith

end TangoSquared.ArboralDilation
