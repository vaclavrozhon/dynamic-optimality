import TangoSquared.Paper20261030.RectangleGadget

/-!
# Exact reflection invariance of rectangle certificates

The generic transport structure below is instantiated by horizontal
reflection and time reversal. Its fields are the explicit geometric
identities proved below, not assumptions about either rectangle bound.
Time reversal swaps the chronological defining endpoints.
-/

namespace TangoSquared.Paper20261030.Rectangles

def Defining (r : Rectangle) (p : Point) : Prop := p = r.1 ∨ p = r.2

structure Symmetry where
  point : Point → Point
  rectangle : Rectangle → Rectangle
  point_involutive : Function.Involutive point
  rectangle_involutive : Function.Involutive rectangle
  on_map : ∀ P r, On (P.image point) (rectangle r) ↔ On P r
  contains_map : ∀ r p, Contains (rectangle r) (point p) ↔ Contains r p
  corner_map : ∀ r p, Corner (rectangle r) (point p) ↔ Corner r p
  defining_map : ∀ r p, Defining (rectangle r) (point p) ↔ Defining r p
  shared_map : ∀ r s, Shared (rectangle r) (rectangle s) ↔ Shared r s

namespace Symmetry

theorem point_injective (σ : Symmetry) : Function.Injective σ.point :=
  σ.point_involutive.injective

theorem rectangle_injective (σ : Symmetry) : Function.Injective σ.rectangle :=
  σ.rectangle_involutive.injective

theorem inputFree_map (σ : Symmetry) {P : Finset Point} {r : Rectangle}
    (h : InputFree P r) : InputFree (P.image σ.point) (σ.rectangle r) := by
  refine ⟨(σ.on_map P r).mpr h.1,?_⟩
  intro p hp hc
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  exact (σ.defining_map r q).mpr (h.2 q hq ((σ.contains_map r q).mp hc))

theorem noCorner_map (σ : Symmetry) {r s : Rectangle} (h : NoCorner r s) :
    NoCorner (σ.rectangle r) (σ.rectangle s) := by
  intro p hp hc
  have hcorner : Corner s (σ.point p) := (σ.corner_map s (σ.point p)).mp
    (by simpa only [σ.point_involutive p] using hp)
  have hcontains : Contains r (σ.point p) := (σ.contains_map r (σ.point p)).mp
    (by simpa only [σ.point_involutive p] using hc)
  exact h _ hcorner hcontains

theorem robustPair_map (σ : Symmetry) {r s : Rectangle} (h : RobustPair r s) :
    RobustPair (σ.rectangle r) (σ.rectangle s) := by
  rcases h with h | ⟨h₁,h₂⟩
  · exact Or.inl ((σ.shared_map r s).mpr h)
  · exact Or.inr ⟨σ.noCorner_map h₁,σ.noCorner_map h₂⟩

theorem robustFamily_map (σ : Symmetry) {P : Finset Point} {R : Finset Rectangle}
    (h : RobustFamily P R) : RobustFamily (P.image σ.point) (R.image σ.rectangle) := by
  constructor
  · intro r hr
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hr
    exact σ.inputFree_map (h.1 a ha)
  · intro r hr s hs hne
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hs
    exact σ.robustPair_map (h.2 a ha b hb (fun he => hne (congrArg σ.rectangle he)))

theorem robustBound_le_map (σ : Symmetry) (P : Finset Point) :
    robustBound P ≤ robustBound (P.image σ.point) := by
  obtain ⟨R,hR,hcard⟩ := exists_robust_maximum P
  have h := robust_card_le (σ.robustFamily_map hR)
  rw [Finset.card_image_of_injective _ σ.rectangle_injective,hcard] at h
  exact h

theorem robustBound_map (σ : Symmetry) (P : Finset Point) :
    robustBound (P.image σ.point) = robustBound P := by
  apply le_antisymm
  · have h := σ.robustBound_le_map (P.image σ.point)
    have he : σ.point ∘ σ.point = id := funext σ.point_involutive
    simpa only [Finset.image_image,he,Finset.image_id] using h
  · exact σ.robustBound_le_map P

theorem point_image_image (σ : Symmetry) (P : Finset Point) :
    (P.image σ.point).image σ.point = P := by
  have he : σ.point ∘ σ.point = id := funext σ.point_involutive
  simp only [Finset.image_image,he,Finset.image_id]

theorem rectangle_image_image (σ : Symmetry) (R : Finset Rectangle) :
    (R.image σ.rectangle).image σ.rectangle = R := by
  have he : σ.rectangle ∘ σ.rectangle = id := funext σ.rectangle_involutive
  simp only [Finset.image_image,he,Finset.image_id]

theorem robustFamily_map_iff (σ : Symmetry) (P : Finset Point) (R : Finset Rectangle) :
    RobustFamily (P.image σ.point) (R.image σ.rectangle) ↔ RobustFamily P R := by
  constructor
  · intro h
    simpa only [σ.point_image_image,σ.rectangle_image_image] using σ.robustFamily_map h
  · exact σ.robustFamily_map

end Symmetry

theorem involution_mem_image (f : Point → Point) (hf : Function.Involutive f)
    (P : Finset Point) (p : Point) : f p ∈ P.image f ↔ p ∈ P := by
  constructor
  · intro h
    obtain ⟨q,hq,he⟩ := Finset.mem_image.mp h
    exact hf.injective he ▸ hq
  · intro hp
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩

def reversePoint (p : Point) : Point := (p.1,-p.2)
def reverseRectangle (r : Rectangle) : Rectangle := (reversePoint r.2,reversePoint r.1)
def mirrorPoint (p : Point) : Point := (-p.1,p.2)
def mirrorRectangle (r : Rectangle) : Rectangle := (mirrorPoint r.1,mirrorPoint r.2)

theorem reversePoint_involutive : Function.Involutive reversePoint := by
  intro p
  simp [reversePoint]

theorem reverseRectangle_involutive : Function.Involutive reverseRectangle := by
  intro r
  exact Prod.ext (reversePoint_involutive _) (reversePoint_involutive _)

theorem mirrorPoint_involutive : Function.Involutive mirrorPoint := by
  intro p
  simp [mirrorPoint]

theorem mirrorRectangle_involutive : Function.Involutive mirrorRectangle := by
  intro r
  exact Prod.ext (mirrorPoint_involutive _) (mirrorPoint_involutive _)

def timeReversal : Symmetry where
  point := reversePoint
  rectangle := reverseRectangle
  point_involutive := reversePoint_involutive
  rectangle_involutive := reverseRectangle_involutive
  on_map := by
    intro P r
    change (reversePoint r.2 ∈ P.image reversePoint ∧
      reversePoint r.1 ∈ P.image reversePoint ∧ -r.2.2 < -r.1.2 ∧ r.2.1 ≠ r.1.1) ↔ On P r
    rw [involution_mem_image reversePoint reversePoint_involutive,
      involution_mem_image reversePoint reversePoint_involutive]
    unfold On
    constructor <;> rintro ⟨h₁,h₂,h₃,h₄⟩
    · exact ⟨h₂,h₁,by omega,Ne.symm h₄⟩
    · exact ⟨h₂,h₁,by omega,Ne.symm h₄⟩
  contains_map := by
    intro r p
    simp only [Contains,reverseRectangle,reversePoint]
    omega
  corner_map := by
    intro r p
    simp only [Corner,reverseRectangle,reversePoint]
    omega
  defining_map := by
    intro r p
    simp only [Defining,reverseRectangle,reversePoint_involutive.injective.eq_iff]
    exact or_comm
  shared_map := by
    intro r s
    simp only [Shared,reverseRectangle,reversePoint_involutive.injective.eq_iff]
    tauto

def horizontalReflection : Symmetry where
  point := mirrorPoint
  rectangle := mirrorRectangle
  point_involutive := mirrorPoint_involutive
  rectangle_involutive := mirrorRectangle_involutive
  on_map := by
    intro P r
    change (mirrorPoint r.1 ∈ P.image mirrorPoint ∧
      mirrorPoint r.2 ∈ P.image mirrorPoint ∧ r.1.2 < r.2.2 ∧ -r.1.1 ≠ -r.2.1) ↔ On P r
    rw [involution_mem_image mirrorPoint mirrorPoint_involutive,
      involution_mem_image mirrorPoint mirrorPoint_involutive]
    unfold On
    constructor <;> rintro ⟨h₁,h₂,h₃,h₄⟩ <;> exact ⟨h₁,h₂,h₃,by omega⟩
  contains_map := by
    intro r p
    simp only [Contains,mirrorRectangle,mirrorPoint]
    omega
  corner_map := by
    intro r p
    simp only [Corner,mirrorRectangle,mirrorPoint,neg_inj]
  defining_map := by
    intro r p
    simp only [Defining,mirrorRectangle,mirrorPoint_involutive.injective.eq_iff]
  shared_map := by
    intro r s
    simp only [Shared,mirrorRectangle,mirrorPoint_involutive.injective.eq_iff]

theorem robustBound_reverse (P : Finset Point) :
    robustBound (P.image reversePoint) = robustBound P := timeReversal.robustBound_map P

theorem robustBound_mirror (P : Finset Point) :
    robustBound (P.image mirrorPoint) = robustBound P := horizontalReflection.robustBound_map P

theorem instance_mirror {P : Finset Point} (hP : Instance P) :
    Instance (P.image mirrorPoint) := by
  intro p hp q hq he
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hq
  exact congrArg mirrorPoint (hP a ha b hb he)

/-- The horizontally reflected extension lemma; the guard is now to the right. -/
theorem rectangle_extension_left {P : Finset Point} (hP : Instance P)
    {p : Point} (hp : p ∈ P) (gx gy : Int) (hgx : p.1 < gx)
    (guard : (gx,gy) ∈ P ∨ ∀ z ∈ P, z.2 < gy)
    (emptyStrip : ∀ z ∈ P, p.1 ≤ z.1 → z.1 < gx → p.2 < z.2 → z.2 < gy → False)
    (west : ∃ z ∈ P, z.1 < p.1 ∧ p.2 < z.2 ∧ z.2 < gy)
    {R : Finset Rectangle} (hR : RobustFamily P R) :
    ∃ z ∈ P, z.1 < p.1 ∧ p.2 < z.2 ∧ z.2 < gy ∧
      RobustFamily P (insert (p,z) R) := by
  have hp' : mirrorPoint p ∈ P.image mirrorPoint := Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hguard : (-gx,gy) ∈ P.image mirrorPoint ∨
      ∀ z ∈ P.image mirrorPoint, z.2 < gy := by
    rcases guard with h | h
    · exact Or.inl (Finset.mem_image.mpr ⟨(gx,gy),h,rfl⟩)
    · right
      intro z hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
      exact h a ha
  have hempty : ∀ z ∈ P.image mirrorPoint, -gx < z.1 → z.1 ≤ (mirrorPoint p).1 →
      (mirrorPoint p).2 < z.2 → z.2 < gy → False := by
    intro z hz hx₁ hx₂ ht₁ ht₂
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    apply emptyStrip a ha (by dsimp [mirrorPoint] at hx₂; omega)
      (by dsimp [mirrorPoint] at hx₁; omega) ht₁ ht₂
  have heast : ∃ z ∈ P.image mirrorPoint, (mirrorPoint p).1 < z.1 ∧
      (mirrorPoint p).2 < z.2 ∧ z.2 < gy := by
    obtain ⟨z,hz,hx,ht,hgy⟩ := west
    exact ⟨mirrorPoint z,Finset.mem_image.mpr ⟨z,hz,rfl⟩,
      by dsimp [mirrorPoint]; omega,ht,hgy⟩
  obtain ⟨z,hz,hx,ht,hgy,hnew⟩ := rectangle_extension (instance_mirror hP) hp'
    (-gx) gy (by dsimp [mirrorPoint]; omega) hguard hempty heast
    (horizontalReflection.robustFamily_map hR)
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
  refine ⟨a,ha,by dsimp [mirrorPoint] at hx; omega,ht,hgy,?_⟩
  apply (horizontalReflection.robustFamily_map_iff P (insert (p,a) R)).mp
  simpa only [Finset.image_insert,horizontalReflection,mirrorRectangle] using hnew

end TangoSquared.Paper20261030.Rectangles
