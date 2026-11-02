import DynamicOptimality.GeometricModel
import ChaCha.ArboralQuotient

/-!
# Monotone key quotients in the shared geometric model

Natural-key points are embedded in the existing integer rectangle library.
Its inwardmost-fiber argument proves that merging consecutive key classes
preserves satisfaction, even when rectangle endpoints coalesce.
-/

namespace DynamicOptimality.Geometry

open GreedyMerge.Geometry

def integerPoint (point : Point) : ChaCha.ArboralDilation.Point :=
  ((point.1 : Int),point.2)

def integerPoints (set : Finset Point) : Finset ChaCha.ArboralDilation.Point :=
  set.image integerPoint

theorem integerPoint_injective : Function.Injective integerPoint := by
  intro first second same
  apply Prod.ext
  · have equal : (first.1:Int) = (second.1:Int) := congrArg Prod.fst same
    exact_mod_cast equal
  · simpa only [integerPoint] using congrArg (fun point : Int × Int => point.2) same

theorem satisfied_integerPoints {set : Finset Point} (satisfied : ArborallySatisfied set) :
    ChaCha.ArboralDilation.Satisfied (integerPoints set : Set ChaCha.ArboralDilation.Point) := by
  intro a t b u first second increasing different
  obtain ⟨p,hp,ep⟩ := Finset.mem_image.mp first
  obtain ⟨q,hq,eq⟩ := Finset.mem_image.mp second
  have pa : (p.1:Int) = a := congrArg Prod.fst ep
  have pt : p.2 = t := congrArg Prod.snd ep
  have qb : (q.1:Int) = b := congrArg Prod.fst eq
  have qu : q.2 = u := congrArg Prod.snd eq
  have order : p.1 < q.1 := by omega
  have times : p.2 ≠ q.2 := by omega
  obtain ⟨r,hr,rp,rq,between,after,before⟩ := satisfied p hp q hq (ne_of_lt order) times
  refine ⟨integerPoint r,Finset.mem_image.mpr ⟨r,hr,rfl⟩,?_,?_,?_⟩
  · change a ≤ (r.1:Int) ∧ (r.1:Int) ≤ b ∧ min t u ≤ r.2 ∧ r.2 ≤ max t u
    simp only [Between,min_eq_left order.le,max_eq_right order.le] at between
    exact ⟨by omega,by omega,by simpa only [← pt,← qu] using after,
      by simpa only [← pt,← qu] using before⟩
  · intro equal
    exact rp (integerPoint_injective (equal.trans ep.symm))
  · intro equal
    exact rq (integerPoint_injective (equal.trans eq.symm))

theorem integerPoints_satisfied {set : Finset Point}
    (satisfied : ChaCha.ArboralDilation.Satisfied
      (integerPoints set : Set ChaCha.ArboralDilation.Point)) : ArborallySatisfied set := by
  have ordered (p q : Point) (hp : p ∈ set) (hq : q ∈ set)
      (increasing : p.1 < q.1) (different : p.2 ≠ q.2) :
      ∃ r ∈ set, r ≠ p ∧ r ≠ q ∧ Between p.1 q.1 r.1 ∧
        min p.2 q.2 ≤ r.2 ∧ r.2 ≤ max p.2 q.2 := by
    obtain ⟨z,hz,rectangle,zp,zq⟩ := satisfied (p.1:Int) p.2 (q.1:Int) q.2
      (Finset.mem_image.mpr ⟨p,hp,rfl⟩) (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
      (by exact_mod_cast increasing) different
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hz
    refine ⟨r,hr,?_,?_,?_,rectangle.2.2.1,rectangle.2.2.2⟩
    · intro equal
      exact zp (congrArg integerPoint equal)
    · intro equal
      exact zq (congrArg integerPoint equal)
    · simp only [Between,min_eq_left increasing.le,max_eq_right increasing.le]
      have lower : (p.1:Int) ≤ (r.1:Int) := rectangle.1
      have upper : (r.1:Int) ≤ (q.1:Int) := rectangle.2.1
      exact ⟨by exact_mod_cast lower,by exact_mod_cast upper⟩
  intro p hp q hq columns times
  rcases lt_or_gt_of_ne columns with increasing | decreasing
  · exact ordered p q hp hq increasing times
  · obtain ⟨r,hr,rq,rp,between,after,before⟩ := ordered q p hq hp decreasing times.symm
    exact ⟨r,hr,rp,rq,by simpa only [Between,min_comm,max_comm] using between,
      by simpa only [min_comm] using after,by simpa only [max_comm] using before⟩

def mapColumns (f : Nat → Nat) (set : Finset Point) : Finset Point :=
  set.image (fun point => (f point.1,point.2))

/-- The key map may identify arbitrarily many adjacent columns. -/
theorem ArborallySatisfied.mapColumns {set : Finset Point} (satisfied : ArborallySatisfied set)
    (f : Nat → Nat) (mono : Monotone f) : ArborallySatisfied (mapColumns f set) := by
  let integerMap : Int → Int := fun key => (f key.toNat : Int)
  have monotone : Monotone integerMap := by
    intro first second order
    change (f first.toNat : Int) ≤ (f second.toNat : Int)
    exact_mod_cast mono (Int.toNat_le_toNat order)
  have result := ChaCha.ArboralQuotient.satisfied_mapColumns
    (integerPoints set) integerMap monotone (satisfied_integerPoints satisfied)
  have imageEq : integerPoints (DynamicOptimality.Geometry.mapColumns f set) =
      ChaCha.ArboralQuotient.mapColumns integerMap (integerPoints set) := by
    simp [integerPoints,DynamicOptimality.Geometry.mapColumns,ChaCha.ArboralQuotient.mapColumns,
      Finset.image_image,integerPoint,integerMap,Function.comp_def]
  apply integerPoints_satisfied
  rw [imageEq]
  exact result

end DynamicOptimality.Geometry
