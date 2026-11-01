import TangoSquared.Paper20261030.RobustWitnessCounting
import TangoSquared.Paper20261030.RectangleSymmetry

/-! The actual robust rectangle maximum is at most twice the size of
any finite arborally satisfied superset. The proof allows repeated keys
and uses the existing rectangle definitions. Turning a BST execution
into such a satisfied set is a further, separate theorem. -/

namespace TangoSquared.Paper20261030.Rectangles

theorem satisfied_mirror {Y : Finset Point} (satisfied : ArboralDilation.Satisfied (Y : Set Point)) :
    ArboralDilation.Satisfied (Y.image mirrorPoint : Set Point) := by
  intro a t b u aMember bMember ordered times
  have oldA : (-a,t) ∈ Y := (involution_mem_image mirrorPoint mirrorPoint_involutive Y (-a,t)).mp
    (by simpa only [mirrorPoint,neg_neg,Finset.mem_coe] using aMember)
  have oldB : (-b,u) ∈ Y := (involution_mem_image mirrorPoint mirrorPoint_involutive Y (-b,u)).mp
    (by simpa only [mirrorPoint,neg_neg,Finset.mem_coe] using bMember)
  obtain ⟨p,member,box,notB,notA⟩ := satisfied (-b) u (-a) t oldB oldA (by omega) times.symm
  refine ⟨mirrorPoint p,Finset.mem_image.mpr ⟨p,member,rfl⟩,?_,?_,?_⟩
  · simp only [ArboralDilation.InRectangle,mirrorPoint] at box ⊢
    omega
  · intro same
    apply notA
    have reflected := congrArg mirrorPoint same
    simpa [mirrorPoint] using reflected
  · intro same
    apply notB
    have reflected := congrArg mirrorPoint same
    simpa [mirrorPoint] using reflected

theorem RobustFamily.subfamily {P : Finset Point} {R S : Finset Rectangle}
    (family : RobustFamily P R) (subset : S ⊆ R) : RobustFamily P S :=
  ⟨fun r member => family.1 r (subset member),
    fun r member s other different => family.2 r (subset member) s (subset other) different⟩

theorem robust_card_le_satisfied {P Y : Finset Point} (included : P ⊆ Y)
    (satisfied : ArboralDilation.Satisfied (Y : Set Point)) {R : Finset Rectangle}
    (family : RobustFamily P R) : R.card ≤ 2*Y.card := by
  classical
  let positive := R.filter Rightward
  let negative := R.filter (fun r => ¬ Rightward r)
  have positiveFamily : RobustFamily P positive := family.subfamily (Finset.filter_subset _ _)
  have negativeFamily : RobustFamily P negative := family.subfamily (Finset.filter_subset _ _)
  have rightBound := robust_right_card_le included satisfied positiveFamily
    (fun r member => (Finset.mem_filter.mp member).2)
  have reflectedFamily := horizontalReflection.robustFamily_map negativeFamily
  have reflectedRight : ∀ r ∈ negative.image mirrorRectangle, Rightward r := by
    intro r member
    obtain ⟨s,inNegative,rfl⟩ := Finset.mem_image.mp member
    obtain ⟨inR,direction⟩ := Finset.mem_filter.mp inNegative
    have different := (family.1 s inR).1.2.2.2
    simp only [Rightward,mirrorRectangle,mirrorPoint] at direction ⊢
    omega
  have leftBound := robust_right_card_le (Finset.image_subset_image included) (satisfied_mirror satisfied)
    reflectedFamily reflectedRight
  change (negative.image mirrorRectangle).card ≤ (Y.image mirrorPoint).card at leftBound
  rw [Finset.card_image_of_injective _ mirrorRectangle_involutive.injective,
    Finset.card_image_of_injective _ mirrorPoint_involutive.injective] at leftBound
  have union : R = positive ∪ negative := by
    ext r
    simp only [positive,negative,Finset.mem_union,Finset.mem_filter]
    tauto
  calc
    R.card = (positive ∪ negative).card := congrArg Finset.card union
    _ ≤ positive.card+negative.card := Finset.card_union_le _ _
    _ ≤ 2*Y.card := by omega

theorem robustBound_le_satisfied {P Y : Finset Point} (included : P ⊆ Y)
    (satisfied : ArboralDilation.Satisfied (Y : Set Point)) : robustBound P ≤ 2*Y.card := by
  obtain ⟨R,family,count⟩ := exists_robust_maximum P
  rw [← count]
  exact robust_card_le_satisfied included satisfied family

end TangoSquared.Paper20261030.Rectangles
