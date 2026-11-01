import TangoSquared.Paper20261030.RobustPrivateCut

/-! Distinct rightward robust rectangles receive distinct horizontally
adjacent pairs in any finite arborally satisfied superset. A horizontal
pair is determined by its left endpoint, so their number is at most the
size of that superset. The assignment uses the proved private cut. -/

namespace TangoSquared.Paper20261030.Rectangles

theorem HorizontalAdjacent.right_unique {Y : Finset Point} {p q next : Point}
    (first : HorizontalAdjacent Y p q) (second : HorizontalAdjacent Y p next) : q = next := by
  obtain ⟨_,qMember,pqKey,pqTime,noFirst⟩ := first
  obtain ⟨_,nextMember,pNextKey,pNextTime,noSecond⟩ := second
  have firstGap := noFirst next nextMember pNextTime.symm
  have secondGap := noSecond q qMember pqTime.symm
  exact Prod.ext (by omega) (pqTime.symm.trans pNextTime)

noncomputable def horizontalPairs (Y : Finset Point) : Finset (Point × Point) := by
  classical
  exact (Y ×ˢ Y).filter (fun pair => HorizontalAdjacent Y pair.1 pair.2)

theorem horizontalPairs_card (Y : Finset Point) : (horizontalPairs Y).card ≤ Y.card := by
  classical
  have injective : Set.InjOn Prod.fst (horizontalPairs Y : Set (Point × Point)) := by
    intro first firstMember second secondMember same
    have firstPair := (Finset.mem_filter.mp firstMember).2
    have secondPair := (Finset.mem_filter.mp secondMember).2
    have secondSame : HorizontalAdjacent Y first.1 second.2 := by simpa only [same] using secondPair
    exact Prod.ext same (firstPair.right_unique secondSame)
  have count := Finset.card_image_iff.mpr injective
  have subset : (horizontalPairs Y).image Prod.fst ⊆ Y := by
    intro key member
    obtain ⟨pair,pairMember,rfl⟩ := Finset.mem_image.mp member
    exact ((Finset.mem_filter.mp pairMember).2 : HorizontalAdjacent Y pair.1 pair.2).1
  rw [← count]
  exact Finset.card_le_card subset

theorem robust_right_witnesses {P Y : Finset Point} (included : P ⊆ Y)
    (satisfied : ArboralDilation.Satisfied (Y : Set Point)) (R : Finset Rectangle)
    (family : RobustFamily P R) (rightward : ∀ r ∈ R, Rightward r) :
    ∃ W : Finset (Point × Point), W ⊆ horizontalPairs Y ∧ W.card = R.card ∧
      ∀ pair ∈ W, ∃ r ∈ R, Contains r pair.1 ∧ Contains r pair.2 := by
  classical
  by_cases empty : R = ∅
  · subst R
    exact ⟨∅,Finset.empty_subset _,rfl,by simp⟩
  · obtain ⟨r,rMember,cut,cutLeft,cutRight,privateCut⟩ := robust_private_cut family rightward
      (Finset.nonempty_iff_ne_empty.mpr empty)
    have smallerFamily : RobustFamily P (R.erase r) := ⟨
      fun s member => family.1 s (Finset.mem_of_mem_erase member),
      fun s member t other distinct => family.2 s (Finset.mem_of_mem_erase member)
        t (Finset.mem_of_mem_erase other) distinct⟩
    obtain ⟨W,inPairs,count,covered⟩ := robust_right_witnesses included satisfied (R.erase r)
      smallerFamily (fun s member => rightward s (Finset.mem_of_mem_erase member))
    have input := family.1 r rMember
    obtain ⟨p,q,adjacent,pInside,qInside,pLeft,qRight⟩ := horizontal_witness satisfied
      (included input.1.1) (included input.1.2.1) input.1.2.2.1.le cut cutLeft cutRight
    have fresh : (p,q) ∉ W := by
      intro member
      obtain ⟨s,sMember,sp,sq⟩ := covered (p,q) member
      have sRight := rightward s (Finset.mem_of_mem_erase sMember)
      have sCross : Crosses s cut p.2 := by
        simp only [Contains,min_eq_left sRight.le,max_eq_right sRight.le] at sp sq
        have sameTime := adjacent.2.2.2.1
        exact ⟨by omega,by omega,sp.2.2.1,by omega⟩
      exact privateCut s (Finset.mem_of_mem_erase sMember) (Finset.mem_erase.mp sMember).1
        p.2 pInside.2.2.1 pInside.2.2.2 sCross
    refine ⟨insert (p,q) W,?_,?_,?_⟩
    · intro pair member
      obtain same | old := Finset.mem_insert.mp member
      · subst pair
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨adjacent.1,adjacent.2.1⟩,adjacent⟩
      · exact inPairs old
    · rw [Finset.card_insert_of_notMem fresh,count,Finset.card_erase_of_mem rMember]
      have positive := Finset.card_pos.mpr ⟨r,rMember⟩
      omega
    · intro pair member
      obtain same | old := Finset.mem_insert.mp member
      · subst pair
        exact ⟨r,rMember,pInside,qInside⟩
      · obtain ⟨s,sMember,inside⟩ := covered pair old
        exact ⟨s,Finset.mem_of_mem_erase sMember,inside⟩
termination_by R.card
decreasing_by exact Finset.card_erase_lt_of_mem (by assumption)

theorem robust_right_card_le {P Y : Finset Point} (included : P ⊆ Y)
    (satisfied : ArboralDilation.Satisfied (Y : Set Point)) {R : Finset Rectangle}
    (family : RobustFamily P R) (rightward : ∀ r ∈ R, Rightward r) : R.card ≤ Y.card := by
  obtain ⟨W,inPairs,count,_⟩ := robust_right_witnesses included satisfied R family rightward
  rw [← count]
  exact (Finset.card_le_card inPairs).trans (horizontalPairs_card Y)

end TangoSquared.Paper20261030.Rectangles
