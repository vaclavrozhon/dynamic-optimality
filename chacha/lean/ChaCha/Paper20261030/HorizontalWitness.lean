import ChaCha.Paper20261030.Rectangles
import ChaCha.ArboralDilation

/-!
# Horizontal witnesses across a rectangle cut

An arborally satisfied finite point set supplies a horizontally adjacent
pair across every nonintegral vertical cut of a rectangle whose defining
points belong to the set. We represent a cut by the integer immediately
to its left. This is the finite extremal argument of Lemma 4.3 in
Demaine et al., *The Geometry of Binary Search Trees* (SODA 2009).
It permits repeated key coordinates.
-/

namespace ChaCha.Paper20261030.Rectangles

def HorizontalAdjacent (Y : Finset Point) (p q : Point) : Prop :=
  p ∈ Y ∧ q ∈ Y ∧ p.1 < q.1 ∧ p.2 = q.2 ∧
    ∀ w ∈ Y, w.2 = p.2 → ¬ (p.1 < w.1 ∧ w.1 < q.1)

private theorem top_right (Y : Finset Point) (nonempty : Y.Nonempty) :
    ∃ p ∈ Y, (∀ q ∈ Y, q.2 ≤ p.2) ∧ (∀ q ∈ Y, q.2 = p.2 → q.1 ≤ p.1) := by
  classical
  obtain ⟨top,topMember,topMax⟩ := Finset.exists_max_image Y Prod.snd nonempty
  let row := Y.filter (fun q => q.2 = top.2)
  have rowNonempty : row.Nonempty := ⟨top,Finset.mem_filter.mpr ⟨topMember,rfl⟩⟩
  obtain ⟨p,pMember,pMax⟩ := Finset.exists_max_image row Prod.fst rowNonempty
  have spec := Finset.mem_filter.mp pMember
  refine ⟨p,spec.1,?_,?_⟩
  · intro q member
    rw [spec.2]
    exact topMax q member
  · intro q member time
    exact pMax q (Finset.mem_filter.mpr ⟨member,time.trans spec.2⟩)

private theorem bottom_left (Y : Finset Point) (nonempty : Y.Nonempty) :
    ∃ p ∈ Y, (∀ q ∈ Y, p.2 ≤ q.2) ∧ (∀ q ∈ Y, q.2 = p.2 → p.1 ≤ q.1) := by
  classical
  obtain ⟨bottom,bottomMember,bottomMin⟩ := Finset.exists_min_image Y Prod.snd nonempty
  let row := Y.filter (fun q => q.2 = bottom.2)
  have rowNonempty : row.Nonempty := ⟨bottom,Finset.mem_filter.mpr ⟨bottomMember,rfl⟩⟩
  obtain ⟨p,pMember,pMin⟩ := Finset.exists_min_image row Prod.fst rowNonempty
  have spec := Finset.mem_filter.mp pMember
  refine ⟨p,spec.1,?_,?_⟩
  · intro q member
    rw [spec.2]
    exact bottomMin q member
  · intro q member time
    exact pMin q (Finset.mem_filter.mpr ⟨member,time.trans spec.2⟩)

theorem horizontal_witness {Y : Finset Point} (satisfied : ArboralDilation.Satisfied (Y : Set Point))
    {a b : Point} (aMember : a ∈ Y) (bMember : b ∈ Y) (time : a.2 ≤ b.2)
    (cut : Int) (left : a.1 ≤ cut) (right : cut < b.1) :
    ∃ p q, HorizontalAdjacent Y p q ∧ Contains (a,b) p ∧ Contains (a,b) q ∧ p.1 ≤ cut ∧ cut < q.1 := by
  classical
  have ordered : a.1 < b.1 := by omega
  let low := Y.filter (fun p => Contains (a,b) p ∧ p.1 ≤ cut)
  have aLow : a ∈ low := by
    apply Finset.mem_filter.mpr
    exact ⟨aMember,by simp [Contains,min_eq_left ordered.le,max_eq_right ordered.le,time,left,ordered.le]⟩
  obtain ⟨p,pLow,pTime,pKey⟩ := top_right low ⟨a,aLow⟩
  obtain ⟨pMember,pBox,pLeft⟩ := Finset.mem_filter.mp pLow
  let high := Y.filter (fun q => Contains (a,b) q ∧ cut < q.1 ∧ p.2 ≤ q.2)
  have bHigh : b ∈ high := by
    apply Finset.mem_filter.mpr
    exact ⟨bMember,by simp [Contains,min_eq_left ordered.le,max_eq_right ordered.le,time,right,pBox.2.2.2,ordered.le]⟩
  obtain ⟨q,qHigh,qTime,qKey⟩ := bottom_left high ⟨b,bHigh⟩
  obtain ⟨qMember,qBox,qRight,pqTime⟩ := Finset.mem_filter.mp qHigh
  have pqKey : p.1 < q.1 := by omega
  have subBox : ∀ w, p.1 ≤ w.1 → w.1 ≤ q.1 → p.2 ≤ w.2 → w.2 ≤ q.2 → Contains (a,b) w := by
    intro w hlo hhi htlo hthi
    exact ⟨pBox.1.trans hlo,hhi.trans qBox.2.1,pBox.2.2.1.trans htlo,hthi.trans qBox.2.2.2⟩
  have sameTime : p.2 = q.2 := by
    by_contra different
    obtain ⟨w,wMember,wBox,notP,notQ⟩ := satisfied p.1 p.2 q.1 q.2 pMember qMember pqKey different
    simp only [ArboralDilation.InRectangle,min_eq_left pqTime,max_eq_right pqTime] at wBox
    have inBox := subBox w wBox.1 wBox.2.1 wBox.2.2.1 wBox.2.2.2
    by_cases wLeft : w.1 ≤ cut
    · have member : w ∈ low := Finset.mem_filter.mpr ⟨wMember,inBox,wLeft⟩
      have height := pTime w member
      have equalTime : w.2 = p.2 := by omega
      have key := pKey w member equalTime
      exact notP (Prod.ext (by omega) equalTime)
    · have member : w ∈ high := Finset.mem_filter.mpr ⟨wMember,inBox,by omega,wBox.2.2.1⟩
      have height := qTime w member
      have equalTime : w.2 = q.2 := by omega
      have key := qKey w member equalTime
      exact notQ (Prod.ext (by omega) equalTime)
  refine ⟨p,q,⟨pMember,qMember,pqKey,sameTime,?_⟩,pBox,qBox,pLeft,qRight⟩
  intro w wMember wTime between
  have inBox := subBox w between.1.le between.2.le (by omega) (by omega)
  by_cases wLeft : w.1 ≤ cut
  · have key := pKey w (Finset.mem_filter.mpr ⟨wMember,inBox,wLeft⟩) wTime
    omega
  · have key := qKey w (Finset.mem_filter.mpr ⟨wMember,inBox,by omega,by omega⟩) (wTime.trans sameTime)
    omega

end ChaCha.Paper20261030.Rectangles
