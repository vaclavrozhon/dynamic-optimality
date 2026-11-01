import TangoSquared.Paper20261030.HorizontalWitness

/-! A widest rightward rectangle in a robust family has a private
vertical cut: within its closed time span no other rectangle crosses
that cut. Closed-corner robustness handles repeated key coordinates.
This is the robust-family version of the private-cut argument in the
independent-rectangle lower bound. -/

namespace TangoSquared.Paper20261030.Rectangles

def Rightward (r : Rectangle) : Prop := r.1.1 < r.2.1

def Crosses (r : Rectangle) (cut time : Int) : Prop :=
  r.1.1 ≤ cut ∧ cut < r.2.1 ∧ r.1.2 ≤ time ∧ time ≤ r.2.2

theorem same_start_order {P : Finset Point} {r s : Rectangle}
    (hr : InputFree P r) (hs : InputFree P s) (rightR : Rightward r) (rightS : Rightward s)
    (different : s ≠ r) (same : s.1 = r.1) (width : s.2.1-s.1.1 ≤ r.2.1-r.1.1) :
    s.2.1 < r.2.1 ∧ r.2.2 < s.2.2 := by
  have rTime := hr.1.2.2.1
  have sTime := hs.1.2.2.1
  have differentEnds : s.2 ≠ r.2 := fun equal => different (Prod.ext same equal)
  have differentStart : s.2 ≠ r.1 := by
    intro equal
    have := congrArg Prod.snd equal
    have := congrArg Prod.snd same
    omega
  have differentOtherStart : r.2 ≠ s.1 := by
    intro equal
    have := congrArg Prod.snd equal
    have := congrArg Prod.snd same
    omega
  have first : ¬ Contains r s.2 := fun inside =>
    (hr.2 s.2 hs.1.2.1 inside).elim differentStart differentEnds
  have last : ¬ Contains s r.2 := fun inside =>
    (hs.2 r.2 hr.1.2.1 inside).elim differentOtherStart differentEnds.symm
  rcases r with ⟨⟨a,t⟩,⟨b,u⟩⟩
  rcases s with ⟨⟨c,v⟩,⟨d,w⟩⟩
  simp only [Rightward] at rightR rightS
  simp only [Contains,min_eq_left rightR.le,max_eq_right rightR.le,
    min_eq_left rightS.le,max_eq_right rightS.le,Prod.mk.injEq] at first last same different
  dsimp only at width rTime sTime ⊢
  omega

theorem overlap_crosses_bottom {P : Finset Point} {r s : Rectangle}
    (hr : InputFree P r) (hs : InputFree P s) (rightR : Rightward r) (rightS : Rightward s)
    (different : s ≠ r) (independent : RobustPair r s)
    (width : s.2.1-s.1.1 ≤ r.2.1-r.1.1) {cut time : Int}
    (rCross : Crosses r cut time) (sCross : Crosses s cut time) :
    s.1 = r.1 ∨ (r.1.1 < s.1.1 ∧ s.1.2 < r.1.2 ∧ r.1.2 ≤ s.2.2) := by
  have rTime := hr.1.2.2.1
  have sTime := hs.1.2.2.1
  have first := hr.2 s.1 hs.1.1
  have last := hs.2 r.1 hr.1.1
  rcases independent with shared | ⟨rNo,sNo⟩
  · rcases r with ⟨⟨a,t⟩,⟨b,u⟩⟩
    rcases s with ⟨⟨c,v⟩,⟨d,w⟩⟩
    simp only [Rightward] at rightR rightS
    simp only [Contains,min_eq_left rightR.le,max_eq_right rightR.le,
      min_eq_left rightS.le,max_eq_right rightS.le,Prod.mk.injEq,Shared,Crosses]
      at first last different shared rCross sCross ⊢
    dsimp only at width rTime sTime
    omega
  · rw [noCorner_iff] at rNo sNo
    rcases r with ⟨⟨a,t⟩,⟨b,u⟩⟩
    rcases s with ⟨⟨c,v⟩,⟨d,w⟩⟩
    simp only [Rightward] at rightR rightS
    simp only [Contains,min_eq_left rightR.le,max_eq_right rightR.le,
      min_eq_left rightS.le,max_eq_right rightS.le,Prod.mk.injEq,Crosses]
      at rNo sNo rCross sCross ⊢
    dsimp only at width rTime sTime
    omega

theorem robust_private_cut {P : Finset Point} {R : Finset Rectangle}
    (family : RobustFamily P R) (rightward : ∀ r ∈ R, Rightward r) (nonempty : R.Nonempty) :
    ∃ r ∈ R, ∃ cut : Int, r.1.1 ≤ cut ∧ cut < r.2.1 ∧
      ∀ s ∈ R, s ≠ r → ∀ time, r.1.2 ≤ time → time ≤ r.2.2 → ¬ Crosses s cut time := by
  classical
  obtain ⟨r,rMember,widest⟩ := Finset.exists_max_image R (fun s => s.2.1-s.1.1) nonempty
  let starts := (R.erase r).filter (fun s => s.1 = r.1)
  let edges := insert r.1.1 (starts.image (fun s => s.2.1))
  obtain ⟨cut,cutMember,cutMax⟩ := Finset.exists_max_image edges id ⟨r.1.1,Finset.mem_insert_self _ _⟩
  dsimp only [id] at cutMax
  have rRight := rightward r rMember
  have cutLeft : r.1.1 ≤ cut := cutMax _ (Finset.mem_insert_self _ _)
  have startsSpec : ∀ s ∈ starts, s ∈ R ∧ s ≠ r ∧ s.1 = r.1 ∧ s.2.1 < r.2.1 ∧ r.2.2 < s.2.2 := by
    intro s member
    obtain ⟨erased,same⟩ := Finset.mem_filter.mp member
    obtain ⟨different,inR⟩ := Finset.mem_erase.mp erased
    have order := same_start_order (family.1 r rMember) (family.1 s inR) rRight
      (rightward s inR) different same (widest s inR)
    exact ⟨inR,different,same,order⟩
  have cutRight : cut < r.2.1 := by
    obtain atStart | member := Finset.mem_insert.mp cutMember
    · simpa only [atStart,Rightward] using rRight
    · obtain ⟨s,inStarts,edge⟩ := Finset.mem_image.mp member
      rw [← edge]
      exact (startsSpec s inStarts).2.2.2.1
  refine ⟨r,rMember,cut,cutLeft,cutRight,?_⟩
  intro s sMember different time timeLo timeHi sCross
  have rCross : Crosses r cut time := ⟨cutLeft,cutRight,timeLo,timeHi⟩
  obtain same | cross := overlap_crosses_bottom (family.1 r rMember) (family.1 s sMember)
    rRight (rightward s sMember) different (family.2 r rMember s sMember different.symm)
    (widest s sMember) rCross sCross
  · have inStarts : s ∈ starts := Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨different,sMember⟩,same⟩
    have edgeBound := cutMax s.2.1 (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨s,inStarts,rfl⟩))
    have cutBound := sCross.2.1
    omega
  · obtain atStart | member := Finset.mem_insert.mp cutMember
    · have xLo := sCross.1
      omega
    · obtain ⟨previous,previousMember,edge⟩ := Finset.mem_image.mp member
      obtain ⟨inR,_,same,_,above⟩ := startsSpec previous previousMember
      have distinct : s ≠ previous := by
        intro equal
        have := congrArg Prod.fst same
        subst s
        omega
      have contain : Contains s (previous.2.1,r.1.2) := by
        have direction := rightward s sMember
        simp only [Contains,min_eq_left direction.le,max_eq_right direction.le]
        have xLo := sCross.1
        have xHi := sCross.2.1
        exact ⟨by omega,by omega,cross.2.1.le,cross.2.2⟩
      have corner : Corner previous (previous.2.1,r.1.2) := ⟨.inr rfl,.inl (congrArg Prod.snd same).symm⟩
      obtain shared | disjoint := family.2 s sMember previous inR distinct
      · have sameX := congrArg Prod.fst same
        have sameTime := congrArg Prod.snd same
        have cutBound := sCross.2.1
        simp only [Shared,Prod.ext_iff] at shared
        omega
      · exact disjoint.1 _ corner contain

end TangoSquared.Paper20261030.Rectangles
