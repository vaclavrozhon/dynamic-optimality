import ChaCha.Paper20261030.ExitWindows

/-!
# Reversed mixed turn at the end of an exit window

The turn has order `(reverse h', reverse h, reverse q)`. With repeated
keys, `h` is replaced by its last equal-key occurrence before `h'`.
-/

namespace ChaCha.Paper20261030.Rectangles

theorem previousDifferent_reverse {P : Finset Point} {p q : Point}
    (h : PreviousDifferent P p q) :
    NextDifferent (P.image reversePoint) (reversePoint q) (reversePoint p) := by
  refine ⟨Finset.mem_image.mpr ⟨q,h.2.1,rfl⟩,
    Finset.mem_image.mpr ⟨p,h.1,rfl⟩,?_,Ne.symm h.2.2.2.1,?_⟩
  · dsimp [reversePoint]
    have := h.2.2.1
    omega
  · intro z hz hqz hzp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    apply h.2.2.2.2 a ha
    · dsimp [reversePoint] at hzp
      omega
    · dsimp [reversePoint] at hqz
      omega

theorem previousDifferent_before_internal_end {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {s q h h' v u : Point}
    (hq : q ∈ P) (hsq : s.2 < q.2) (hout : f q.1 ≠ f s.1)
    (hnext : NextInternal P f s h) (hnd : NextDifferent P h h')
    (hvu : PreviousDifferent P v u) (hvcolor : f v.1 = f s.1)
    (hucolor : f u.1 = f s.1) (huh' : u.2 < h'.2) : u.2 < q.2 := by
  by_contra hn
  have hqu : q.2 < u.2 := by
    by_cases he : q.2 = u.2
    · have heq := hP q hq u hvu.2.1 he
      exact (hout ((congrArg f (congrArg Prod.fst heq)).trans hucolor)).elim
    · omega
  have hqv : q.2 < v.2 := by
    by_cases he : q.2 = v.2
    · have heq := hP q hq v hvu.1 he
      exact (hout ((congrArg f (congrArg Prod.fst heq)).trans hvcolor)).elim
    by_contra hn'
    have hqkey := hvu.2.2.2.2 q hq (by omega) hqu
    exact hout ((congrArg f hqkey).trans hucolor)
  have hvInt := previousDifferent_internalStart hP f hvu (hvcolor.trans hucolor.symm)
  have hhv := hnext.2.2 v (hvcolor ▸ hvInt) (lt_trans hsq hqv)
  have hvh' : v.2 < h'.2 := lt_trans hvu.2.2.1 huh'
  have hvkey : v.1 = h.1 := by
    by_cases he : v.2 = h.2
    · exact congrArg Prod.fst (hP v hvu.1 h hnd.1 he)
    · exact hnd.2.2.2.2 v hvu.1 (by omega) hvh'
  have hukey := hnd.2.2.2.2 u hvu.2.1
    (by have := hvu.2.2.1; omega) huh'
  exact hvu.2.2.2.1 (hvkey.trans hukey.symm)

theorem mixed_reverse_at_next_internal {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {s q h h' : Point}
    (hq : q ∈ P) (hsq : s.2 < q.2) (hqh : q.2 < h.2)
    (hout : f q.1 ≠ f s.1)
    (hnext : NextInternal P f s h) (hnd : NextDifferent P h h')
    (hhcolor : f h.1 = f s.1) (hh'color : f h'.1 = f s.1)
    (hturn : Turn q h h') : MixedTurn (P.image reversePoint) f (reversePoint h') := by
  obtain ⟨v,hvh'⟩ := exists_previous hnd.2.1 ⟨h,hnd.1,hnd.2.2.1⟩
  have hhv := previous_ge hvh' hnd.1 hnd.2.2.1
  have hvkey : v.1 = h.1 := by
    by_cases he : v.2 = h.2
    · exact congrArg Prod.fst (hP v hvh'.1 h hnd.1 he)
    · exact hnd.2.2.2.2 v hvh'.1 (by omega) hvh'.2.2.1
  have hpd : PreviousDifferent P v h' := by
    refine ⟨hvh'.1,hvh'.2.1,hvh'.2.2.1,
      by simpa only [hvkey] using hnd.2.2.2.1,?_⟩
    intro z hz hvz hzh'
    exact (hvh'.2.2.2 z hz hvz hzh').elim
  have hqvh' : Turn q v h' :=
    ⟨lt_of_lt_of_le hqh hhv,hvh'.2.2.1,by simpa only [hvkey] using hturn.2.2⟩
  refine ⟨reversePoint v,reversePoint q,previousDifferent_reverse hpd,
    ?_,Finset.mem_image.mpr ⟨q,hq,rfl⟩,?_,turn_reverse hqvh',?_⟩
  · change f h'.1 = f v.1
    rw [hvkey]
    exact hh'color.trans hhcolor.symm
  · exact fun he => hout (he.trans hh'color)
  · intro a b hab hacolor hbcolor hstart
    obtain ⟨u,hu,huEq⟩ := Finset.mem_image.mp hab.1
    obtain ⟨v',hv',hvEq⟩ := Finset.mem_image.mp hab.2.1
    subst a
    subst b
    have hpd' := nextDifferent_reverse hab
    have hPP : (P.image reversePoint).image reversePoint = P :=
      timeReversal.point_image_image P
    rw [hPP,reversePoint_involutive u,reversePoint_involutive v'] at hpd'
    have huq := previousDifferent_before_internal_end hP f hq hsq hout hnext hnd hpd'
      (hbcolor.trans hh'color) (hacolor.trans hh'color)
      (by dsimp [reversePoint] at hstart; omega)
    dsimp [reversePoint]
    omega

end ChaCha.Paper20261030.Rectangles
