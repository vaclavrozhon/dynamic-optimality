import DynamicOptimality.Funnel.Basic

/-!
# The triangle lemma with the repeated-column boundary retained

For a funnel switch with apex `p` and earlier endpoints `q < r`, every
occurrence strictly between `q` and `r` inside their closed key interval
lies on `r`'s column. Claiming the base rectangle is always empty would
be false for repeated keys; the word `[1,3,3,2]` is a counterexample.
-/

namespace DynamicOptimality.Funnel

variable {α : Type*} [LinearOrder α] {m : Nat}

private theorem triangle_left {word : Fin m → α} {active : Finset (Fin m)}
    {p q r s : Fin m} (turn : Switch word active p q r)
    (left : word q < word p) (right : word p < word r)
    (hs : s ∈ active) (qs : q < s) (sr : s < r)
    (keys : Between (word q) (word r) (word s)) : word s = word r := by
  have sp : s < p := sr.trans turn.2.1.2.2.1
  have bounds := (between_of_le (left.trans right).le).mp keys
  have ps : word p < word s := by
    apply lt_of_not_ge
    intro h
    exact turn.1.2.2.2.2 s hs qs sp (Or.inl ⟨bounds.1,h⟩)
  by_contra different
  have sKeyR : word s < word r := lt_of_le_of_ne bounds.2 different
  let candidates := active.filter (fun t => q < t ∧ t < r ∧
    word p < word t ∧ word t < word r)
  have nonempty : candidates.Nonempty := by
    exact ⟨s,Finset.mem_filter.mpr ⟨hs,qs,sr,ps,sKeyR⟩⟩
  let last := candidates.max' nonempty
  have lastMember : last ∈ candidates := Finset.max'_mem candidates nonempty
  obtain ⟨lastActive, qLast, lastR, pLastKey, lastRKey⟩ := Finset.mem_filter.mp lastMember
  have lastVisible : Visible word active p last := by
    refine ⟨turn.1.1,lastActive,lastR.trans turn.2.1.2.2.1,ne_of_gt pLastKey,?_⟩
    intro t ht lastT tp between
    have tBounds := (between_of_le pLastKey.le).mp ((between_comm _ _ _).mp between)
    have pT : word p < word t := by
      apply lt_of_not_ge
      intro h
      exact turn.1.2.2.2.2 t ht (qLast.trans lastT) tp
        (Or.inl ⟨left.le.trans tBounds.1,h⟩)
    rcases lt_trichotomy t r with tr | tr | rt
    · have member : t ∈ candidates := Finset.mem_filter.mpr
        ⟨ht,qLast.trans lastT,tr,pT,tBounds.2.trans_lt lastRKey⟩
      have maxBound : t ≤ last := Finset.le_max' candidates t member
      exact (not_lt_of_ge maxBound) lastT
    · subst t
      exact (not_le_of_gt lastRKey) tBounds.2
    · exact turn.2.1.2.2.2.2 t ht rt tp
        (Or.inr ⟨tBounds.1,(tBounds.2.trans_lt lastRKey).le⟩)
  exact turn.2.2.2.2 last lastActive qLast lastR lastVisible

/-- The base of a funnel switch is empty except for repeats on its later
endpoint's column. This includes boundary blockers in the closed rectangle. -/
theorem Switch.base_column {word : Fin m → α} {active : Finset (Fin m)}
    {p q r s : Fin m} (turn : Switch word active p q r)
    (hs : s ∈ active) (qs : q < s) (sr : s < r)
    (keys : Between (word q) (word r) (word s)) : word s = word r := by
  rcases turn.2.2.2.1 with sides | sides
  · exact triangle_left turn sides.1 sides.2 hs qs sr keys
  · exact triangle_left (α := OrderDual α) turn.dual sides.2 sides.1 hs qs sr keys.dual

end DynamicOptimality.Funnel
