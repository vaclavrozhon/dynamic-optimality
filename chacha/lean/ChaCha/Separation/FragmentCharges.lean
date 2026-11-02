import ChaCha.Paper20261030.FragmentDecomposition

/-!
# Concrete fragment charges when one coarse cell is a singleton key

An actual DOWN-to-UP event must leave a cell containing two distinct keys.
If every other cell consists of one exceptional key, that event is charged
to an occurrence of this key. The two vanishing lemmas account for inactive
parts of the fixed reference, without suppressing them in the definition.
-/

namespace ChaCha.Separation

open Paper20261030 Paper20261030.Rectangles Paper20261030.Dyadic

theorem downUp_exceptional_key {points : Finset Point} (valid : Instance points)
    (projection : Int → Int) (exception : Int) (different : projection exception ≠ 0)
    (cells : ∀ point ∈ points, projection point.1 = 0 ∨ point.1 = exception)
    {query : Point} (event : DownUpAt points projection query) : query.1 = exception := by
  obtain ⟨previous,adjacent,state⟩ := event
  obtain ⟨⟨older,olderDifferent,sameCell⟩,exitCell⟩ :=
    (downUp_iff_exit_edge valid projection adjacent).mp state
  have previousZero : projection previous.1 = 0 := by
    rcases cells previous adjacent.1 with zero | singleton
    · exact zero
    · rcases cells older olderDifferent.1 with zero | olderSingleton
      · exact (different (by rw [← singleton,← sameCell,zero])).elim
      · exact (olderDifferent.2.2.2.1 (olderSingleton.trans singleton.symm)).elim
  rcases cells query adjacent.2.1 with zero | singleton
  · exact (exitCell (previousZero.trans zero.symm)).elim
  · exact singleton

theorem fragment_event_charge {points : Finset Point} (valid : Instance points)
    (projection : Int → Int) (exception : Int) (different : projection exception ≠ 0)
    (cells : ∀ point ∈ points, projection point.1 = 0 ∨ point.1 = exception) :
    eventCount points (DownUpAt points projection) ≤
      (points.filter (fun point => point.1 = exception)).card := by
  classical
  rw [eventCount_eq_card]
  apply Finset.card_le_card
  intro point member
  obtain ⟨present,event⟩ := Finset.mem_filter.mp member
  exact Finset.mem_filter.mpr ⟨present,downUp_exceptional_key valid projection exception different cells event⟩

theorem fragment_event_zero_of_constant_projection {points : Finset Point}
    (valid : Instance points) (projection : Int → Int) (value : Int)
    (constant : ∀ point ∈ points, projection point.1 = value) :
    eventCount points (DownUpAt points projection) = 0 := by
  classical
  rw [eventCount_eq_card,Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro point member
  obtain ⟨present,previous,adjacent,state⟩ := Finset.mem_filter.mp member
  have different := ((downUp_iff_exit_edge valid projection adjacent).mp state).2
  exact different ((constant previous adjacent.1).trans (constant point present).symm)

theorem fragment_event_zero_of_constant_keys {points : Finset Point}
    (projection : Int → Int) (key : Int) (constant : ∀ point ∈ points, point.1 = key) :
    eventCount points (DownUpAt points projection) = 0 := by
  classical
  rw [eventCount_eq_card,Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro point member
  obtain ⟨present,previous,adjacent,⟨older,distinct,sameCell⟩,next⟩ := Finset.mem_filter.mp member
  exact distinct.2.2.2.1 ((constant older distinct.1).trans (constant previous adjacent.1).symm)

theorem fragmentAlternations_constant {a b : Nat} (reference : DepthTree a b)
    (points : Finset Point) (key : Int) (constant : ∀ point ∈ points, point.1 = key) :
    fragmentAlternations reference points = 0 := by
  induction reference generalizing points key with
  | leaf => rfl
  | @node a b cut ha hb left right ihl ihr =>
      rw [fragmentAlternations,fragment_event_zero_of_constant_keys _ key constant]
      have projected : fragmentAlternations left (project (coarsen (b+1) (cut+1)) points) = 0 := by
        apply ihl _ (coarsen (b+1) (cut+1) key)
        intro point member
        obtain ⟨original,present,rfl⟩ := Finset.mem_image.mp member
        change coarsen (b+1) (cut+1) original.1 = _
        rw [constant original present]
      rw [projected]
      simp only [Nat.zero_add]
      apply Finset.sum_eq_zero
      intro index present
      apply ihr _ key
      exact fun point member => constant point (Finset.mem_filter.mp member).1

theorem coarsen_small {cut top : Nat} (below : cut < top) {key : Int}
    (small : 0 ≤ key ∧ key ≤ 1) : coarsen (top+1) (cut+1) key = 0 := by
  have denominator : (2 : Int) ≤ 2^(top-cut) := by
    calc
      (2 : Int) = 2^1 := by simp
      _ ≤ 2^(top-cut) := pow_le_pow_right₀ (by decide) (by omega)
  simp only [coarsen,Nat.add_sub_add_right]
  exact Int.ediv_eq_zero_of_lt small.1 (by omega)

/-- Keys zero and one branch only at the final primary level, so no
secondary fragment can observe both directions. -/
theorem fragmentAlternations_small {a b : Nat} (reference : DepthTree a b)
    (points : Finset Point) (valid : Instance points)
    (small : ∀ point ∈ points, 0 ≤ point.1 ∧ point.1 ≤ 1) :
    fragmentAlternations reference points = 0 := by
  induction reference generalizing points with
  | leaf => rfl
  | @node a b cut ha hb left right ihl ihr =>
      have zero : ∀ point ∈ points, coarsen (b+1) (cut+1) point.1 = 0 :=
        fun point member => coarsen_small hb (small point member)
      rw [fragmentAlternations,fragment_event_zero_of_constant_projection valid _ 0 zero]
      have projected : fragmentAlternations left (project (coarsen (b+1) (cut+1)) points) = 0 := by
        apply fragmentAlternations_constant _ _ 0
        intro point member
        obtain ⟨original,present,rfl⟩ := Finset.mem_image.mp member
        exact zero original present
      rw [projected]
      simp only [Nat.zero_add]
      apply Finset.sum_eq_zero
      intro index present
      exact ihr _ (instance_fiber valid _ index)
        (fun point member => small point (Finset.mem_filter.mp member).1)

end ChaCha.Separation
