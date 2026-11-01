import BlockLifetime

/-! An elementary label update from snapshot t to t+1 is crossed by
entries minJoin ≤ t < maxJoin. Since historical family order uses the
predicate `cut ≤ join`, its cut parameter must be t+1, not t. -/
namespace GreedyMerge.CutChronology
open GreedyForest

example : min 2 5 ≤ 2 ∧ 2 < max 2 5 := by norm_num

/-- The old witness has no straddler, despite a counted crossing. -/
theorem old_cut_not_straddled :
    ¬ Straddles (fun x : ℕ => decide (2 ≤ x)) ({2, 5} : Finset ℕ) := by
  rw [straddles_nat_cut_iff]
  simp

/-- Incrementing the cut matches the actual elementary-event convention. -/
theorem corrected_cut_straddled :
    Straddles (fun x : ℕ => decide (3 ≤ x)) ({2, 5} : Finset ℕ) := by
  rw [straddles_nat_cut_iff]
  exact ⟨2, by simp, 5, by simp, by omega, by omega⟩

theorem event_interval_iff_cut (winnerJoin loserJoin time : ℕ) :
    (min winnerJoin loserJoin ≤ time ∧ time < max winnerJoin loserJoin) ↔
      Straddles (fun x : ℕ => decide (time + 1 ≤ x))
        ({winnerJoin, loserJoin} : Finset ℕ) := by
  rw [straddles_nat_cut_iff]
  constructor
  · intro h
    by_cases hw : winnerJoin ≤ time
    · exact ⟨winnerJoin, by simp, loserJoin, by simp, by omega, by omega⟩
    · exact ⟨loserJoin, by simp, winnerJoin, by simp, by omega, by omega⟩
  · rintro ⟨x, hx, y, hy, hxt, hty⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega

end GreedyMerge.CutChronology
#print axioms GreedyMerge.CutChronology.event_interval_iff_cut
