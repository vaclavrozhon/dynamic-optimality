import TangoSquared.CyclicGapAccounting

/-! Every actual source exit turn triggers its outgoing delayed gap. -/
namespace TangoSquared.SourceExit

open CyclicRuns TurnAccounting GapChunks CyclicGapAccounting

variable {α C : Type*} [LinearOrder α] [LinearOrder C]

/-- The source run's exit to the first actual intervening coarse run. -/
def sourceExit (c : Chunk (Block α)) : Nat :=
  (Run.mk c.source.micro
    (decide (c.source.last < (c.middle.headD c.source).first))).exitTurn

theorem sourceExit_le_one (c : Chunk (Block α)) : sourceExit c ≤ 1 := by
  cases hm : c.source.micro with
  | nil => simp [sourceExit, Run.exitTurn, hm]
  | cons a as =>
    simp only [sourceExit, Run.exitTurn, hm, turn]
    split <;> omega

/-- An exit turn meets an opposite-side query at the first intervening run, so
its actual outgoing gap has a delayed charge. -/
theorem sourceExit_le_delayed (coarse : α → C) (ordered : Monotone coarse) (cell : C)
    (c : Chunk (Block α)) (next : Block α)
    (hsource : coarse c.source.first = cell) (hnext : coarse next.first = cell)
    (homogeneous : c.source.Homogeneous coarse)
    (adjacent : AdjacentDistinct coarse (c.word ++ [next])) :
    sourceExit c ≤ (outgoingGap coarse cell c next).delayed := by
  by_cases hz : sourceExit c = 0
  · rw [hz]; exact Nat.zero_le _
  have hone : sourceExit c = 1 := by have := sourceExit_le_one c; omega
  obtain ⟨hn, _⟩ := outgoing_middle_last coarse cell c next hsource hnext adjacent
  cases hm : c.middle with
  | nil => exact False.elim (hn hm)
  | cons d ds =>
    have hfirst : coarse c.source.first ≠ coarse d.first := by
      have ha := adjacent
      simp only [Chunk.word, hm, List.cons_append, AdjacentDistinct] at ha
      exact ha.1
    have hout : coarse d.first ≠ cell := by rw [← hsource]; exact Ne.symm hfirst
    have hs : coarse c.source.last = cell :=
      (Block.homogeneous_last coarse c.source homogeneous).trans hsource
    have hd := direction_coarse coarse ordered c.source.last d.first (by rw [hs]; exact Ne.symm hout)
    rw [hs] at hd
    have hturn : decide (cell < coarse d.first) ≠ c.source.micro.getLastD false := by
      intro he
      cases hmi : c.source.micro with
      | nil => simp [sourceExit, hmi, Run.exitTurn] at hone
      | cons a as =>
        have hzero : sourceExit c = 0 := by
          simp only [sourceExit, hmi, Run.exitTurn, hm, List.headD_cons, hd]
          have he' : decide (cell < coarse d.first) = as.getLastD a := by
            simpa only [hmi, List.getLastD_cons] using he
          rw [he', turn_self]
        omega
    have hdelayed : (outgoingGap coarse cell c next).delayed = 1 := by
      apply (outgoingGap_delayed_iff coarse cell c next).mpr
      refine ⟨d.first, ?_, hout, hturn⟩
      simp [hm, Block.word]
    rw [hone, hdelayed]

end TangoSquared.SourceExit
