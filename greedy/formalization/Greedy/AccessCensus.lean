import Greedy.AccessJournal
import Greedy.JournalKinds

/-! The classified journal counts every actual access link exactly once. -/

namespace Greedy.AccessJournal

open Splay.Rank GreedyMerge.ActualLinks EntryJournal

 theorem program_link_count {n : ℕ} (rank : ℕ → ℕ) (kind : External n × External n → Kind)
    (events : List (External n × External n)) (ordinaryFree : ∀ event ∈ events, kind event ≠ .ordinary)
    (state : WeightedMemory.State (External n)) :
    total internal state (program rank kind events) + total boundary state (program rank kind events) = events.length := by
  induction events generalizing state with
  | nil => simp [program, total]
  | cons event rest ih =>
      have notOrdinary := ordinaryFree event (by simp)
      have tail := ih (fun next member => ordinaryFree next (by simp [member])) (advance rank kind state event)
      cases kindEq : kind event with
      | ordinary => exact False.elim (notOrdinary kindEq)
      | internal =>
          simp only [program, total, kindEq, internal, boundary, List.length_cons, Nat.cast_add, Nat.cast_one]
          change 1 + (0 + total internal (advance rank kind state event) (program rank kind rest)) +
            (0 + (0 + total boundary (advance rank kind state event) (program rank kind rest))) = _
          linarith
      | boundary =>
          simp only [program, total, kindEq, internal, boundary, List.length_cons, Nat.cast_add, Nat.cast_one]
          change 0 + (0 + total internal (advance rank kind state event) (program rank kind rest)) +
            (1 + (0 + total boundary (advance rank kind state event) (program rank kind rest))) = _
          linarith

end Greedy.AccessJournal
