import MultiSplay.IntervalWitnesses
import ChaCha.PeriodicAccounting

/-! # Actual event budgets for arbitrary secondary interval hierarchies -/

namespace MultiSplay.IntervalLower

open ChaCha
open ChaCha.Primary ChaCha.Witnesses ChaCha.MTR ChaCha.MTR.Tree ChaCha.NormalizedWords

theorem eventSum_budget {H : Nat} {hierarchy : DepthTree 0 H} (qs : Finset Gadget) (valid : ∀ q ∈ qs, Valid hierarchy q)
    (t : Tree Key) (history xs : List Key)
    (hn : Normalized (initialPreference H t) H (history ++ xs))
    (hs : Successful t (history ++ xs)) (hl : OnLeaves H (history ++ xs)) :
    eventSum H qs history xs ≤ internalSearchVisits (run t history) xs := by
  induction xs generalizing history with
  | nil => simp [eventSum, internalSearchVisits]
  | cons x xs ih =>
    have hs' := (successful_append t history (x :: xs)).mp hs
    obtain ⟨d, hd⟩ := hs'.2.1
    have hone : OneFlip (initialPreference H t) H history x := hn history x xs rfl
    have hl' : OnLeaves H (history ++ [x]) := by
      intro y hy
      apply hl y
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · simp [hy]
      · simp
    have hb := activeEvents_budget qs valid hl' (initialPreference H t) hone t hs'.1 d hd
    have hi := ih (history ++ [x])
      (by simpa only [List.append_assoc, List.singleton_append] using hn)
      (by simpa only [List.append_assoc, List.singleton_append] using hs)
      (by simpa only [List.append_assoc, List.singleton_append] using hl)
    have hr : run t (history ++ [x]) = moveToRoot x (run t history) := by
      rw [run_append]
      rfl
    rw [hr] at hi
    simp only [eventSum, internalSearchVisits, hd, Option.getD_some]
    omega


theorem four_period_budget {H : Nat} {hierarchy : DepthTree 0 H} {tree : Tree Key} {word : List Key}
    (gadgets : Finset Gadget) (valid : ∀ gadget ∈ gadgets, Valid hierarchy gadget)
    (normal : AmbientNormalized H tree word) (successful : Successful tree word)
    (leaves : OnLeaves H word) (closed : run tree word = tree) :
    eventSum H gadgets [] (word++(word++(word++word))) ≤ 4 * internalSearchVisits tree word := by
  have paid := eventSum_budget gadgets valid tree [] (repeatWord word 4)
    (by simpa only [List.nil_append] using history_normalized_repeatWord normal successful leaves closed 4)
    (by simpa only [List.nil_append] using successful_repeatWord successful closed 4)
    (by simpa only [List.nil_append] using leaves_repeatWord leaves 4)
  change eventSum H gadgets [] (repeatWord word 4) ≤ internalSearchVisits tree (repeatWord word 4) at paid
  rw [internalSearchVisits_repeatWord closed] at paid
  simpa only [repeatWord, List.append_nil] using paid

end MultiSplay.IntervalLower
