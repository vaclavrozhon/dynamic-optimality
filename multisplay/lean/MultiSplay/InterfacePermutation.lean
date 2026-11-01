import MultiSplay.InterfaceReindex
import MultiSplay.ListReindexExistence
import MultiSplay.InterfaceHistory

/-!
# Transport from an arbitrary current ordering of persistent histories

Only the proof's local naming is permuted. The target is an actual legal trace
starting from the original global state, with its immutable creator records.
The transported operation word has exactly the original activity and charges.
-/

namespace MultiSplay.InterfacePermutation

open Splay.Interface

variable {n : Nat}

def Equivalent (a b : State n) : Prop :=
  (a.blocks.map InterfaceHistory.observable).Perm (b.blocks.map InterfaceHistory.observable) ∧ a.value = b.value

theorem proxy {a b : State n} (same : Equivalent a b) :
    ∃ rename : Equiv.Perm Nat, ∃ middle : State n,
      InterfaceReindex.Related rename a middle ∧ InterfaceHistory.Equivalent middle b := by
  obtain ⟨rename, related⟩ := ListReindex.exists_related same.1
  have fresh : ∀ i, a.blocks.length ≤ i → rename i = i := by simpa using related.fresh
  let middle : State n := ⟨ListReindex.reorder rename a.blocks fresh, b.value⟩
  have realigned : InterfaceReindex.Related rename a middle := ⟨ListReindex.reorder_related rename a.blocks fresh, same.2⟩
  refine ⟨rename, middle, realigned, ?_, rfl⟩
  apply List.ext_getElem?
  intro j
  obtain ⟨i, rfl⟩ := rename.surjective j
  have eq := related.lookup i
  simp only [List.getElem?_map] at eq ⊢
  rw [realigned.blocks.lookup i]
  exact eq.symm

theorem Equivalent.valid {a b : State n} (same : Equivalent a b) {params : Parameters}
    (valid : a.Valid params) : b.Valid params := by
  obtain ⟨rename, middle, realigned, equivalent⟩ := proxy same
  exact equivalent.valid (realigned.valid valid)

theorem trace {a a' b : State n} (same : Equivalent a b) {params : Parameters}
    {word : List (Operation n)} (execution : Trace params a word a') :
    ∃ translated b', Trace params b translated b' ∧ Equivalent a' b' ∧
      translated.length = word.length ∧ totalActivity translated = totalActivity word ∧
      totalInserts translated = totalInserts word ∧ totalIncreases translated = totalIncreases word ∧
      totalDecreases translated = totalDecreases word := by
  obtain ⟨rename, middle, reindexed, initialEq⟩ := proxy same
  obtain ⟨middleAfter, reindexedRun, finalReindexed⟩ := InterfaceReindex.trace reindexed execution
  obtain ⟨final, actualRun, finalEq⟩ := InterfaceHistory.trace initialEq reindexedRun
  refine ⟨word.map (InterfaceBlockIds.operation rename), final, actualRun, ?_, by simp, by simp, by simp, by simp, by simp⟩
  exact ⟨(finalReindexed.blocks.perm.map InterfaceHistory.observable).trans (List.Perm.of_eq finalEq.1),
    finalReindexed.values.trans finalEq.2⟩

end MultiSplay.InterfacePermutation
