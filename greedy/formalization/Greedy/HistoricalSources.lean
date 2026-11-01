import Greedy.RunGrowthInvariant
import Greedy.RunJournal

/-!
# Every access source is covered by one final historical book

The final book covers not only the final live fragments, but the frozen
sources of every earlier access. This follows by composing literal book
extensions along the same execution. The definition includes states before
administration as well as the converted sources used by each access.
-/

namespace Greedy.GrowthJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.GrowthBook GreedyMerge.GrowthWindows GreedyMerge.ActualLinks

theorem HeapCovered.mono {n : ℕ} {books finalBooks : HeapBooks n} {states : HeapSides n}
    (covered : HeapCovered books states) (extension : HeapExtends books finalBooks) : HeapCovered finalBooks states :=
  fun owner side block member => (covered owner side block member).mono extension

def AllSourcesCovered {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)}
    (books : HeapBooks n) : Execution.Run K first last requests → Prop
  | .done state => HeapCovered books state.blocks
  | .rotate (first := first) _ _ _ rest => HeapCovered books first.blocks ∧ AllSourcesCovered books rest
  | .access (first := first) request _ _ _ _ rest =>
      HeapCovered books first.blocks ∧ HeapCovered books (RunJournal.prepared first request) ∧ AllSourcesCovered books rest

 theorem exists_all_sources {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K first last requests)
    (books : HeapBooks n) (inv : Invariant first.clock first.next first.blocks books) :
    ∃ finalBooks, Invariant last.clock last.next last.blocks finalBooks ∧ HeapExtends books finalBooks ∧
      AllSourcesCovered finalBooks execution := by
  induction execution generalizing books with
  | done state => exact ⟨books, inv, HeapExtends.refl _, inv.covered⟩
  | @rotate first last after depth requests rotation data valid rest ih =>
      obtain ⟨nextBooks, nextInv, headExtension⟩ := complete_rotation_history first after rotation K data books inv
      obtain ⟨finalBooks, finalInv, tailExtension, sources⟩ := ih nextBooks nextInv
      have extension := headExtension.trans tailExtension
      exact ⟨finalBooks, finalInv, extension, inv.covered.mono extension, sources⟩
  | @access first last requests request root decomposition data valid rest ih =>
      let selected := fun (owner : External n) (_ : Bool) => decide (owner = Execution.source request)
      let converted := RunJournal.prepared first request
      let convertedBooks := convertHeapBooks selected first.next first.blocks books
      let afterBooks := runBook first.clock convertedBooks data.events
      have convertedInv := convertHeap_invariant first.comparator.externalDepth selected first.next first.blocks books inv
      have afterInv : Invariant (Execution.afterAccess first request K decomposition data).clock
          (Execution.afterAccess first request K decomposition data).next
          (Execution.afterAccess first request K decomposition data).blocks afterBooks :=
        runBook_invariant (Execution.source request) _ _ first.clock _ converted convertedBooks data.events convertedInv
      obtain ⟨finalBooks, finalInv, tailExtension, sources⟩ := ih afterBooks afterInv
      have fromConverted := (runBook_extends first.clock convertedBooks data.events).trans tailExtension
      have extension := (convertHeapBooks_extends selected first.next first.blocks books).trans fromConverted
      exact ⟨finalBooks, finalInv, extension, inv.covered.mono extension, convertedInv.covered.mono fromConverted, sources⟩

theorem initialized_all_sources {n : ℕ} (initial comparator : BST 0 n) (K : ℤ)
    {last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K (Execution.initial initial comparator K) last requests) :
    ∃ finalBooks, Invariant last.clock last.next last.blocks finalBooks ∧ AllSourcesCovered finalBooks execution := by
  obtain ⟨books, inv, _, covered⟩ := exists_all_sources execution
    (GreedyMerge.GrowthBook.initial (Snapshot.ofTree comparator) (Execution.initial initial comparator K).refined.tree K)
    (initial_invariant (Snapshot.ofTree comparator) _ K)
  exact ⟨books, inv, covered⟩

end Greedy.GrowthJournal
