import MultiSplay.FramedSplay
import Splay.Accounting.ArticleMacroBoundaryCredit

/-!
# One boundary-credit potential for all active component histories

The boundary credit depends only on payload length, mode, and pass count.
It is invariant under element embeddings, local proxies for retired creators,
and permutations of block names. Passive records contribute the same additive
term at both endpoints, so the article's boundary estimate telescopes globally.
-/

namespace MultiSplay

open Splay.Interface

@[simp] theorem boundaryCredit_observable {n : Nat} (cutoff : Nat) (block : Block n) :
    boundaryBlockCredit cutoff (InterfaceHistory.observable block) = boundaryBlockCredit cutoff block := by
  cases mode : block.mode <;> simp [boundaryBlockCredit, InterfaceHistory.observable, mode]

@[simp] theorem boundaryCredit_embedded {n m : Nat} (cutoff : Nat) (embedding : Element n → Element m) (block : Block n) :
    boundaryBlockCredit cutoff (InterfaceEmbedding.block embedding block) = boundaryBlockCredit cutoff block := by
  cases mode : block.mode <;> simp [boundaryBlockCredit, InterfaceEmbedding.block, mode]

theorem InterfacePermutation.Equivalent.boundaryCredit {n : Nat} {a b : State n}
    (same : InterfacePermutation.Equivalent a b) (cutoff : Nat) : boundaryCredit cutoff a = boundaryCredit cutoff b := by
  have equality := (same.1.map (boundaryBlockCredit cutoff)).sum_eq
  simpa [Splay.Interface.boundaryCredit, List.map_map, Function.comp_def] using equality

theorem InterfacePrefix.boundaryCredit {n m : Nat} (embedding : Element n → Element m)
    (frame : State m) (component : State n) (cutoff : Nat) :
    boundaryCredit cutoff (InterfacePrefix.state embedding frame component) = boundaryCredit cutoff frame + boundaryCredit cutoff component := by
  simp [InterfacePrefix.state, Splay.Interface.boundaryCredit, List.map_append, List.map_map, Function.comp_def]

theorem InterfaceFramedTrace.Framed.boundaryCredit {n m : Nat} {params : Parameters}
    {component : State n} {whole : State m} (framed : InterfaceFramedTrace.Framed params component whole) (cutoff : Nat) :
    boundaryCredit cutoff whole = boundaryCredit cutoff framed.frame + boundaryCredit cutoff component := by
  rw [← framed.equivalent.boundaryCredit cutoff, InterfacePrefix.boundaryCredit]

namespace FramedSplay

open Splay.Accounting Splay.Lazy Splay.Rank

/-- This is the article estimate on the actual shared state. The only geometric
premise is the same unbroken-block invariant required by the local theorem. -/
theorem Realization.boundary_credit {n m cutoff : Nat} {params : Parameters}
    {before after : ArticleCheckpoint n} {step : ArticleMacro params before after}
    {whole : Splay.Interface.State m} {initial : InterfaceFramedTrace.Framed params before.state.toInterface whole}
    (run : Realization step whole initial)
    (exempt : params.exemptPasses = 2) (numerator : params.matchingNumerator = 1) (denominator : params.matchingDenominator = 8)
    (unbroken : PassedBlocksUnbroken (Snapshot.ofTree before.comparison).withTruePriority before.splay before.state) :
    cutoff * (2 * step.boundaryCount) + 4 * cutoff * boundaryCredit cutoff run.final ≤
      4 * cutoff * boundaryCredit cutoff whole + 4 * cutoff * boundaryCreditCapacity cutoff * step.birthBudget +
        16 * totalActivity run.operations := by
  have paid := step.boundary_credit_estimate exempt numerator denominator (cutoff := cutoff) unbroken
  rw [run.framed.boundaryCredit, initial.boundaryCredit, run.frame_eq, run.activity_eq]
  nlinarith

end FramedSplay
end MultiSplay
