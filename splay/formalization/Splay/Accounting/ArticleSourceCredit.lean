import Splay.Accounting.ArticleAdmissibleWorklist
import Splay.Accounting.BoundaryCreditHistory
import Splay.Lazy.CanonicalBlockCount

namespace Splay.Accounting

open Splay.Lazy

/-- A first pass pays either the initial unit or a genuine fractional
reduction of a source whose size is below the selected cutoff. -/
def boundarySourceDemand {n : ℕ} (cutoff : ℕ) (source : Lazy.Block n) (rows : ℕ) : ℕ :=
  if source.passCount = 0 then 1 else
    if 0 < source.elements.length ∧ source.elements.length ≤ cutoff ∧
      source.elements.length ≤ 8 * rows then 1 else 0

theorem ArticleExecutedSourceMacro.boundaryCredit_drop {n cutoff : ℕ}
    {params : Interface.Parameters} {initial : Lazy.State n}
    (executed : ArticleExecutedSourceMacro params initial) :
    Interface.boundaryCredit cutoff executed.final.toInterface +
      boundarySourceDemand cutoff executed.source executed.batch.firstMatching.length ≤
        Interface.boundaryCredit cutoff initial.toInterface := by
  obtain ⟨charge, history⟩ := Interface.BoundaryCreditHistory.lift executed.trace.toInterface cutoff
  have bound := history.credit_bound
  have growth := executed.trace.blocks_length_eq
  rw [executed.blocks_length_eq] at growth
  have growthZero : Interface.totalBlockGrowth (eraseOperations executed.events) = 0 := by omega
  rw [growthZero, Nat.mul_zero, Nat.add_zero] at bound
  obtain ⟨winners, suffix, shape⟩ := executed.initialPass
  rw [shape] at history
  have found : initial.toInterface.block? executed.sourceId = some executed.source.toInterface := by
    unfold Interface.State.block? Lazy.State.toInterface
    simpa using congrArg (Option.map Lazy.Block.toInterface) executed.sourceFound
  have paid := history.initialPass_charge_le found
  change boundarySourceDemand cutoff executed.source executed.batch.firstMatching.length ≤ charge at paid
  omega

theorem ArticleSourceMacroChain.boundaryCredit_drop {n cutoff : ℕ}
    {params : Interface.Parameters} {initial : Lazy.State n}
    (chain : ArticleSourceMacroChain params initial) :
    Interface.boundaryCredit cutoff chain.final.toInterface +
      (chain.firstPassSources.map fun entry => boundarySourceDemand cutoff entry.1 entry.2).sum ≤
        Interface.boundaryCredit cutoff initial.toInterface := by
  induction chain with
  | nil => simp [final, firstPassSources]
  | cons head tail ih =>
    have paid := head.boundaryCredit_drop (cutoff := cutoff)
    simp only [final, firstPassSources, List.map_cons, List.sum_cons]
    omega

theorem ArticleAdmissibleWorklistExecution.boundaryCredit_drop
    {n key cutoff : ℕ} {snapshot : Splay.Rank.Snapshot n} {before : Splay.Tree.BST 0 n}
    {params : Interface.Parameters} {initial : Lazy.State n}
    {items : List (ArticleAdmissibleSourceWorkItem key snapshot before params initial)}
    (execution : ArticleAdmissibleWorklistExecution items) :
    Interface.boundaryCredit cutoff execution.chain.final.toInterface +
      (items.map fun item => boundarySourceDemand cutoff item.source item.batches.rows.length).sum ≤
        Interface.boundaryCredit cutoff initial.toInterface := by
  simpa only [execution.firstPassSources_eq, List.map_map, Function.comp_def] using
    execution.chain.boundaryCredit_drop (cutoff := cutoff)

end Splay.Accounting
