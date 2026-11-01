import Splay.Accounting.ArticleGlobalFirstLeave

namespace Splay.Accounting

open Splay.Lazy

/-- A dependent sequence of already constructed one-source article macros.
Each macro starts at the exact stable endpoint of its predecessor. -/
inductive ArticleSourceMacroChain {n : ℕ}
    (params : Interface.Parameters) : Lazy.State n → Type
  | nil (state : Lazy.State n) (stable : state.Stable params) :
      ArticleSourceMacroChain params state
  | cons {state : Lazy.State n}
      (head : ArticleExecutedSourceMacro params state)
      (tail : ArticleSourceMacroChain params head.final) :
      ArticleSourceMacroChain params state

namespace ArticleSourceMacroChain

/-- The actual source before each first pass, with that pass's matching size. -/
def firstPassSources {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n} :
    ArticleSourceMacroChain params state → List (Lazy.Block n × ℕ)
  | .nil _ _ => []
  | .cons head tail => (head.source, head.batch.firstMatching.length) :: tail.firstPassSources

/-- Actual equal-valued pairings paid by the geometric loss of the macros. -/
def goodCount {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n} :
    ArticleSourceMacroChain params state → ℕ
  | .nil _ _ => 0
  | .cons head tail => head.goodCount + tail.goodCount

/-- Concatenate the exact rich event lists in execution order. -/
def events {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n} :
    ArticleSourceMacroChain params state → List (Lazy.Event n)
  | .nil _ _ => []
  | .cons head tail => head.events ++ tail.events

/-- The endpoint after every source macro has run. -/
def final {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n} :
    ArticleSourceMacroChain params state → Lazy.State n
  | .nil state _ => state
  | .cons _ tail => tail.final

/-- The source-local loser batches in the same order as their rich macros. -/
def batches {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n} :
    ArticleSourceMacroChain params state →
      List (ArticleSourceLoserBatch n)
  | .nil _ _ => []
  | .cons head tail => head.batch :: tail.batches

/-- Local trace proofs compose to one exact request-internal rich trace. -/
theorem trace {n : ℕ} {params : Interface.Parameters}
    {state : Lazy.State n}
    (chain : ArticleSourceMacroChain params state) :
    Lazy.Trace params state chain.events chain.final := by
  induction chain with
  | nil state stable =>
      exact Lazy.Trace.nil stable.valid
  | cons head tail ih =>
      exact head.trace.append ih

/-- Every dependent chain ends in a stable rich state. -/
theorem finalStable {n : ℕ} {params : Interface.Parameters}
    {state : Lazy.State n}
    (chain : ArticleSourceMacroChain params state) :
    chain.final.Stable params := by
  induction chain with
  | nil state stable =>
      exact stable
  | cons head tail ih =>
      exact ih

/-- The complete source fold creates no new element incidences. -/
theorem inserts_eq_zero {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (chain : ArticleSourceMacroChain params state) :
    Interface.totalInserts (eraseOperations chain.events) = 0 := by
  induction chain with
  | nil => rfl
  | cons head tail ih =>
      have appendCount : ∀ a b : List (Interface.Operation n),
          Interface.totalInserts (a ++ b) = Interface.totalInserts a + Interface.totalInserts b := by
        intros; simp [Interface.totalInserts]
      simp only [events, eraseOperations_append, appendCount, head.inserts_eq_zero, ih, Nat.zero_add]

/-- Every increase in a source fold is precisely a restored good winner. -/
theorem increases_eq_good {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (chain : ArticleSourceMacroChain params state) :
    Interface.totalIncreases (eraseOperations chain.events) = chain.goodCount := by
  induction chain with
  | nil => rfl
  | cons head tail ih =>
      have appendCount : ∀ a b : List (Interface.Operation n),
          Interface.totalIncreases (a ++ b) = Interface.totalIncreases a + Interface.totalIncreases b := by
        intros; simp [Interface.totalIncreases]
      simp only [events, goodCount, eraseOperations_append, appendCount, head.increases_eq_good, ih]

/-- Telescope the geometric drops over the actual changing rich states. -/
theorem gap_drop {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (chain : ArticleSourceMacroChain params state) :
    geometricGapPotential chain.final + chain.goodCount ≤ geometricGapPotential state := by
  induction chain with
  | nil => simp [final, goodCount]
  | cons head tail ih =>
      have localDrop := head.gap_drop
      simp only [final, goodCount]
      omega

theorem blocks_length_eq {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (chain : ArticleSourceMacroChain params state) :
    chain.final.blocks.length = state.blocks.length := by
  induction chain with
  | nil => rfl
  | cons head tail ih => exact ih.trans head.blocks_length_eq

/-- No paid operation is hidden inside the complete internal-pairing fold. -/
theorem increases_le_initial_gap {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (chain : ArticleSourceMacroChain params state) :
    Interface.totalIncreases (eraseOperations chain.events) ≤ geometricGapPotential state := by
  rw [chain.increases_eq_good]
  exact (Nat.le_add_left _ _).trans chain.gap_drop

/-- The residence-ending footprint of the global fold is exactly the
flattened loser list of its checked source-local batches. -/
theorem leavingElements_eq {n : ℕ} {params : Interface.Parameters}
    {state : Lazy.State n}
    (chain : ArticleSourceMacroChain params state) :
    operationLeavingElementsList (Lazy.eraseOperations chain.events) =
      chain.batches.flatMap fun batch =>
        Interface.pairingLosers
          (batch.firstMatching ++ batch.secondMatching) := by
  induction chain with
  | nil state stable =>
      rfl
  | cons head tail ih =>
      simp only [events, batches, Lazy.eraseOperations_append,
        operationLeavingElementsList_append, List.flatMap_cons]
      rw [head.leavingElements_eq, ih]

/-- Pairwise-disjoint frozen source payloads make every leaving occurrence in
the composed internal article phase globally unique. -/
theorem leavingElements_nodup
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (chain : ArticleSourceMacroChain params state)
    (payloadsDisjoint :
      chain.batches.Pairwise
        (Function.onFun List.Disjoint
          ArticleSourceLoserBatch.sourceElements)) :
    (operationLeavingElementsList
      (Lazy.eraseOperations chain.events)).Nodup := by
  rw [chain.leavingElements_eq]
  exact ArticleSourceLoserBatch.globalLosers_nodup
    chain.batches payloadsDisjoint

end ArticleSourceMacroChain

end Splay.Accounting
