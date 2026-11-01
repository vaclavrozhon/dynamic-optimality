import Splay.Interface.BlockCount
import Splay.Lazy.CanonicalInitial
import Splay.Lazy.CanonicalState
import Splay.Lazy.CanonicalTrace
import Mathlib.Data.List.ProdSigma

namespace Splay.Lazy

namespace Trace

/-- Rich traces inherit the exact persistent block-count law after erasure. -/
theorem blocks_length_eq {n : ℕ} {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    (trace : Trace params initial events final) :
    final.blocks.length =
      initial.blocks.length +
        Interface.totalBlockGrowth (eraseOperations events) := by
  have projected := trace.toInterface.blocks_length_eq
  simpa [State.toInterface] using projected

end Trace

namespace Canonical

open Splay.Rank

@[simp]
theorem ownerSidePairs_length (n : ℕ) :
    (ownerSidePairs n).length = (2 * n + 1) * 2 := by
  simp [ownerSidePairs, List.product]

@[simp]
theorem canonicalBlocks_length {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (canonicalBlocks snapshot tree).length = (2 * n + 1) * 2 := by
  simp [canonicalBlocks]

@[simp]
theorem canonicalState_blocks_length {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (canonicalState snapshot tree).blocks.length =
      (2 * n + 1) * 2 := by
  simp [canonicalState]

/--
Any rich trace whose two endpoints are literal canonical states has zero
total block growth.  In particular, such an endpoint specification cannot
describe a macro that uses `create` or `split`, because the interface
deliberately preserves every historical block identity.
-/
theorem canonical_to_canonical_totalBlockGrowth_eq_zero
    {n : ℕ} {params : Interface.Parameters}
    {beforeSnapshot afterSnapshot : Snapshot n}
    {beforeTree afterTree : Tree.BST 0 n}
    {events : List (Event n)}
    (trace :
      Trace params
        (canonicalState beforeSnapshot beforeTree) events
        (canonicalState afterSnapshot afterTree)) :
    Interface.totalBlockGrowth (eraseOperations events) = 0 := by
  have hCount := trace.blocks_length_eq
  simp only [canonicalState_blocks_length] at hCount
  omega

/--
Conversely, every initialization trace from the empty-block state to the
literal canonical state must create exactly the canonical number of persistent
block identities.
-/
theorem empty_to_canonical_totalBlockGrowth
    {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n} {tree : Tree.BST 0 n}
    {events : List (Event n)}
    (trace :
      Trace params
        (emptyCanonicalState snapshot tree) events
        (canonicalState snapshot tree)) :
    Interface.totalBlockGrowth (eraseOperations events) =
      (2 * n + 1) * 2 := by
  have hCount := trace.blocks_length_eq
  simp only [emptyCanonicalState_blocks, List.length_nil,
    canonicalState_blocks_length, Nat.zero_add] at hCount
  exact hCount.symm

end Canonical

end Splay.Lazy
