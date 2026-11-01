import Splay.Lazy.RootSwapCheckpoint
import Splay.Lazy.SingletonInsertionOrigins

namespace Splay.Lazy.State

/-- A complete root swap after bounded interval preparation. -/
structure RootSwapExecution {n : ℕ} (params : Interface.Parameters) (initial : State n) (target : HeapView n) where
  final : State n
  events : List (Event n)
  trace : Trace params initial events final
  stable : final.Stable params
  view_eq : final.view = target
  births : final.blocks.length ≤ initial.blocks.length + 1
  inserts : Interface.totalInserts (eraseOperations events) = 1
  increases : Interface.totalIncreases (eraseOperations events) ≤ 3 * params.valueBound
  largeOrigin : ∀ block ∈ final.blocks, 1 < block.elements.length →
    ∃ old ∈ initial.blocks, block.elements = old.elements ∧ block.passCount = old.passCount

theorem RootSwapCheckpoint.finish {n : ℕ} {params : Interface.Parameters} {initial : State n} {target : HeapView n}
    (checkpoint : RootSwapCheckpoint params initial target) (ordered : target.HeapOrdered)
    (rootsNe : target.root ≠ initial.view.root) : Nonempty (RootSwapExecution params initial target) := by
  let element := initial.view.root
  have parented : target.parent element ≠ none := target.parent_ne_none_of_ne_root rootsNe.symm
  cases parentEq : target.parent element with
  | none => exact (parented parentEq).elim
  | some owner =>
      let side := target.side element
      obtain ⟨index, property, _unique⟩ := checkpoint.oneGrowing owner side
      let block := checkpoint.state.blocks.get index
      have found : checkpoint.state.blocks[index.val]? = some block := List.getElem?_eq_some_iff.mpr ⟨index.isLt, rfl⟩
      have growing : block.mode = .growing := property.1
      have blockOwner : block.owner = owner := property.2.1
      have blockSide : block.side = side := property.2.2
      have ownerEq : block.owner = (target.parent initial.view.root).getD target.root := by rw [parentEq]; exact blockOwner
      have empty := checkpoint.empty block (List.get_mem _ _) growing ownerEq
      have traceStable := insertSingleton_stable_of_completeExcept checkpoint.valid
        (by rw [checkpoint.view_eq]; exact ordered) checkpoint.oneGrowing checkpoint.topmost checkpoint.values
        element checkpoint.completeExcept checkpoint.oldRootValue found growing empty
        (by rw [checkpoint.view_eq, blockOwner]; exact parentEq)
        (by rw [checkpoint.view_eq, blockSide])
        (by intro current member; rw [checkpoint.view_eq]; exact checkpoint.fullSegments current member)
      refine ⟨{
        final := checkpoint.state.insertSingleton index.val block element
        events := checkpoint.events ++ checkpoint.state.insertSingletonEvents index.val block element
        trace := checkpoint.trace.append traceStable.1
        stable := traceStable.2
        view_eq := (checkpoint.state.insertSingleton_view index.val block element).trans checkpoint.view_eq
        births := ?_
        inserts := ?_
        increases := ?_
        largeOrigin := by
          intro current member large
          exact checkpoint.largeOrigin current
            (checkpoint.state.insertSingleton_large_preserved index.val block element found empty member large) large
      }⟩
      · rw [insertSingleton_blocks_length, checkpoint.births]
      · rw [eraseOperations_append, Interface.totalInserts_append, checkpoint.noInserts, insertSingletonEvents_inserts]
      · rw [eraseOperations_append, Interface.totalIncreases_append, checkpoint.noIncreases, Nat.zero_add]
        exact checkpoint.state.insertSingletonEvents_increases index.val block element checkpoint.valid

end Splay.Lazy.State
