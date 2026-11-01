import MultiSplay.GlobalPreferredInventoryHistory
import MultiSplay.ClassicalSwitchAccountingEG

/-!
# Forest comparison bounds the actual online classical strategy

The exact persistent replay connects the original-key physical strategy to
the Splay forest comparison theorem. This intermediate result takes a paid
comparator program for the literal chronological word. Constructing a cheap
such program is a separate theorem, not a hypothesis about the algorithm.
-/

namespace MultiSplay.Global.Preferred.Online

open DynamicOptimality (RawTree BST)
open EndpointEncoding ClassicalSwitch CommonForest

/-- One uniform Splay comparison constant applies to the fixed online
strategy on every indexed reference. The only additional physical charge is
one per original request; all search depths and rotations are already paid
by the retained forest work. -/
theorem initial_run_comparator_bound_eg :
    ∃ constant : Nat, 0 < constant ∧
      ∀ {n : Nat} (reference : BST 0 n) (preference : EndpointEncoding.State)
        (requests : List (Fin n))
        {sources targets : List (RawTree Nat)} {budget : Nat},
        domains sources = domains (forest preference reference.toRaw) →
        Program sources
          (historyWord reference.toRaw preference
            (requests.map fun key => nodeAddress reference key.val)) targets budget →
        ((strategy reference).run (initial reference preference) requests).2 ≤
          constant * (n + budget) * Splay.Analysis.egTargetFactor reference.height +
            requests.length := by
  obtain ⟨constant,positive,bound⟩ := Accounting.finite_history_splay_bound_linear_eg
  refine ⟨2*constant,Nat.mul_pos (by omega) positive,?_⟩
  intro n reference preference requests sources targets budget same comparator
  obtain ⟨next,inventory,trace⟩ := initial_run_trace reference preference requests
  have paid := bound reference preference requests rfl same trace comparator
  calc
    ((strategy reference).run (initial reference preference) requests).2 ≤
        2 * runWork (initial reference preference) requests + requests.length := run_cost_le _ _
    _ ≤ 2 * (constant * (n+budget) * Splay.Analysis.egTargetFactor reference.height) +
        requests.length := Nat.add_le_add_right (Nat.mul_le_mul_left 2 paid) _
    _ = (2*constant) * (n+budget) * Splay.Analysis.egTargetFactor reference.height +
        requests.length := by ring

end MultiSplay.Global.Preferred.Online
