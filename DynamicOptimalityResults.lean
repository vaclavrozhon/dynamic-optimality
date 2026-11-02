import DynamicOptimality.SplayBound
import DynamicOptimality.SplayBlackBoxBound
import DynamicOptimality.SearchRotationEquivalence
import DynamicOptimality.OnlineBST
import Greedy.Competitive
import ChaChaAll
import DynamicOptimality.MultiSplayBound
import MultiSplay.CompetitiveLogHeight
import DynamicOptimality.BSTModels

/-!
# Results in the common BST/OPT framework

This is the short public entry point, separate from historical implementation
experiments. Every comparison uses `DynamicOptimality.OPT` and the existing
key-tree types. Algorithm-specific cost conventions remain explicit:

* splay: requests plus the rotations of standard splay;
* Greedy: geometric touches from the initial tree's depth surface;
* Cha-Cha: a fixed online search-and-rotation strategy, from every initial
  tree on every finite key universe, with the shared-OPT competitive bound;
* classical MultiSplay: a fixed online search-and-rotation strategy, with
  factor `L₃(n) * egTargetFactor (ceil(log₂(n+1)))` from every initial tree.

See `FORMALIZATION.md` for exact interfaces and scope, and
`multisplay/COMPOSED_BOUND.txt` for the composed MultiSplay argument.
-/

namespace DynamicOptimality.Results

theorem splay :
    Competitive Splay.Accounting.concreteSplayCost Splay.Analysis.targetFactor :=
  splay_competitive

theorem greedy : Competitive Greedy.cost Greedy.loglogFactor :=
  Greedy.competitive

theorem chacha : Competitive ChaCha.All.cost (Splay.Analysis.iteratedLog 3) :=
  ChaCha.All.third_log_competitive

theorem multisplay : Competitive MultiSplay.Online.cost
    (MultiSplay.logarithmicFactor Splay.Analysis.egTargetFactor) :=
  MultiSplay.Online.competitive_logarithmic

/-- Finite execution costs in all five models agree up to a universal factor.
The geometric-to-tree reconstruction in this theorem is offline. -/
theorem bst_models_equivalent (source target : BSTModel) {n cost : Nat}
    {requests : List (Fin n)} (run : source.costs requests cost) :
    ∃ targetCost, target.costs requests targetCost ∧ targetCost ≤ 481 * cost :=
  source.all_five_equivalent target run

end DynamicOptimality.Results
