import DynamicOptimality.SplayBound
import DynamicOptimality.SplayBlackBoxBound
import DynamicOptimality.SearchRotationEquivalence
import DynamicOptimality.OnlineBST
import Greedy.Competitive
import ChaChaAll
import DynamicOptimality.MultiSplayBound
import DynamicOptimality.BSTModels
import DynamicOptimality.ReferenceClosure
import Splay.Accounting.LogHeightNormalForm
import ChaCha.Paper20261030.SplayAuxiliaryAll
import ChaCha.Separation.Explicit
import DynamicOptimality.Funnel.ConvexComposition
import DynamicOptimality.Funnel.ShuffleOPT
import MultiSplay.Obstructions.IntervalProjection
import MultiSplay.Obstructions.ClassicalPotentialObstruction
import ChaCha.Entropy.ExpectationEntropy
import DynamicOptimality.ColoredWalks.ProjectionExecution
import DynamicOptimality.ColoredWalks.Embedding
import DynamicOptimality.ColoredWalks.Shuffle
import DynamicOptimality.GeometricOnlineSimulation.GreedyInstance

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

/-- The refined Splay factor, also used in the MultiSplay composition. -/
theorem splay_refined :
    Competitive Splay.Accounting.concreteSplayCost Splay.Analysis.egTargetFactor :=
  splay_eg_competitive

theorem greedy : Competitive Greedy.cost Greedy.loglogFactor :=
  Greedy.competitive

theorem chacha : Competitive ChaCha.All.cost (Splay.Analysis.iteratedLog 3) :=
  ChaCha.All.third_log_competitive

/-- The same third-logarithm factor with actual ordinary Splay auxiliaries. -/
theorem chacha_splay : Competitive _root_.ChaCha.Paper20261030.SplayAuxiliary.All.cost
    (Splay.Analysis.iteratedLog 3) :=
  _root_.ChaCha.Paper20261030.SplayAuxiliary.All.third_log_competitive

theorem multisplay : Competitive MultiSplay.Online.cost
    (MultiSplay.logarithmicFactor Splay.Analysis.egTargetFactor) :=
  multisplay_logarithmic_competitive

/-- Arbitrary occurrence interleavings, including overlapping alphabets. -/
theorem funnel_shuffle {n : Nat} {X Y W : List (Fin n)} (shuffle : Funnel.Shuffle X Y W) :
    Funnel.wordCount W + W.length ≤ 360639 * (OPT X + OPT Y) :=
  shuffle.OPT_bound

/-- Arbitrary interleavings of walks on fixed ordered subsets. -/
theorem colored_shuffle {n k : Nat} (sets : Fin k → Finset (Fin n))
    (events : List (Fin k × Fin n)) (walk : ColoredWalks.ShuffleWalk sets events) :
    OPT (events.map Prod.snd) ≤
      292864*events.length*(MultiFinger.logarithmicFactor k)^2 :=
  ColoredWalks.shuffle_OPT_bound sets events walk

/-- One online physical strategy simulates all future geometric prefixes. -/
theorem geometric_online {n : Nat} (source : Geometry.OnlineStrategy n)
    (initial : source.State) (baseline : source.height initial = fun _ => 0) :
    ∃ target : OnlineBST n, ∃ start : BST 0 n → target.State,
      (∀ before, target.tree (start before) = before.toRaw) ∧
      ∀ before requests, (target.run (start before) requests).2 ≤
        387*n+381*(source.run initial requests).2 :=
  source.exists_onlineBST initial baseline

/-- Finite execution costs in all five models agree up to a universal factor.
The geometric-to-tree reconstruction in this theorem is offline. -/
theorem bst_models_equivalent (source target : BSTModel) {n cost : Nat}
    {requests : List (Fin n)} (run : source.costs requests cost) :
    ∃ targetCost, target.costs requests targetCost ∧ targetCost ≤ 481 * cost :=
  source.all_five_equivalent target run

end DynamicOptimality.Results
