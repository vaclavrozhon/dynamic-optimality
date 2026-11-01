import DynamicOptimality.SplayBound
import DynamicOptimality.SplayBlackBoxBound
import DynamicOptimality.SearchRotationEquivalence
import DynamicOptimality.OnlineBST
import Greedy.Competitive
import TangoSquaredAll
import MultiSplay.CommonForestSplayBound
import MultiSplay.EndpointCounterBound

/-!
# Results in the common BST/OPT framework

This is the short public entry point, separate from historical implementation
experiments. Every comparison uses `DynamicOptimality.OPT` and the existing
key-tree types. Algorithm-specific cost conventions remain explicit:

* splay: requests plus the rotations of standard splay;
* Greedy: geometric touches from the initial tree's depth surface;
* Tango²: a fixed online search-and-rotation strategy, from every initial
  tree on every finite key universe, with the shared-OPT competitive bound;
* MultiSplay: the common-forest comparison and actual endpoint counters.

The MultiSplay imports must not be read as a full MultiSplay competitiveness
theorem. See `docs/tango2-proof-guide/guide.pdf` for the proof and scope map,
and its adjacent verification note for the completed Tango² endpoint.
-/

namespace DynamicOptimality.Results

theorem splay :
    Competitive Splay.Accounting.concreteSplayCost Splay.Analysis.targetFactor :=
  splay_competitive

theorem greedy : Competitive Greedy.cost Greedy.loglogFactor :=
  Greedy.competitive

theorem tango2 : Competitive Tango2.All.cost (Splay.Analysis.iteratedLog 3) :=
  Tango2.All.third_log_competitive

end DynamicOptimality.Results
