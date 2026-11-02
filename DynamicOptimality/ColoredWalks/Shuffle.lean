import DynamicOptimality.ColoredWalks.ShuffleReduction
import DynamicOptimality.MultiFinger.Simulation

/-! # Shuffles of nearest-neighbor walks in an ordinary BST

Each source walks on a fixed ordered subset of the original keys, staying
put or moving to a neighboring key of that subset. The source subsets may
overlap and the interleaving is arbitrary. No source occurrence is lost.
The actual multifinger construction discharges the reduction's simulator
premise. The shared optimum bound has no additive universe-size term.
-/

namespace DynamicOptimality.ColoredWalks

open ChaCha.MTR

/-- The factor is `(1+floor(log₂(k+1)))²`, including unused colors and
empty words. The constant is uniform in the subsets and their shuffle. -/
theorem shuffle_OPT_bound {n k : Nat} (sets : Fin k → Finset (Fin n))
    (events : List (Fin k × Fin n)) (walk : ShuffleWalk sets events) :
    OPT (events.map Prod.snd) ≤
      292864*events.length*(MultiFinger.logarithmicFactor k)^2 := by
  simpa only [show 286*1024 = 292864 by norm_num] using
    shuffle_OPT_of_simulation MultiFinger.simulationBound sets walk

/-- Actual execution from any supplied original-key BST, with one linear
initialization allowance in the shared search-plus-rotations model. -/
theorem shuffle_from_initial {n k : Nat} (sets : Fin k → Finset (Fin n))
    (events : List (Fin k × Fin n)) (walk : ShuffleWalk sets events) (initial : BST 0 n) :
    ∃ (final : BST 0 n) (cost : Nat),
      SearchRotation.Execution initial.toRaw ((events.map Prod.snd).map Fin.val) final.toRaw cost ∧
      cost ≤ 585728*events.length*(MultiFinger.logarithmicFactor k)^2+12*n := by
  simpa only [show 572*1024 = 585728 by norm_num] using
    shuffle_from_initial_of_simulation MultiFinger.simulationBound sets walk initial

end DynamicOptimality.ColoredWalks
