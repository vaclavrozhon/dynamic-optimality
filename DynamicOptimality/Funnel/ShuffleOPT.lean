import DynamicOptimality.Funnel.ShuffleOPTCore
import DynamicOptimality.Funnel.ShuffleInterleave
import DynamicOptimality.Funnel.ApproxMonotonicity.Run

/-! # Arbitrary two-source funnel shuffles are bounded by the shared BST optimum

Each source is expanded along an actual cheap MTR execution. The two expanded
words admit an interleaving containing the original output. The proved
geometric subsequence bound then combines with the occurrence-color charging
argument. Every source uses the same attained `DynamicOptimality.OPT` as the
other developments in this repository, with no universe-size startup term.
-/

namespace DynamicOptimality.Funnel

/-- Arbitrary order-preserving occurrence interleavings; the source alphabets
may overlap, and all three words may repeat keys. -/
theorem interleave_OPT_bound {n : Nat} {X Y W : List (Fin n)} (interleave : Interleave X Y W) :
    wordCount W + W.length ≤ 360639 * (DynamicOptimality.OPT X + DynamicOptimality.OPT Y) :=
  interleave_OPT_bound_of_subsequence_bound
    (fun _ _ sublist => wordCount_sublist sublist) interleave

/-- The same endpoint for the explicit occurrence-embedding shuffle interface. -/
theorem Shuffle.OPT_bound {n : Nat} {X Y W : List (Fin n)} (shuffle : Shuffle X Y W) :
    wordCount W + W.length ≤ 360639 * (DynamicOptimality.OPT X + DynamicOptimality.OPT Y) :=
  interleave_OPT_bound shuffle.interleave

/-- In particular, the same geometric count is a lower bound for the shared
BST optimum, with a deliberately loose uniform normalization constant. -/
theorem wordCount_add_length_le_OPT {n : Nat} (word : List (Fin n)) :
    wordCount word + word.length ≤ 360639 * DynamicOptimality.OPT word := by
  have shuffle : Interleave word [] word := by simpa using Interleave.append word []
  have bound := interleave_OPT_bound shuffle
  simpa only [DynamicOptimality.OPT,Splay.Accounting.OfflineOptimum.offlineOptCost_nil,
    Nat.add_zero] using bound

end DynamicOptimality.Funnel
