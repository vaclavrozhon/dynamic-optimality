import TangoSquaredAbstract
import DynamicOptimality.OnlineBSTProjection
import DynamicOptimality.UniverseExtension
import DynamicOptimality.PaddingSize
import DynamicOptimality.PaddingFactor

/-!
# Tango² on every finite universe in the abstract BST model

The internal Tango² state uses a power-of-two universe containing the
original keys. Its actual tree is obtained by pruning every larger key.
The checked projection transforms each source access into actual searches
and rotations on exactly the original keys, without increasing the cost.

Thus the extra keys occur only in free mathematical bookkeeping. Starting
from any supplied indexed BST, the physical initial tree is that exact
tree. The strategy is fixed per state and request, including its choices
of projected transitions; all request prefixes remain consistent.
-/

namespace DynamicOptimality.Tango2.All

/-- The power-of-two construction's factor at the chosen universe height. -/
def factor (n : Nat) : Nat := Tango2.factor (Padding.height n)

/-- An online strategy whose actual tree contains exactly `0,...,n-1`. -/
noncomputable def strategy (n : Nat) : OnlineBST n :=
  OnlineBST.Projection.strategy (Tango2.strategy (Padding.height n)) (Padding.le_capacity n)

noncomputable def initial {n : Nat} (tree : BST 0 n) : (strategy n).State :=
  Tango2.initial (UniverseExtension.extend tree (Padding.le_capacity n))

theorem initial_tree {n : Nat} (tree : BST 0 n) :
    (strategy n).tree (initial tree) = tree.toRaw :=
  UniverseExtension.prune_extend tree (Padding.le_capacity n)

noncomputable def cost {n : Nat} (tree : BST 0 n) (requests : List (Fin n)) : Nat :=
  ((strategy n).run (initial tree) requests).2

/-- This cost is paid by an actual execution on only the original keys. -/
theorem execution {n : Nat} (tree : BST 0 n) (requests : List (Fin n)) :
    SearchRotation.Execution tree.toRaw (requests.map Fin.val)
      ((strategy n).tree ((strategy n).run (initial tree) requests).1) (cost tree requests) := by
  simpa only [initial_tree, cost] using (strategy n).run_execution (initial tree) requests

/-- No change is performed before the first request. -/
theorem empty_word {n : Nat} (tree : BST 0 n) :
    (strategy n).tree ((strategy n).run (initial tree) []).1 = tree.toRaw ∧ cost tree [] = 0 :=
  ⟨initial_tree tree, rfl⟩

theorem zero_universe (tree : BST 0 0) (requests : List (Fin 0)) : cost tree requests = 0 := by
  cases requests with
  | nil => rfl
  | cons request requests => exact Fin.elim0 request

/-- Exact state and cost consistency under every extension of a prefix. -/
theorem online {n : Nat} (state : (strategy n).State) (first last : List (Fin n)) :
    (strategy n).run state (first ++ last) =
      let front := (strategy n).run state first
      let back := (strategy n).run front.1 last
      (back.1, front.2 + back.2) :=
  (strategy n).run_append state first last

theorem cost_bound_positive {n : Nat} (positive : 0 < n)
    (tree : BST 0 n) (requests : List (Fin n)) :
    cost tree requests ≤ 809280000114 * (OPT requests + n) * factor n := by
  have projected := OnlineBST.Projection.run_cost_le
    (Tango2.strategy (Padding.height n)) (Padding.le_capacity n)
    (Tango2.initial (UniverseExtension.extend tree (Padding.le_capacity n))) requests
  have sourceBound := Tango2.cost_bound (h := Padding.height n)
    (UniverseExtension.extend tree (Padding.le_capacity n))
    (requests.map (Fin.castLE (Padding.le_capacity n)))
  have optimum := UniverseExtension.OPT_castLE_le requests (Padding.le_capacity n)
  have capacity := Padding.capacity_le_four_mul positive
  change cost tree requests ≤
    Tango2.cost (UniverseExtension.extend tree (Padding.le_capacity n))
      (requests.map (Fin.castLE (Padding.le_capacity n))) at projected
  change _ ≤ 134880000019 *
    (OPT (requests.map (Fin.castLE (Padding.le_capacity n))) + Padding.capacity n) * factor n at sourceBound
  calc
    cost tree requests ≤ _ := projected
    _ ≤ 134880000019 *
        (OPT (requests.map (Fin.castLE (Padding.le_capacity n))) + Padding.capacity n) * factor n := sourceBound
    _ ≤ 134880000019 * (6 * (OPT requests + n)) * factor n :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    _ = _ := by ring

/-- The same constant works for every universe, initial tree, and word. -/
theorem cost_bound {n : Nat} (tree : BST 0 n) (requests : List (Fin n)) :
    cost tree requests ≤ 809280000114 * (OPT requests + n) * factor n := by
  cases n with
  | zero => rw [zero_universe]; exact Nat.zero_le _
  | succ n => exact cost_bound_positive (Nat.succ_pos n) tree requests

/-- The final theorem uses the shared algorithm-cost and OPT interfaces. -/
theorem competitive : Competitive cost factor :=
  ⟨809280000114, by decide, fun _ _ tree requests => cost_bound tree requests⟩

/-- The explicit padding factor is bounded by the shared stabilized third
logarithm, including the small and empty universes. -/
theorem factor_le_third_log (n : Nat) : factor n ≤ 4 * Splay.Analysis.iteratedLog 3 n :=
  Padding.factor_le_four_iteratedLog n

theorem third_log_cost_bound {n : Nat} (tree : BST 0 n) (requests : List (Fin n)) :
    cost tree requests ≤ 3237120000456 * (OPT requests + n) * Splay.Analysis.iteratedLog 3 n := by
  calc
    cost tree requests ≤ 809280000114 * (OPT requests + n) * factor n := cost_bound tree requests
    _ ≤ 809280000114 * (OPT requests + n) * (4 * Splay.Analysis.iteratedLog 3 n) :=
      Nat.mul_le_mul_left _ (factor_le_third_log n)
    _ = _ := by ring

/-- Unrestricted shared competitiveness: every nonempty universe, every
initial BST, every request word, and the stabilized third-log factor. -/
theorem third_log_competitive : Competitive cost (Splay.Analysis.iteratedLog 3) :=
  ⟨3237120000456, by decide, fun _ _ tree requests => third_log_cost_bound tree requests⟩

/-- Every competing execution uses exactly the same physical keys and
search-depth-plus-rotations cost model as this online strategy. -/
theorem competitor_bound {n : Nat} (tree competitor : BST 0 n)
    (requests : List (Fin n)) {final : RawTree Nat} {paid : Nat}
    (other : SearchRotation.Execution competitor.toRaw (requests.map Fin.val) final paid) :
    cost tree requests ≤ 1618560000228 * (paid + n) * factor n := by
  have optimum := SearchRotation.OPT_le_cost competitor requests other
  calc
    cost tree requests ≤ 809280000114 * (OPT requests + n) * factor n := cost_bound tree requests
    _ ≤ 809280000114 * (2 * (paid + n)) * factor n :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    _ = _ := by ring

end DynamicOptimality.Tango2.All
