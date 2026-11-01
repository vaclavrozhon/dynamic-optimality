import TangoSquared.Reference
import Mathlib.Algebra.Order.Ring.Nat

/-!
# Number of genuine internal fragment memories

For a secondary interval starting at depth `a`, there are `2^a` possible
primary owners in a perfect primary reference. Only internal secondary
intervals carry a memory bit. `memoryCount` sums these actual multiplicities.
The completion root is a separate bit and is not included here.
-/

namespace TangoSquared.Paper20261030.Secondary

def memoryCount : {a b : Nat} → DepthTree a b → Nat
  | _, _, .leaf _ => 0
  | a, _, .node _ _ _ l r => 2 ^ a + memoryCount l + memoryCount r

theorem memoryCount_bound {a b : Nat} (t : DepthTree a b) :
    memoryCount t + 2 ^ a ≤ 2 ^ b := by
  induction t with
  | leaf a => simp [memoryCount]
  | @node a b c ha hb l r ihl ihr =>
    have hpow : 2 ^ a ≤ (2 : Nat) ^ c := Nat.pow_le_pow_right (by decide) ha
    rw [pow_succ] at ihr
    simp only [memoryCount]
    omega

/-- For primary height `h+1`, this is at most half the leaf count minus one. -/
theorem root_memoryCount_bound {h : Nat} (t : DepthTree 0 h) :
    memoryCount t + 1 ≤ 2 ^ h := by
  simpa only [pow_zero] using memoryCount_bound t

end TangoSquared.Paper20261030.Secondary
