import GeometricGreedy
import SurfaceUpdate
import DynamicOptimality.Cost

/-!
# The actual geometric Greedy algorithm

A surface assigns each key its last touch time. `costFrom` executes the
inclusion-least row proved correct in `GeometricGreedy`, then raises exactly
that row to the next time. `cost` starts from the negative depths of the
prescribed initial BST. Costs count all touched keys, including requests.
-/

namespace Greedy

open GreedyMerge.Geometry GreedyMerge.Surface

abbrev Surface := ℕ → ℤ

noncomputable def costFrom {n : ℕ} (height : Surface) (time : ℤ) : List (Fin n) → ℕ
  | [] => 0
  | request :: rest =>
      (GreedyRow height n request.val).card +
        costFrom (RaiseSurface height n request.val time) (time + 1) rest

noncomputable def linksFrom {n : ℕ} (height : Surface) (time : ℤ) : List (Fin n) → ℕ
  | [] => 0
  | request :: rest =>
      2 * ((GreedyRow height n request.val).card - 1) +
        linksFrom (RaiseSurface height n request.val time) (time + 1) rest

def initialSurface {n : ℕ} (initial : DynamicOptimality.BST 0 n) : Surface :=
  fun key => -(initial.depth key : ℤ)

noncomputable def cost : DynamicOptimality.AlgorithmCost :=
  fun initial requests => costFrom (initialSurface initial) 1 requests

theorem initialSurface_lt_one {n : ℕ} (initial : DynamicOptimality.BST 0 n) (key : ℕ) :
    initialSurface initial key < 1 := by
  unfold initialSurface
  omega

theorem row_card_pos {n : ℕ} (height : Surface) (request : Fin n) :
    0 < (GreedyRow height n request.val).card :=
  Finset.card_pos.mpr ⟨request.val, access_mem_greedyRow height request.isLt⟩

theorem length_le_costFrom {n : ℕ} (height : Surface) (time : ℤ)
    (requests : List (Fin n)) : requests.length ≤ costFrom height time requests := by
  induction requests generalizing height time with
  | nil => simp [costFrom]
  | cons request rest ih =>
      have positive := row_card_pos height request
      have tailBound := ih (RaiseSurface height n request.val time) (time + 1)
      simp only [List.length_cons, costFrom]
      omega

/-- Exact touch/link identity, with no division or parity convention. -/
theorem twice_costFrom {n : ℕ} (height : Surface) (time : ℤ)
    (requests : List (Fin n)) :
    2 * costFrom height time requests = 2 * requests.length + linksFrom height time requests := by
  induction requests generalizing height time with
  | nil => simp [costFrom, linksFrom]
  | cons request rest ih =>
      have positive := row_card_pos height request
      have tailEq := ih (RaiseSurface height n request.val time) (time + 1)
      simp only [List.length_cons, costFrom, linksFrom]
      omega

theorem cost_empty {n : ℕ} (initial : DynamicOptimality.BST 0 n) : cost initial [] = 0 := rfl

theorem length_le_cost {n : ℕ} (initial : DynamicOptimality.BST 0 n)
    (requests : List (Fin n)) : requests.length ≤ cost initial requests :=
  length_le_costFrom _ _ _

end Greedy
