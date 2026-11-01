import Splay.Statement
import Mathlib.Tactic

namespace Splay

/--
A deliberately unconstrained cost model witnessing that `TargetBound` cannot
be proved for every inhabitant of the abstract `CostModel` structure.

Its alleged splay cost is the request count, while its alleged optimum is
zero.  This is not intended as a BST model; it records the exact logical
boundary imposed by keeping both costs abstract in `Statement.lean`.
-/
def unboundedAbstractModel : CostModel where
  Initial := fun _ => Unit
  splayCost := fun _ accesses => accesses.length
  optCost := fun _ => 0

/--
There is no theorem `∀ model : CostModel, TargetBound model`: the structure
contains no laws relating its two arbitrary cost functions.
-/
theorem unboundedAbstractModel_not_targetBound :
    ¬ TargetBound unboundedAbstractModel := by
  rintro ⟨constant, _, bound⟩
  let request : Fin 1 := ⟨0, by omega⟩
  let accesses : List (Fin 1) :=
    List.replicate
      (constant * Analysis.targetFactor 1 + 1) request
  have impossible :=
    bound 1 (by omega) () accesses
  simp only [unboundedAbstractModel, accesses, List.length_replicate,
    zero_add, mul_one] at impossible
  omega

theorem not_every_costModel_satisfies_targetBound :
    ¬ ∀ model : CostModel, TargetBound model := by
  intro universal
  exact unboundedAbstractModel_not_targetBound
    (universal unboundedAbstractModel)

end Splay
