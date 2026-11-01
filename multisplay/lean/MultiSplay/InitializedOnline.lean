import MultiSplay.GlobalPreferredOnline
import MultiSplay.CompetitiveFactor
import DynamicOptimality.OnlineBSTInitialization

/-!
# Classical MultiSplay from every supplied initial BST

The reference uses exactly the original keys. After the single charged
initialization, the fixed online transition executes the actual bottom-up
classical switches, including the mandatory final switch. Computation and
mathematical bookkeeping are free; searches and ordinary rotations are
certified through the common `OnlineBST` interface.
-/

namespace MultiSplay.Online

open DynamicOptimality

variable {n : Nat}

noncomputable def canonicalStrategy (n : Nat) : OnlineBST n :=
  Global.Preferred.Online.strategy (balancedReference n)

noncomputable def canonicalState (n : Nat) : (canonicalStrategy n).State :=
  Global.Preferred.Online.initial (balancedReference n) (fun _ => true)

noncomputable def strategy (n : Nat) : OnlineBST n :=
  OnlineBST.Initialization.strategy (canonicalStrategy n) (canonicalState n)

def initial (before : BST 0 n) : (strategy n).State := .inl before

noncomputable def cost (before : BST 0 n) (requests : List (Fin n)) : Nat :=
  ((strategy n).run (initial before) requests).2

theorem initial_tree (before : BST 0 n) :
    (strategy n).tree (initial before) = before.toRaw := rfl

theorem execution (before : BST 0 n) (requests : List (Fin n)) :
    SearchRotation.Execution before.toRaw (requests.map Fin.val)
      ((strategy n).tree ((strategy n).run (initial before) requests).1)
      (cost before requests) :=
  (strategy n).run_execution (initial before) requests

theorem exact_keys (state : (strategy n).State) :
    ((strategy n).tree state).inorder = List.range n := (strategy n).tree_word state

theorem online (state : (strategy n).State) (first rest : List (Fin n)) :
    (strategy n).run state (first++rest) =
      let front := (strategy n).run state first
      let back := (strategy n).run front.1 rest
      (back.1,front.2+back.2) := (strategy n).run_append state first rest

theorem empty_word (before : BST 0 n) : cost before [] = 0 := rfl

theorem zero_universe (before : BST 0 0) (requests : List (Fin 0)) :
    cost before requests = 0 := by
  cases requests with
  | nil => rfl
  | cons request rest => exact Fin.elim0 request

/-- The initialized strategy pays at most one linear allowance in addition
to the exact same fixed canonical online choices. -/
theorem cost_le_canonical (before : BST 0 n) (requests : List (Fin n)) :
    cost before requests ≤
      19*n+((canonicalStrategy n).run (canonicalState n) requests).2 :=
  OnlineBST.Initialization.run_cost_le (canonicalStrategy n) (canonicalState n) before requests

/-- The physical cost reduces to the retained classical forest work;
the remaining competitive theorem must bound this very run's work. -/
theorem cost_le_classical (before : BST 0 n) (requests : List (Fin n)) :
    cost before requests ≤ 19*n+
      2*Global.Preferred.Online.runWork (canonicalState n) requests+requests.length := by
  have initialized := cost_le_canonical before requests
  have classical := Global.Preferred.Online.run_cost_le (canonicalState n) requests
  change ((canonicalStrategy n).run (canonicalState n) requests).2 ≤
    2*Global.Preferred.Online.runWork (canonicalState n) requests+requests.length at classical
  omega

end MultiSplay.Online
