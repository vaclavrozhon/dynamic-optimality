import ChaCha.Paper20261030.SplayAuxiliaryNatural
import DynamicOptimality.OnlineBSTProjection
import DynamicOptimality.OnlineBSTInitialization
import DynamicOptimality.UniverseExtension
import DynamicOptimality.PaddingSize
import DynamicOptimality.PaddingFactor

/-!
# Ordinary-splay Cha-Cha on every finite key universe

Each auxiliary is an actual ordinary bottom-up splay tree. The checked
secondary and primary request certificates persist in the maintained
state. Shared online projection removes padding keys from the actual BST;
shared initialization starts at any supplied BST and is paid only once.
The final cost is the initial search depth plus one plus actual rotations,
with arbitrary mathematical bookkeeping allowed as in the other results.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary.All

open DynamicOptimality

 def factor (n : Nat) : Nat := OnlineSearchRotation.factor (Padding.height n)

noncomputable def projected (n : Nat) : OnlineBST n :=
  OnlineBST.Projection.strategy (Natural.strategy (Padding.height n)) (Padding.le_capacity n)

noncomputable def canonical (n : Nat) : (projected n).State := Natural.initial (Padding.height n)

noncomputable def strategy (n : Nat) : OnlineBST n :=
  OnlineBST.Initialization.strategy (projected n) (canonical n)

def initial {n : Nat} (tree : BST 0 n) : (strategy n).State := .inl tree

 theorem initial_tree {n : Nat} (tree : BST 0 n) : (strategy n).tree (initial tree) = tree.toRaw := rfl

noncomputable def cost {n : Nat} (tree : BST 0 n) (requests : List (Fin n)) : Nat :=
  ((strategy n).run (initial tree) requests).2

 theorem execution {n : Nat} (tree : BST 0 n) (requests : List (Fin n)) :
    SearchRotation.Execution tree.toRaw (requests.map Fin.val)
      ((strategy n).tree ((strategy n).run (initial tree) requests).1) (cost tree requests) :=
  (strategy n).run_execution (initial tree) requests

 theorem empty_word {n : Nat} (tree : BST 0 n) :
    (strategy n).tree ((strategy n).run (initial tree) []).1 = tree.toRaw ∧ cost tree [] = 0 := ⟨rfl,rfl⟩

 theorem zero_universe (tree : BST 0 0) (requests : List (Fin 0)) : cost tree requests = 0 := by
  cases requests with
  | nil => rfl
  | cons request requests => exact Fin.elim0 request

 theorem online {n : Nat} (state : (strategy n).State) (first last : List (Fin n)) :
    (strategy n).run state (first++last) =
      let front := (strategy n).run state first
      let back := (strategy n).run front.1 last
      (back.1,front.2+back.2) := (strategy n).run_append state first last

 theorem projected_bound {n : Nat} (positive : 0 < n) (requests : List (Fin n)) :
    ((projected n).run (canonical n) requests).2 ≤
      360012000*(OPT requests+n)*factor n := by
  have projection := OnlineBST.Projection.run_cost_le (Natural.strategy (Padding.height n))
    (Padding.le_capacity n) (Natural.initial (Padding.height n)) requests
  have sourceBound := Natural.canonical_bound (Padding.height n) (requests.map (Fin.castLE (Padding.le_capacity n)))
  have optimum := UniverseExtension.OPT_castLE_le requests (Padding.le_capacity n)
  have capacity := Padding.capacity_le_four_mul positive
  change _ ≤ 60002000*(OPT (requests.map (Fin.castLE (Padding.le_capacity n)))+Padding.capacity n)*factor n at sourceBound
  calc
    _ ≤ _ := projection
    _ ≤ 60002000*(OPT (requests.map (Fin.castLE (Padding.le_capacity n)))+Padding.capacity n)*factor n := sourceBound
    _ ≤ 60002000*(6*(OPT requests+n))*factor n :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    _ = _ := by ring

 theorem cost_bound_positive {n : Nat} (positive : 0 < n) (tree : BST 0 n) (requests : List (Fin n)) :
    cost tree requests ≤ 360012019*(OPT requests+n)*factor n := by
  have initialization := OnlineBST.Initialization.run_cost_le (projected n) (canonical n) tree requests
  have canonicalBound := projected_bound positive requests
  have factorPositive : 1 ≤ factor n := by unfold factor OnlineSearchRotation.factor; omega
  have reserve : 19*n ≤ 19*(OPT requests+n)*factor n := by
    calc
      19*n ≤ 19*(OPT requests+n) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 19*(OPT requests+n)*factor n := by nlinarith
  change cost tree requests ≤ _ at initialization
  nlinarith

 theorem cost_bound {n : Nat} (tree : BST 0 n) (requests : List (Fin n)) :
    cost tree requests ≤ 360012019*(OPT requests+n)*factor n := by
  cases n with
  | zero => rw [zero_universe]; exact Nat.zero_le _
  | succ n => exact cost_bound_positive (Nat.succ_pos n) tree requests

 theorem competitive : Competitive cost factor :=
  ⟨360012019,by decide,fun _ _ tree requests => cost_bound tree requests⟩

 theorem factor_le_third_log (n : Nat) : factor n ≤ 4*Splay.Analysis.iteratedLog 3 n :=
  Padding.factor_le_four_iteratedLog n

 theorem third_log_cost_bound {n : Nat} (tree : BST 0 n) (requests : List (Fin n)) :
    cost tree requests ≤ 1440048076*(OPT requests+n)*Splay.Analysis.iteratedLog 3 n := by
  calc
    _ ≤ 360012019*(OPT requests+n)*factor n := cost_bound tree requests
    _ ≤ 360012019*(OPT requests+n)*(4*Splay.Analysis.iteratedLog 3 n) :=
      Nat.mul_le_mul_left _ (factor_le_third_log n)
    _ = _ := by ring

/-- One uniform constant, arbitrary initial BST, all finite universes,
and the shared attained offline optimum. -/
 theorem third_log_competitive : Competitive cost (Splay.Analysis.iteratedLog 3) :=
  ⟨1440048076,by decide,fun _ _ tree requests => third_log_cost_bound tree requests⟩

 theorem competitor_bound {n : Nat} (tree competitor : BST 0 n) (requests : List (Fin n))
    {final : RawTree Nat} {paid : Nat}
    (other : SearchRotation.Execution competitor.toRaw (requests.map Fin.val) final paid) :
    cost tree requests ≤ 720024038*(paid+n)*factor n := by
  have optimum := SearchRotation.OPT_le_cost competitor requests other
  calc
    _ ≤ 360012019*(OPT requests+n)*factor n := cost_bound tree requests
    _ ≤ 360012019*(2*(paid+n))*factor n :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    _ = _ := by ring

/-- The padding state still runs the actual ordinary-splay request. The
shared projection realizes this same transition on only the original keys. -/
 theorem ordinary_active {n : Nat} (state : (projected n).State) (request : Fin n) :
    RequestExecution (OnlineSearchRotation.reference (Padding.height n)) state.memory (request.val : Int)
      state.components (Natural.next state (Fin.castLE (Padding.le_capacity n) request)).components :=
  Natural.ordinary state (Fin.castLE (Padding.le_capacity n) request)

end ChaCha.Paper20261030.SplayAuxiliary.All
