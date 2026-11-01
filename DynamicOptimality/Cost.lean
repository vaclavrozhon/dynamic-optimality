import DynamicOptimality.Basic
import Splay.Accounting.OfflineOptimum

/-!
# Shared offline optimum and competitive statements

`OPT` is exactly the already proved, attained offline minimum from the
splay development. It counts one per request and one per rotation, with
a freely chosen initial tree. The cost of adjacent cursor movement is
not identified with this rotation cost by definition.

`Competitive cost factor` uses one universal multiplicative constant and
an additive initial-tree allowance of `n` inside that factor. Setting the
factor to one gives the dynamic-optimality statement used here.
-/

namespace DynamicOptimality

abbrev OfflineExecution := @Splay.Accounting.OfflineOptimum.Execution
noncomputable abbrev OPT := @Splay.Accounting.OfflineOptimum.offlineOptCost

abbrev AlgorithmCost := {n : Nat} → BST 0 n → List (Fin n) → Nat

def Competitive (cost : AlgorithmCost) (factor : Nat → Nat) : Prop :=
  ∃ C : Nat, 0 < C ∧ ∀ n : Nat, 0 < n →
    ∀ initial : BST 0 n, ∀ requests : List (Fin n),
      cost initial requests ≤ C * (OPT requests + n) * factor n

def DynamicallyOptimal (cost : AlgorithmCost) : Prop :=
  Competitive cost (fun _ => 1)

theorem OPT_attained {n : Nat} (requests : List (Fin n)) :
    ∃ (initial final : BST 0 n) (rotations : Nat),
      OfflineExecution requests initial final rotations ∧
      OPT requests = requests.length + rotations :=
  Splay.Accounting.OfflineOptimum.exists_optimalExecution_eq requests

theorem OPT_le_execution {n rotations : Nat} {requests : List (Fin n)}
    {initial final : BST 0 n} (execution : OfflineExecution requests initial final rotations) :
    OPT requests ≤ requests.length + rotations :=
  Splay.Accounting.OfflineOptimum.offlineOptCost_le_ofExecution execution

/-- The existing public splay statement is definitionally the shared
competitive statement, with the same actual algorithm and the same OPT. -/
theorem splay_target_iff :
    Splay.TargetBound Splay.Accounting.OfflineOptimum.concreteOfflineCostModel ↔
      Competitive Splay.Accounting.concreteSplayCost Splay.Analysis.targetFactor :=
  Iff.rfl

end DynamicOptimality
