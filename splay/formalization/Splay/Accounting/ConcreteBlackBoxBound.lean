import Splay.Analysis.CoefficientFactor
import Splay.Accounting.BoundaryCreditRateBound
import Splay.Accounting.ConcreteTargetBound
import Splay.FactorBound

namespace Splay.Accounting.ConstructedPolylogNormalForm

open Splay.Tree.BST Splay.Assumptions.NormalForm

/-- The gap cap of the fixed, physically constructed comparison trace.
It depends only on the universe size, not on the access word. -/
def interfaceGapCap (n : ℕ) : ℕ :=
  (articleParameters (54000 * (Analysis.stabilizedLog n) ^ 3)).valueBound

theorem interfaceGapCap_ge_two (n : ℕ) : 2 ≤ interfaceGapCap n :=
  (articleParameters _).valueBound_ge_two

/-- The actual pairing estimate accepts any interface coefficient function.
Its constant is independent even of the chosen coefficient function. -/
theorem articleRun_activity_add_boundary_of_coefficients :
    ∃ constant : ℕ, 0 < constant ∧
      ∀ coefficients : Interface.ActivityCoefficients,
        Interface.CoefficientBound articleShape coefficients →
        ∀ (n : ℕ) (tree : BST 0 n) (accesses : List (Fin n)), 0 < n →
          Interface.totalActivity (articleRun tree accesses).operations +
            (articleRun tree accesses).boundaryCount ≤
          constant * (n + (trace accesses).cost) *
            Analysis.coefficientFactor coefficients (interfaceGapCap n) := by
  obtain ⟨constant, positive, bound⟩ := boundary_credit_rate_bound 36 79855 (by decide)
  refine ⟨constant, positive, ?_⟩
  intro coefficients valid n tree accesses positive
  let run := articleRun tree accesses
  let gap := interfaceGapCap n
  let volume := n + (trace accesses).cost
  let a := (coefficients gap).1
  let b := (coefficients gap).2
  change Interface.totalActivity run.operations + run.boundaryCount ≤
    constant * volume * Analysis.coefficientFactor coefficients gap
  rw [Analysis.coefficientFactor, ← Nat.mul_assoc]
  apply bound _ volume _ _ (Analysis.coefficientRate_pos coefficients gap)
  · have raw := valid (articleParameters (comparisonProfile.maxHeight accesses)) rfl
      run.initialState run.trace.toInterface
    change Interface.totalActivity run.operations ≤
      a * Interface.totalInserts run.operations + b * Interface.totalValueChanges run.operations at raw
    have inserts := run.inserts
    have values := run.valueChanges
    have volumeBound : 2 * n + 1 + (trace accesses).rotationCount ≤ 3 * volume := by
      dsimp [volume, ComparisonTrace.cost]
      omega
    have insertsBound : Interface.totalInserts run.operations ≤ 3 * volume + 2 * run.boundaryCount := by omega
    have valuesBound : Interface.totalValueChanges run.operations ≤
        36 * gap * volume + 32 * gap * run.boundaryCount := by
      change Interface.totalValueChanges run.operations ≤
        9 * gap * (2 * n + 1) + 32 * gap * run.boundaryCount +
          12 * gap * (trace accesses).rotationCount at values
      nlinarith [Nat.mul_le_mul_left (12 * gap) volumeBound]
    have enlarged := raw.trans (Nat.add_le_add (Nat.mul_le_mul_left a insertsBound)
      (Nat.mul_le_mul_left b valuesBound))
    change Interface.totalActivity run.operations ≤ 36 * (a + gap * b + 1) * (volume + run.boundaryCount)
    apply enlarged.trans
    ring_nf
    omega
  · intro cutoff
    have estimate := articleRun_boundary_estimate (cutoff := cutoff) tree accesses positive
    change cutoff * (2 * run.boundaryCount) ≤
      319420 * cutoff * Interface.boundaryCreditCapacity cutoff * volume +
        16 * Interface.totalActivity run.operations at estimate
    nlinarith

/-- Plugging in interface coefficients requires no new splay execution,
comparison-tree, or boundary-credit proof. -/
theorem concrete_cost_of_coefficients :
    ∃ constant : ℕ, 0 < constant ∧
      ∀ coefficients : Interface.ActivityCoefficients,
        Interface.CoefficientBound articleShape coefficients →
        ∀ (n : ℕ) (tree : BST 0 n) (accesses : List (Fin n)), 0 < n →
          concreteSplayCost tree accesses ≤
            constant * (OfflineOptimum.offlineOptCost accesses + n) *
              Analysis.coefficientFactor coefficients (interfaceGapCap n) := by
  obtain ⟨constant, positive, bound⟩ := articleRun_activity_add_boundary_of_coefficients
  refine ⟨(4 * constant + 268) * 400000001, by positivity, ?_⟩
  intro coefficients valid n tree accesses positive
  have paid := bound coefficients valid n tree accesses positive
  have cost := articleRun_cost_le_pairings tree accesses
  have factorPositive := Analysis.coefficientFactor_pos coefficients (interfaceGapCap n)
  have lower := Nat.mul_le_mul_left (268 * (n + (trace accesses).cost)) factorPositive
  have total : concreteSplayCost tree accesses ≤
      (4 * constant + 268) * (n + (trace accesses).cost) *
        Analysis.coefficientFactor coefficients (interfaceGapCap n) := by nlinarith
  have comparisonCost := trace_cost accesses
  have volume : n + (trace accesses).cost ≤
      400000001 * (OfflineOptimum.offlineOptCost accesses + n) := by omega
  calc
    _ ≤ _ := total
    _ ≤ (4 * constant + 268) * (400000001 * (OfflineOptimum.offlineOptCost accesses + n)) *
        Analysis.coefficientFactor coefficients (interfaceGapCap n) := by gcongr
    _ = _ := by ring

end Splay.Accounting.ConstructedPolylogNormalForm

namespace Splay

/-- Public black-box transfer to the actual standard splay algorithm and
the attained offline optimum. All interface hypotheses are explicit. -/
theorem concreteBound_of_activityCoefficients
    (coefficients : Interface.ActivityCoefficients)
    (valid : Interface.CoefficientBound Accounting.articleShape coefficients) :
    FactorBound Accounting.OfflineOptimum.concreteOfflineCostModel
      (fun n => Analysis.coefficientFactor coefficients
        (Accounting.ConstructedPolylogNormalForm.interfaceGapCap n)) := by
  obtain ⟨constant, positive, bound⟩ :=
    Accounting.ConstructedPolylogNormalForm.concrete_cost_of_coefficients
  exact ⟨constant, positive, fun n positive initial accesses =>
    bound coefficients valid n initial accesses positive⟩

end Splay
