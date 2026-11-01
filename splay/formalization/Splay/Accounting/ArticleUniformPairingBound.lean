import Splay.Accounting.ArticleInitializedBoundaryEstimate
import Splay.Accounting.BoundaryCreditUniformBound

namespace Splay.Accounting.ConstructedPolylogNormalForm

open Splay.Tree.BST Splay.Assumptions.NormalForm

/-- Uniform control of the complete actual run. The interface constants are
chosen once, before the tree size, access sequence, or gap cap is supplied. -/
theorem articleRun_activity_add_boundary :
    ∃ constant : ℕ, 0 < constant ∧ ∀ (n : ℕ) (tree : BST 0 n) (accesses : List (Fin n)), 0 < n →
      let run := articleRun tree accesses
      let gap := (articleParameters (comparisonProfile.maxHeight accesses)).valueBound
      Interface.totalActivity run.operations + run.boundaryCount ≤
        constant * (n + (trace accesses).cost) * gap * (Nat.clog 2 gap + 1) ^ 2 := by
  obtain ⟨a, b, aPositive, bPositive, interfaceBound⟩ := Interface.activityBound articleShape
  let coefficient := 64 * (a + b + 1)
  have coefficientPositive : 0 < coefficient := by dsimp [coefficient]; omega
  obtain ⟨constant, constantPositive, bound⟩ := boundary_credit_uniform_bound coefficient 79855 coefficientPositive
  refine ⟨constant, constantPositive, ?_⟩
  intro n tree accesses positive
  dsimp only
  let run := articleRun tree accesses
  let gap := (articleParameters (comparisonProfile.maxHeight accesses)).valueBound
  let volume := n + (trace accesses).cost
  have gapPositive : 0 < gap := lt_of_lt_of_le (by decide : 0 < 2) (articleParameters _).valueBound_ge_two
  apply bound gap volume (Interface.totalActivity run.operations) run.boundaryCount gapPositive
  · have raw := interfaceBound (articleParameters (comparisonProfile.maxHeight accesses)) rfl
      run.initialState run.trace.toInterface
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
    have enlarged : Interface.totalActivity run.operations ≤
        a * gap * (3 * volume + 2 * run.boundaryCount) +
          b * Nat.clog 2 gap * (36 * gap * volume + 32 * gap * run.boundaryCount) := by
      apply raw.trans
      exact Nat.add_le_add (Nat.mul_le_mul_left _ insertsBound) (Nat.mul_le_mul_left _ valuesBound)
    have first : a * gap * (3 * volume + 2 * run.boundaryCount) ≤
        3 * a * gap * (Nat.clog 2 gap + 1) * (volume + run.boundaryCount) := by
      calc
        _ ≤ a * gap * (3 * (volume + run.boundaryCount)) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = 3 * a * gap * 1 * (volume + run.boundaryCount) := by ring
        _ ≤ _ := by gcongr <;> omega
    have second : b * Nat.clog 2 gap * (36 * gap * volume + 32 * gap * run.boundaryCount) ≤
        36 * b * gap * (Nat.clog 2 gap + 1) * (volume + run.boundaryCount) := by
      calc
        _ ≤ b * Nat.clog 2 gap * (36 * gap * (volume + run.boundaryCount)) :=
          Nat.mul_le_mul_left _ (by nlinarith)
        _ = 36 * b * gap * Nat.clog 2 gap * (volume + run.boundaryCount) := by ring
        _ ≤ _ := by gcongr <;> omega
    have coefficientBound : 3 * a + 36 * b ≤ coefficient := by dsimp [coefficient]; omega
    have finalBound := Nat.mul_le_mul_right (gap * (Nat.clog 2 gap + 1) * (volume + run.boundaryCount)) coefficientBound
    nlinarith
  · intro cutoff
    have estimate := articleRun_boundary_estimate (cutoff := cutoff) tree accesses positive
    change cutoff * (2 * run.boundaryCount) ≤
      319420 * cutoff * Interface.boundaryCreditCapacity cutoff * volume +
        16 * Interface.totalActivity run.operations at estimate
    nlinarith

end Splay.Accounting.ConstructedPolylogNormalForm
