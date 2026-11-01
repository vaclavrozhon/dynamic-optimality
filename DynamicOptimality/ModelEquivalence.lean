import DynamicOptimality.ConnectedPointer

/-! The shared competitive statement is equivalent to comparison against
every genuine root-starting adjacent-pointer BST execution. -/

namespace DynamicOptimality

theorem competitive_iff_pointer (cost : AlgorithmCost) (factor : Nat → Nat) :
    Competitive cost factor ↔
      ∃ C : Nat, 0 < C ∧ ∀ n : Nat, 0 < n →
        ∀ initial : BST 0 n, ∀ requests : List (Fin n),
          ∀ competitor : BST 0 n, ∀ final : RawTree Nat, ∀ pointerCost : Nat,
            PointerExecution competitor.toRaw (requests.map Fin.val) final pointerCost →
            cost initial requests ≤ C * (pointerCost + n) * factor n := by
  constructor
  · rintro ⟨C,hC,bound⟩
    refine ⟨13 * C,by omega,?_⟩
    intro n hn initial requests competitor final pointerCost execution
    have opt := OPT_le_pointer_cost competitor requests execution
    calc
      _ ≤ C * (OPT requests + n) * factor n := bound n hn initial requests
      _ ≤ C * (13 * (pointerCost + n)) * factor n :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      _ = _ := by ring
  · rintro ⟨C,hC,bound⟩
    refine ⟨37 * C,by omega,?_⟩
    intro n hn initial requests
    obtain ⟨competitor,final,pointerCost,execution,cp⟩ := exists_pointer_of_OPT requests
    calc
      _ ≤ C * (pointerCost + n) * factor n :=
        bound n hn initial requests competitor final pointerCost execution
      _ ≤ C * (37 * (OPT requests + n)) * factor n :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      _ = _ := by ring

end DynamicOptimality
