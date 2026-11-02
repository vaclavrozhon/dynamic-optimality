import Splay.Accounting.LogHeightChocolatePop

namespace Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate

open Splay.Tree OfflineNormalForm

/-- Weighted leaf bounds compose with the depth of a selected skeleton. -/
theorem height_le_weightedHeight_add {lower upper extra : ℕ} {tree : BST lower upper}
    (selected : RootPrefix tree)
    (payloads : selected.frontier.AllPayloads
      (fun payload => payload.height ≤ 7 * logMass payload + extra)) :
    tree.height ≤ weightedHeight selected + extra := by
  induction selected with
  | none => exact payloads
  | node left right ihL ihR =>
      obtain ⟨a, b⟩ := (SupportFrontier.allPayloads_append _ _).mp payloads
      have leftBound := ihL a
      have rightBound := ihR b
      simp only [BST.height, weightedHeight]
      omega

namespace Chocolate

theorem activeDepth_le_weightedHeight {kind : Bool} {level lower upper : ℕ}
    {tree : BST lower upper} (layer : Chocolate kind level tree) :
    layer.activeDepth ≤ weightedHeight layer.selected := by
  induction layer <;> simp only [activeDepth, selected, weightedHeight] <;> omega

theorem activeDepth_le_log {lower upper : ℕ} {tree : BST lower upper}
    (layer : Layer 0 tree) : layer.activeDepth ≤ 7 * logMass tree + 8 := by
  have geometry := layer.weightedHeight_le
  have depth := layer.activeDepth_le_weightedHeight
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at geometry
  omega

end Chocolate

/-- The capacity bounds physical keys, including literal attached payloads. -/
structure MinimumStack (capacity : ℕ) {lower upper : ℕ}
    (frontier : SupportFrontier lower upper) where
  tree : BST lower upper
  layer : Layer 0 tree
  frontier_eq : layer.selected.frontier = frontier
  fits : tree.size ≤ capacity

/-- A uniform worst-case bound used only to bound heights during a macro.
The amortized support and rotation cost remains an absolute constant. -/
def stackUnitCost (capacity : ℕ) : ℕ := 144 * (Nat.clog 2 (capacity + 1) + 1)

namespace MinimumStack

def potential {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : MinimumStack capacity frontier) : ℕ := 16 * stack.layer.potential

theorem potential_le_card {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : MinimumStack capacity frontier) : stack.potential ≤ 64 * frontier.card := by
  have credit := stack.layer.potential_le_card
  have count := congrArg SupportFrontier.card stack.frontier_eq
  simp only [RootPrefix.frontier_card] at count
  dsimp [potential]
  omega

theorem height_le {capacity lower upper extra : ℕ} {frontier : SupportFrontier lower upper}
    (stack : MinimumStack capacity frontier)
    (payloads : frontier.AllPayloads
      (fun payload => payload.height ≤ 7 * logMass payload + extra)) :
    stack.tree.height ≤ 7 * logMass stack.tree + 8 + extra := by
  have filled := height_le_weightedHeight_add stack.layer.selected
    (by rwa [stack.frontier_eq])
  have geometry := stack.layer.weightedHeight_le
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at geometry
  omega

theorem operationCost_le {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : MinimumStack capacity frontier) :
    16 * (stack.layer.activeDepth + 1) ≤ stackUnitCost capacity := by
  have depth := stack.layer.activeDepth_le_log
  have logBound := (Nat.log_le_clog 2 (stack.tree.size + 1)).trans
    (Nat.clog_mono_right 2 (Nat.add_le_add_right stack.fits 1))
  dsimp [logMass, mass] at depth
  dsimp [stackUnitCost]
  omega

theorem exists_initial {lower upper : ℕ} (capacity : ℕ)
    (frontier : SupportFrontier lower upper) (fits : frontier.tree.size ≤ capacity) :
    Nonempty (MinimumStack capacity frontier) := by
  induction frontier with
  | last payload => exact ⟨⟨payload, .base (.leaf payload), rfl, fits⟩⟩
  | next payload tail ih =>
      have tailFits : tail.tree.size ≤ capacity := by
        simp only [SupportFrontier.tree, BST.size] at fits
        omega
      obtain ⟨stack⟩ := ih tailFits
      obtain ⟨after, result, cost, frontierEq, path, amortized, worst⟩ :=
        stack.layer.exists_push (.leaf payload)
      have sourceSize := (BST.node payload tail.tree).size_add_lower_eq_upper
      have afterSize := after.size_add_lower_eq_upper
      refine ⟨⟨after, result, ?_, ?_⟩⟩
      · simpa only [Crumb.selected, RootPrefix.frontier, SupportFrontier.append,
          stack.frontier_eq] using frontierEq
      · calc
          after.size = (BST.node payload tail.tree).size :=
            Nat.add_right_cancel (afterSize.trans sourceSize.symm)
          _ ≤ capacity := fits

theorem exists_push {capacity lower root upper : ℕ}
    {frontier : SupportFrontier (root + 1) upper}
    (stack : MinimumStack capacity frontier) (payload : BST lower root)
    (fits : (BST.node payload stack.tree).size ≤ capacity) :
    ∃ (result : MinimumStack capacity (.next payload frontier)) (cost : ℕ),
      HasSupportedPath (.node payload stack.tree) result.tree cost cost ∧
      cost + result.potential ≤ stack.potential + 16 ∧ cost ≤ stackUnitCost capacity := by
  obtain ⟨after, layer, cost, same, path, amortized, worst⟩ :=
    stack.layer.exists_push (.leaf payload)
  have sameSize := Chocolate.mass_eq_of_interval after (.node payload stack.tree)
  have afterFits : after.size ≤ capacity := by dsimp [mass] at sameSize; omega
  have frontierEq : layer.selected.frontier = .next payload frontier := by
    simpa only [Crumb.selected, RootPrefix.frontier, SupportFrontier.append,
      stack.frontier_eq] using same
  refine ⟨⟨after, layer, frontierEq, afterFits⟩, cost, path, amortized, ?_⟩
  exact worst.trans stack.operationCost_le

theorem exists_pop {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : MinimumStack capacity frontier) (positive : 0 < frontier.card) :
    ∃ (root : ℕ) (payload : BST lower root) (rest : SupportFrontier (root + 1) upper)
      (result : MinimumStack capacity rest) (cost : ℕ),
      frontier = .next payload rest ∧ HasSupportedPath stack.tree (.node payload result.tree) cost cost ∧
      cost + result.potential ≤ stack.potential + 16 ∧ cost ≤ stackUnitCost capacity := by
  have active : 0 < stack.layer.activeDepth := by
    by_contra zero
    obtain ⟨crumb, same⟩ := stack.layer.eq_base_of_activeDepth_zero (by omega)
    have sameFrontier := stack.frontier_eq
    rw [same] at sameFrontier
    cases crumb
    simp only [Chocolate.selected, Crumb.selected, RootPrefix.frontier] at sameFrontier
    rw [← sameFrontier] at positive
    simp [SupportFrontier.card] at positive
  obtain ⟨root, payload, crumb, after, result, cost, same, path, amortized, worst⟩ :=
    stack.layer.exists_pop active
  cases crumb with
  | leaf payload =>
      have sizeEq := Chocolate.mass_eq_of_interval stack.tree (.node payload after)
      have fits : after.size ≤ capacity := by
        have beforeFits := stack.fits
        simp only [mass, BST.size] at sizeEq
        omega
      let updated : MinimumStack capacity result.selected.frontier := ⟨after, result, rfl, fits⟩
      refine ⟨root, payload, _, updated, cost, ?_, path, amortized, worst.trans stack.operationCost_le⟩
      rw [← stack.frontier_eq, same]
      rfl

end MinimumStack

end Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate
