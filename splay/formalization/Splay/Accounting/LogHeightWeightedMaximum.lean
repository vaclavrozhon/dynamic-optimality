import Splay.Accounting.LogHeightWeightedMinimum
import Splay.Accounting.LogHeightReflection

namespace Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate

open Splay.Tree OfflineNormalForm

/-- A maximum stack is the exact order reversal of a minimum stack. Ghost
labels are only a proof device; the exposed tree has the original key interval. -/
structure MaximumStack (capacity : ℕ) {lower upper : ℕ}
    (frontier : SupportFrontier lower upper) where
  imageLower : ℕ
  image : BST imageLower capacity
  layer : Layer 0 image
  tree : BST lower upper
  reflection : Reflection image tree
  frontier_eq : (reflection.restrict layer.selected).frontier = frontier

namespace MaximumStack

def potential {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : MaximumStack capacity frontier) : ℕ := 16 * stack.layer.potential

theorem fits {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : MaximumStack capacity frontier) : stack.tree.size ≤ capacity := by
  have count := stack.image.size_add_lower_eq_upper
  have same := stack.reflection.size_eq
  omega

theorem potential_le_card {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : MaximumStack capacity frontier) : stack.potential ≤ 64 * frontier.card := by
  have credit := stack.layer.potential_le_card
  have count := congrArg SupportFrontier.card stack.frontier_eq
  simp only [RootPrefix.frontier_card, Reflection.restrict_card] at count
  dsimp [potential]
  omega

theorem height_le {capacity lower upper extra : ℕ} {frontier : SupportFrontier lower upper}
    (stack : MaximumStack capacity frontier)
    (payloads : frontier.AllPayloads
      (fun payload => payload.height ≤ 7 * logMass payload + extra)) :
    stack.tree.height ≤ 7 * logMass stack.tree + 8 + extra := by
  have filled := height_le_weightedHeight_add (stack.reflection.restrict stack.layer.selected)
    (by rwa [stack.frontier_eq])
  rw [stack.reflection.weightedHeight_restrict] at filled
  have geometry := stack.layer.weightedHeight_le
  have same : logMass stack.tree = logMass stack.image := by
    simp only [logMass, mass, stack.reflection.size_eq]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at geometry
  omega

private theorem selected_frontier {lower upper : ℕ} (frontier : SupportFrontier lower upper) :
    frontier.selected.frontier = frontier := by
  induction frontier with
  | last => rfl
  | next payload tail ih => simpa only [SupportFrontier.selected, RootPrefix.frontier,
      SupportFrontier.append] using congrArg (SupportFrontier.next payload) ih

theorem exists_initial {lower upper : ℕ} (capacity : ℕ)
    (frontier : SupportFrontier lower upper) (fits : frontier.tree.size ≤ capacity) :
    Nonempty (MaximumStack capacity frontier) := by
  obtain ⟨imageUpper, image, ⟨reflection⟩, imageEnd⟩ :=
    Reflection.exists_image frontier.tree (capacity - frontier.tree.size)
  have endpoint : imageUpper = capacity := by omega
  clear imageEnd
  subst imageUpper
  let selected := reflection.restrict frontier.selected
  have imageFits : selected.frontier.tree.size ≤ capacity := by
    have bound := selected.frontier.tree.size_add_lower_eq_upper
    omega
  obtain ⟨minimum⟩ := MinimumStack.exists_initial capacity selected.frontier imageFits
  obtain ⟨physicalUpper, physical, ⟨resultReflection⟩, physicalEnd⟩ :=
    Reflection.exists_image minimum.tree lower
  have oldSize := frontier.tree.size_add_lower_eq_upper
  have newSize := minimum.tree.size_add_lower_eq_upper
  have endpoint : physicalUpper = upper := by omega
  clear physicalEnd
  subst physicalUpper
  refine ⟨⟨_, minimum.tree, minimum.layer, physical, resultReflection, ?_⟩⟩
  have equal := Reflection.frontier_eq_of_reflected resultReflection reflection.symm
    minimum.layer.selected selected minimum.frontier_eq
  rw [equal]
  dsimp [selected]
  rw [reflection.restrict_symm]
  exact selected_frontier frontier

theorem exists_push {capacity lower root upper : ℕ} {frontier : SupportFrontier lower root}
    (stack : MaximumStack capacity frontier) (payload : BST (root + 1) upper)
    (fits : (BST.node stack.tree payload).size ≤ capacity) :
    ∃ (result : MaximumStack capacity (frontier.append (.last payload))) (cost : ℕ),
      HasSupportedPath (.node stack.tree payload) result.tree cost cost ∧
      cost + result.potential ≤ stack.potential + 16 ∧ cost ≤ stackUnitCost capacity := by
  obtain ⟨imageLower, image, layer, tree, reflection, frontierEq⟩ := stack
  have count := image.size_add_lower_eq_upper
  have sameSize := reflection.size_eq
  change (BST.node tree payload).size ≤ capacity at fits
  simp only [BST.size] at fits
  cases imageLower with
  | zero => omega
  | succ imageLower =>
      have payloadFits : payload.size ≤ imageLower := by omega
      obtain ⟨incomingUpper, incoming, ⟨incomingReflection⟩, incomingEnd⟩ :=
        Reflection.exists_image payload (imageLower - payload.size)
      have endpoint : incomingUpper = imageLower := by omega
      clear incomingEnd
      subst incomingUpper
      let minimum : MinimumStack capacity layer.selected.frontier :=
        ⟨image, layer, rfl, by omega⟩
      obtain ⟨result, cost, path, amortized, worst⟩ := minimum.exists_push incoming
        (by
          have reflected := incomingReflection.size_eq
          change (BST.node incoming image).size ≤ capacity
          simp only [BST.size]
          omega)
      let initialReflection : Reflection (.node incoming image) (.node tree payload) :=
        .node incomingReflection.symm reflection
      obtain ⟨actual, ⟨resultReflection⟩, actualPath⟩ := path.reflect initialReflection
      have frontierSame : (resultReflection.restrict result.layer.selected).frontier =
          frontier.append (.last payload) := by
        have same := Reflection.frontier_eq_of_reflected resultReflection initialReflection
          result.layer.selected (.node (.none incoming) layer.selected) result.frontier_eq
        rw [same]
        simp only [initialReflection, Reflection.restrict, Reflection.restrict_none, RootPrefix.frontier, frontierEq]
      refine ⟨⟨_, result.tree, result.layer, actual, resultReflection, frontierSame⟩,
        cost, actualPath, amortized, worst⟩

private theorem reflected_node_exists {lo key hi lower upper : ℕ}
    {left : BST lo key} {right : BST (key + 1) hi} {actual : BST lower upper}
    (reflection : Reflection (.node left right) actual) :
    ∃ (root : ℕ) (actualLeft : BST lower root) (actualRight : BST (root + 1) upper),
      actual = .node actualLeft actualRight ∧
      Nonempty (Reflection left actualRight) ∧ Nonempty (Reflection right actualLeft) := by
  cases reflection with
  | node first last => exact ⟨_, _, _, rfl, ⟨first⟩, ⟨last⟩⟩

theorem exists_pop {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : MaximumStack capacity frontier) (positive : 0 < frontier.card) :
    ∃ (root : ℕ) (rest : SupportFrontier lower root) (payload : BST (root + 1) upper)
      (result : MaximumStack capacity rest) (cost : ℕ),
      frontier = rest.append (.last payload) ∧ HasSupportedPath stack.tree (.node result.tree payload) cost cost ∧
      cost + result.potential ≤ stack.potential + 16 ∧ cost ≤ stackUnitCost capacity := by
  have count := stack.image.size_add_lower_eq_upper
  let minimum : MinimumStack capacity stack.layer.selected.frontier :=
    ⟨stack.image, stack.layer, rfl, by omega⟩
  have selectedPositive : 0 < stack.layer.selected.frontier.card := by
    have same := congrArg SupportFrontier.card stack.frontier_eq
    simp only [RootPrefix.frontier_card, Reflection.restrict_card] at same ⊢
    omega
  obtain ⟨root, payload, rest, result, cost, frontierSame, path, amortized, worst⟩ :=
    minimum.exists_pop selectedPositive
  obtain ⟨actual, ⟨resultReflection⟩, actualPath⟩ := path.reflect stack.reflection
  obtain ⟨physicalRoot, physicalRest, physicalPayload, actualEq, ⟨first⟩, ⟨last⟩⟩ :=
    reflected_node_exists resultReflection
  cases actualEq
  let updated : MaximumStack capacity (last.restrict result.layer.selected).frontier :=
    ⟨root + 1, result.tree, result.layer, physicalRest, last, rfl⟩
  refine ⟨physicalRoot, _, physicalPayload, updated, cost, ?_, actualPath, amortized, worst⟩
  have same := Reflection.frontier_eq_of_reflected stack.reflection (.node first last)
    stack.layer.selected (.node (.none payload) result.layer.selected)
    (by simpa only [RootPrefix.frontier, SupportFrontier.append, result.frontier_eq] using frontierSame)
  rw [← stack.frontier_eq, same]
  simp only [Reflection.restrict, Reflection.restrict_none, RootPrefix.frontier]

end MaximumStack

end Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate
