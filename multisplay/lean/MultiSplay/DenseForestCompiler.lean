import MultiSplay.DenseForestTransactions

/-! # Compiling an independently supplied bounded raw comparator -/

namespace MultiSplay.DenseForest

open DynamicOptimality (RawTree)
open Splay.Accounting (articleParameters)

variable {α : Type*} {height slack : Nat}

def Access (height slack : Nat) : CommonForest.Access α := fun key before after work =>
  CommonForest.RootAccess key before after work ∧ BoundedMacros.Geometry height slack before

abbrev Trace (height slack : Nat) := @CommonForest.Trace α (Access height slack) (BoundedMacros.Preparation height slack)

theorem compile_step {before after : List (RawTree α)} {word : List (CommonForest.Event α)} {budget : Nat}
    (step : CommonForest.Step (Access height slack) (BoundedMacros.Preparation height slack) before word after budget)
    (cap : 3 ≤ (articleParameters height).valueBound)
    (initial : List (Component α)) (same : initial.map Component.source = before) :
    ∃ final : List (Component α), final.map Component.source = after ∧ Nonempty (Execution height slack initial final word budget) := by
  induction step generalizing initial with
  | search execution =>
      obtain ⟨access, geometry⟩ := execution
      cases access with
      | root left key right =>
          obtain ⟨component, rfl, sourceEq⟩ := List.map_eq_singleton_iff.mp same
          obtain ⟨result, resultEq, actual⟩ := service component sourceEq (sourceEq.symm ▸ geometry)
          refine ⟨[result], by simp [resultEq, sourceEq], ?_⟩
          simpa only [sourceEq] using actual
  | split execution =>
      obtain ⟨access, geometry⟩ := execution
      cases access with
      | root left key right =>
          obtain ⟨component, rfl, sourceEq⟩ := List.map_eq_singleton_iff.mp same
          obtain ⟨a, b, leftEq, rightEq, actual⟩ := split component sourceEq (sourceEq.symm ▸ geometry)
          exact ⟨[a,b], by simp [leftEq, rightEq], actual⟩
  | join left right key =>
      obtain ⟨a, rest, rfl, leftEq, restEq⟩ := List.map_eq_cons_iff.mp same
      obtain ⟨b, rfl, rightEq⟩ := List.map_eq_singleton_iff.mp restEq
      obtain ⟨result, resultEq, actual⟩ := join_service a b key cap
      refine ⟨[result], by simp [resultEq, leftEq, rightEq], ?_⟩
      simpa only [leftEq, rightEq] using actual
  | prepare preparation =>
      obtain ⟨component, rfl, sourceEq⟩ := List.map_eq_singleton_iff.mp same
      obtain ⟨result, resultEq, actual⟩ := prepare_service component (sourceEq.symm ▸ preparation)
      exact ⟨[result], by simp [resultEq], actual⟩
  | @context a b events cost step front back ih =>
      obtain ⟨frontStates, rest, rfl, frontEq, restEq⟩ := List.map_eq_append_iff.mp
        (show initial.map Component.source = front ++ (a ++ back) by simpa only [List.append_assoc] using same)
      obtain ⟨selected, backStates, rfl, selectedEq, backEq⟩ := List.map_eq_append_iff.mp restEq
      obtain ⟨final, finalEq, ⟨actual⟩⟩ := ih selected selectedEq
      refine ⟨frontStates++final++backStates, ?_, ?_⟩
      · simp only [List.map_append, frontEq, finalEq, backEq]
      · simpa only [List.append_assoc] using actual.context frontStates backStates
  | @reorder a b order =>
      have permutation : (initial.map Component.source).Perm _ := same ▸ order
      have lifted : Relation.Comp (fun a b => a = b.map Component.source) List.Perm b initial := by
        rw [List.eq_map_comp_perm]
        exact permutation.symm
      obtain ⟨final, finalEq, localOrder⟩ := lifted
      exact ⟨final, finalEq.symm, ⟨Execution.reorder localOrder.symm⟩⟩

/-- Every raw normalizer step is translated, in chronological order, retaining
the actual splay children and all unrelated components. -/
theorem compile {before after : List (RawTree α)} {word : List (CommonForest.Event α)} {budget : Nat}
    (trace : Trace height slack before word after budget) (cap : 3 ≤ (articleParameters height).valueBound)
    (initial : List (Component α)) (same : initial.map Component.source = before) :
    ∃ final : List (Component α), final.map Component.source = after ∧ Nonempty (Execution height slack initial final word budget) := by
  induction trace generalizing initial with
  | nil forest => exact ⟨initial, same, ⟨Execution.done initial⟩⟩
  | cons head tail ih =>
      obtain ⟨middle, middleEq, ⟨first⟩⟩ := compile_step head cap initial same
      obtain ⟨final, finalEq, ⟨last⟩⟩ := ih middle middleEq
      exact ⟨final, finalEq, ⟨first.append last⟩⟩

end MultiSplay.DenseForest
