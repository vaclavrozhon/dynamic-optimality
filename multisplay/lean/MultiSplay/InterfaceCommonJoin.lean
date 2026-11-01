import MultiSplay.InterfaceSum
import MultiSplay.InterfacePriorityJoin
import MultiSplay.JoinIntervals

/-!
# Constructing the strict common join from two current interface states

The inputs are arbitrary valid current histories, with their neutral unassigned
component roots. Their disjoint sum and the new pivot determine the full legal
join trace. Neither input is reinitialized, and no stored pass count is reset.
-/

namespace MultiSplay.InterfaceCommonJoin

open Splay.Interface
open JoinIntervals (leftEmbedding rightEmbedding)

variable {l r : Nat}

noncomputable def initial (a : State l) (b : State r) : State (0 + l + 1 + r) :=
  InterfaceSum.state (leftEmbedding l r) (rightEmbedding l r) a b

noncomputable def final (a : State l) (b : State r) (leftRoot : Element l) (rightRoot : Element r) : State (0 + l + 1 + r) :=
  InterfaceForest.priorityJoin (initial a b) (JoinRanks.pivot l r)
    (leftEmbedding l r leftRoot) (rightEmbedding l r rightRoot)

noncomputable def operations (a : State l) (b : State r) (leftRoot : Element l) (rightRoot : Element r) :
    List (Operation (0 + l + 1 + r)) :=
  InterfaceForest.priorityJoinWord (initial a b) (JoinRanks.pivot l r)
    (leftEmbedding l r leftRoot) (rightEmbedding l r rightRoot)

theorem trace {params : Parameters} (a : State l) (b : State r) (leftRoot : Element l) (rightRoot : Element r)
    (leftValid : a.Valid params) (rightValid : b.Valid params)
    (leftFree : leftRoot ∉ a.allElements) (rightFree : rightRoot ∉ b.allElements)
    (leftOne : a.value leftRoot = 1) (rightOne : b.value rightRoot = 1)
    (growingLimit : 2 ≤ params.growingLimit) (valueCap : 3 ≤ params.valueBound) :
    Trace params (initial a b) (operations a b leftRoot rightRoot) (final a b leftRoot rightRoot) := by
  unfold operations final initial
  apply InterfaceForest.priorityJoin_trace
  · exact InterfaceSum.valid _ _ (RankEmbedding.external_injective _ _) (RankEmbedding.external_injective _ _)
      (JoinIntervals.disjoint l r) leftValid rightValid
  · exact JoinIntervals.left_ne_pivot _ _ _
  · exact JoinIntervals.right_ne_pivot _ _ _
  · exact (JoinIntervals.disjoint l r leftRoot rightRoot).symm
  · exact valueCap
  · exact InterfaceSum.value_outside _ _ a b _
      (by rintro ⟨x, same⟩; exact JoinIntervals.left_ne_pivot l r x same)
      (by rintro ⟨x, same⟩; exact JoinIntervals.right_ne_pivot l r x same)
  · rw [InterfaceSum.value_left _ _ (RankEmbedding.external_injective _ _)]
    exact leftOne
  · rw [InterfaceSum.value_right _ _ (RankEmbedding.external_injective _ _) (JoinIntervals.disjoint l r)]
    exact rightOne
  · rw [InterfaceSum.allElements]
    intro member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨x, xm, same⟩ := List.mem_map.mp member
      exact leftFree ((RankEmbedding.external_injective _ _ same) ▸ xm)
    · obtain ⟨x, _, same⟩ := List.mem_map.mp member
      exact JoinIntervals.disjoint l r leftRoot x same.symm
  · rw [InterfaceSum.allElements]
    intro member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨x, _, same⟩ := List.mem_map.mp member
      exact JoinIntervals.disjoint l r x rightRoot same
    · obtain ⟨x, xm, same⟩ := List.mem_map.mp member
      exact rightFree ((RankEmbedding.external_injective _ _ same) ▸ xm)
  · rw [InterfaceSum.growing_outside _ _ a b _
      (by rintro ⟨x, same⟩; exact JoinIntervals.left_ne_pivot l r x same)
      (by rintro ⟨x, same⟩; exact JoinIntervals.right_ne_pivot l r x same)]
    exact growingLimit

theorem old_left_value (a : State l) (b : State r) (leftRoot : Element l) (rightRoot : Element r)
    (element : Element l) (notRoot : element ≠ leftRoot) :
    (final a b leftRoot rightRoot).value (leftEmbedding l r element) = a.value element := by
  rw [final, InterfaceForest.priorityJoin_other_value]
  · exact InterfaceSum.value_left _ _ (RankEmbedding.external_injective _ _) _ _ _
  · exact fun same => notRoot (RankEmbedding.external_injective _ _ same)
  · exact JoinIntervals.disjoint _ _ _ _

theorem old_right_value (a : State l) (b : State r) (leftRoot : Element l) (rightRoot : Element r)
    (element : Element r) (notRoot : element ≠ rightRoot) :
    (final a b leftRoot rightRoot).value (rightEmbedding l r element) = b.value element := by
  rw [final, InterfaceForest.priorityJoin_other_value]
  · exact InterfaceSum.value_right _ _ (RankEmbedding.external_injective _ _) (JoinIntervals.disjoint _ _) _ _ _
  · exact (JoinIntervals.disjoint _ _ _ _).symm
  · exact fun same => notRoot (RankEmbedding.external_injective _ _ same)

@[simp] theorem inserts (a : State l) (b : State r) (leftRoot : Element l) (rightRoot : Element r) :
    totalInserts (operations a b leftRoot rightRoot) = 2 := InterfaceForest.priorityJoinWord_inserts _ _ _ _

@[simp] theorem increases (a : State l) (b : State r) (leftRoot : Element l) (rightRoot : Element r) :
    totalIncreases (operations a b leftRoot rightRoot) = 4 := InterfaceForest.priorityJoinWord_increases _ _ _ _

@[simp] theorem activity (a : State l) (b : State r) (leftRoot : Element l) (rightRoot : Element r) :
    totalActivity (operations a b leftRoot rightRoot) = 0 := InterfaceForest.priorityJoinWord_activity _ _ _ _

end MultiSplay.InterfaceCommonJoin
