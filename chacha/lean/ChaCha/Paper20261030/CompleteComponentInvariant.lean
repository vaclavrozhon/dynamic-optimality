import ChaCha.Paper20261030.CanonicalPhysicalHeaders

/-! Individual complete components retain the original key word and the
uniform physical record capacity, including nested payload attachments. -/

namespace ChaCha.Paper20261030.PackedPrimary

open ColoredStorage PreferredProjection PrimaryWings PrimaryPhysical

variable {α ρ : Type*} [DecidableEq α]

theorem Input.physical_bounded {primary : PrefRouter α} (input : Input primary ρ)
    (payload : Exit α → Source α (List (Option (Datum ρ))))
    (bounded : ∀ exit, (payload exit).Bounded 5)
    (rootBound : ∀ exit, (payload exit).rootRecord.length ≤ 1) : (input.physical payload).Bounded 5 := by
  apply component_bounded
  · exact graftWing_bounded payload input.completePlan.left 3 1 input.completePlan_bounded.1 bounded rootBound
  · exact graftWing_bounded payload input.completePlan.right 3 1 input.completePlan_bounded.2 bounded rootBound
  · simp [Input.completeHeader]

theorem Input.physical_root_bound {primary : PrefRouter α} (input : Input primary ρ)
    (payload : Exit α → Source α (List (Option (Datum ρ)))) : (input.physical payload).rootRecord.length ≤ 1 :=
  component_root_bound _ _ _ _

theorem Input.physical_leaves {primary : PrefRouter α} (input : Input primary ρ)
    (payload : Exit α → Source α (List (Option (Datum ρ))))
    (words : ∀ exit, (payload exit).shape.leaves = exit.subtree.leaves) :
    (input.physical payload).shape.leaves = primary.leaves := by
  rw [Input.physical,PrimaryPhysical.component_leaves,graftWing_leaves,graftWing_leaves]
  simp only [input.completePlan_words.1,input.completePlan_words.2,words]
  exact (leaf_partition primary).symm

end ChaCha.Paper20261030.PackedPrimary
