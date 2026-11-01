import Splay.Accounting.OfflineConnectedNormalization

namespace Splay.Assumptions.OfflineModelEquivalence

open Splay.Accounting.OfflineConnectedSupport

/--
Compatibility name for the proved offline model-equivalence theorem.

It states the nontrivial direction of constant-factor equivalence between the
active arbitrary-rotation root model and the root-connected support model used
by the manuscript's normal-form proof.  In the target model, every modified
region is an ancestor-closed prefix containing the root, and its cardinality is
charged.  The reverse inequality is already a theorem: forgetting the support
certificate gives an arbitrary-rotation execution.

The proof postpones rotations outside each request's connected support and
obtains the explicit cost multiplier two. It does not yet construct the
logarithmic-height, bounded-depth, ribless structural normal form; that is the
separate downstream Bose--Brodal--Cleary simulation.
-/
theorem connectedSupportNormalization :
    UniformConnectedSupportNormalization :=
  uniformConnectedSupportNormalization

/-- Constructive optimal-execution form of the proved model equivalence. -/
theorem optimalExecutionConnectedNormalizer :
    UniformOptimalExecutionConnectedNormalizer :=
  uniformOptimalExecutionConnectedNormalizer_iff_costNormalization.mpr
    connectedSupportNormalization

/-- The two attained optimum costs are within a universal constant factor. -/
theorem optimumCostsWithinConstantFactor :
    ∃ multiplier : ℕ,
      ∀ (n : ℕ) (accesses : List (Fin n)),
        Splay.Accounting.OfflineOptimum.offlineOptCost accesses ≤
            connectedOptCost accesses ∧
          connectedOptCost accesses ≤
            multiplier *
              Splay.Accounting.OfflineOptimum.offlineOptCost accesses := by
  obtain ⟨multiplier, upper⟩ := connectedSupportNormalization
  refine ⟨multiplier, ?_⟩
  intro n accesses
  exact ⟨offlineOptCost_le_connectedOptCost accesses,
    upper n accesses⟩

end Splay.Assumptions.OfflineModelEquivalence
