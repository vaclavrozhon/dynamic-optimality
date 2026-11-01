import CutPath
import BlockLifetime

namespace GreedyForest.Execution

/-- A phase's internal bad links across one historical cut inject into
strict-rise crossing edges of its active Cartesian tree, plus two possible
augmented leaf edges. The tree count is proved, not assumed as k+1. -/
structure CutPhaseGeometry (k crossings : ℕ) where
  tree : CutTree
  ordered : CutOrdered tree
  labels : LabelBounded (k:ℤ) 1 tree
  project : Fin crossings → Sum (Fin (badCutCount tree).toNat) (Fin 2)
  injective : Function.Injective project

theorem CutPhaseGeometry.bound {k crossings : ℕ}
    (h : CutPhaseGeometry k crossings) (hk : 1 ≤ k) : crossings ≤ k+1 := by
  have hproj := Fintype.card_le_of_injective h.project h.injective
  have hc : crossings ≤ (badCutCount h.tree).toNat + 2 := by simpa using hproj
  have ht := badCutCount_le_levels (k:ℤ) 1 h.tree (by exact_mod_cast hk) h.ordered h.labels
  have hn : (badCutCount h.tree).toNat ≤ k-1 := by omega
  omega

/-- Local no-merge and source-collapse conditions, with no numerical
crossing-capacity premise. Geometry supplies that premise separately. -/
def CutTransitions (cut : ℕ) (before : Family ℕ) : List (Family ℕ × ℕ) → Prop
  | [] => True
  | (after, crossings) :: rest =>
      UniqueStraddler (fun x => decide (cut ≤ x)) before ∧
      Refines after before ∧
      (0 < crossings → ∃ source ∈ before,
        Straddles (fun x => decide (cut ≤ x)) source ∧ Collapses source before after) ∧
      CutTransitions cut after rest

theorem cutTransitions_to_valid {cut k : ℕ} (before : Family ℕ)
    (steps : List (Family ℕ × ℕ)) (hk : 1 ≤ k)
    (htrans : CutTransitions cut before steps)
    (hgeometry : ∀ step ∈ steps, Nonempty (CutPhaseGeometry k step.2)) :
    ValidCutRun (fun x => decide (cut ≤ x)) (k+1) before steps := by
  induction steps generalizing before with
  | nil => trivial
  | cons step rest ih =>
      rcases step with ⟨after, crossings⟩
      rcases htrans with ⟨hu, hr, hc, htail⟩
      obtain ⟨geom⟩ := hgeometry (after, crossings) (by simp)
      exact ⟨hu, hr, geom.bound hk, hc,
        ih after htail (fun step hs => hgeometry step (by simp [hs]))⟩

end GreedyForest.Execution
