import BlockLifetime
import FringeProjection

namespace GreedyForest.Execution

/-- The phase's wins inject into outgoing edges of a canonical fringe
projection. The degree is derived from local neighborhood minima and
the canonical Cartesian tree, not assumed numerically. -/
structure WinnerPhaseGeometry (wins : ℕ) where
  lo : ℕ
  hi : ℕ
  rank : ℕ → ℕ
  owner : ℕ → ℕ
  tree : Splay.Tree.BST lo hi
  parent : ℕ
  canonical : GreedyMerge.Plateau.Cartesian (GreedyMerge.Plateau.Priority rank) tree
  localOwners : GreedyMerge.Fringe.LocalOwners rank owner lo hi
  uniqueIntervals : GreedyMerge.Fringe.UniqueIntervals rank (2*lo) (2*hi)
  project : Fin wins → Fin (GreedyMerge.Fringe.outgoing owner parent tree).length
  injective : Function.Injective project

theorem WinnerPhaseGeometry.bound {wins : ℕ} (h : WinnerPhaseGeometry wins) : wins ≤ 4 := by
  have hproj := GreedyMerge.Fringe.projection_of_cartesian
    h.rank h.owner h.tree h.canonical h.localOwners h.uniqueIntervals
  have ht := GreedyMerge.Fringe.outgoing_degree_le_four h.rank h.owner h.tree h.parent
    hproj h.localOwners
  have hc := Fintype.card_le_of_injective h.project h.injective
  simp only [Fintype.card_fin] at hc
  omega

/-- Local partition transitions with the phase degree omitted; the
canonical fringe geometry supplies that degree. -/
def FamilyTransitions (v : ℕ) (before : Family ℕ) : List (Family ℕ × ℕ) → Prop
  | [] => True
  | (after, wins) :: rest =>
      Partitioned before ∧ Refines after before ∧
      (0 < wins → ¬ Isolated v before ∧
        ∃ source ∈ before, v ∈ source ∧ Collapses source before after) ∧
      FamilyTransitions v after rest

theorem familyTransitions_to_valid {v : ℕ} (before : Family ℕ)
    (steps : List (Family ℕ × ℕ)) (ht : FamilyTransitions v before steps)
    (hg : ∀ step ∈ steps, Nonempty (WinnerPhaseGeometry step.2)) :
    ValidFamilyRun v 4 before steps := by
  induction steps generalizing before with
  | nil => trivial
  | cons step rest ih =>
      rcases step with ⟨after, wins⟩
      rcases ht with ⟨hp, hr, hc, htail⟩
      obtain ⟨geom⟩ := hg (after,wins) (by simp)
      exact ⟨hp, hr, geom.bound, hc,
        ih after htail (fun step hs => hg step (by simp [hs]))⟩

end GreedyForest.Execution
