import CutGeometry
import BlockDepartures

namespace GreedyForest.Execution

open scoped BigOperators

/-- Boundary nondrops project to strict rises on the two endpoint
search paths, plus constant exceptional harmful/augmented edge slots.
Five exception slots leave slack relative to the candidate's sharper
count. The source-block lifetime is proved separately by deletions. -/
structure BoundaryPhaseGeometry (k count : ℕ) where
  left : CutTree
  right : CutTree
  leftOrdered : CutOrdered left
  rightOrdered : CutOrdered right
  leftLabels : LabelBounded (k:ℤ) 1 left
  rightLabels : LabelBounded (k:ℤ) 1 right
  project : Fin count → Sum (Fin (badCutCount left).toNat)
    (Sum (Fin (badCutCount right).toNat) (Fin 5))
  injective : Function.Injective project

theorem BoundaryPhaseGeometry.bound {k count : ℕ}
    (h : BoundaryPhaseGeometry k count) (hk : 1 ≤ k) : count ≤ 2*k+3 := by
  have hproj := Fintype.card_le_of_injective h.project h.injective
  have hc : count ≤ (badCutCount h.left).toNat + (badCutCount h.right).toNat + 5 := by
    simpa [add_assoc] using hproj
  have hl := badCutCount_le_levels (k:ℤ) 1 h.left (by exact_mod_cast hk)
    h.leftOrdered h.leftLabels
  have hr := badCutCount_le_levels (k:ℤ) 1 h.right (by exact_mod_cast hk)
    h.rightOrdered h.rightLabels
  have hln : (badCutCount h.left).toNat ≤ k-1 := by omega
  have hrn : (badCutCount h.right).toNat ≤ k-1 := by omega
  omega

structure BoundaryDepartureLifetime (stages k : ℕ) (count : Fin stages → ℕ) where
  initial : Finset ℕ
  step : Fin stages → DepartureStep ℕ
  census : ∀ p, (step p).charged.card = count p
  transitions : DepartureTransitions initial (List.ofFn step)
  geometry : ∀ p, BoundaryPhaseGeometry k (count p)

theorem BoundaryDepartureLifetime.bound {stages k : ℕ} {count : Fin stages → ℕ}
    (h : BoundaryDepartureLifetime stages k count) (hk : 1 ≤ k) :
    (∑ p, count p) ≤ 2*k+4 := by
  have hc : ∀ step ∈ List.ofFn h.step, step.charged.card ≤ 2*k+3 := by
    intro step hs
    obtain ⟨p, hp⟩ := List.mem_ofFn.mp hs
    subst step
    rw [h.census p]
    exact (h.geometry p).bound hk
  have hv := departureTransitions_to_valid (2*k+3) h.initial
    (List.ofFn h.step) h.transitions hc
  have hb := departure_activity_le_capacity (2*k+3) h.initial (List.ofFn h.step) hv
  rw [departureActivity_ofFn] at hb
  simpa [h.census, add_assoc] using hb

structure BoundaryEventLifetime (Record Event : Type*) [DecidableEq Record]
    (stages k : ℕ) (events : Fin stages → Finset Event) (record : Event → Record)
    extends EventDepartureHistory Record Event stages events record where
  geometry : ∀ p, BoundaryPhaseGeometry k (events p).card

theorem BoundaryEventLifetime.bound {Record Event : Type*} [DecidableEq Record]
    {stages k : ℕ} {events : Fin stages → Finset Event} {record : Event → Record}
    (h : BoundaryEventLifetime Record Event stages k events record) (hk : 1 ≤ k) :
    (∑ p, (events p).card) ≤ 2*k+4 := by
  have hphase : ∀ p, (events p).card ≤ 2*k+3 := fun p => (h.geometry p).bound hk
  simpa [add_assoc] using h.toEventDepartureHistory.bound hphase

end GreedyForest.Execution
