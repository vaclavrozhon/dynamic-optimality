import AccessSurvivors

/-! Lift the actual Nat-valued schedule to bounded external records.
Endpoint bounds follow from membership in the exact old heap child list;
no additional global injectivity or supplied typed-event certificate is used. -/
namespace GreedyMerge.ActualLinks
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.AccessFrontier

def boundedRecord (n value : ℕ) : External n := ⟨min value (2*n),by omega⟩

def physicalEvent (n : ℕ) (event : ℕ × ℕ) : External n × External n :=
  (boundedRecord n event.1,boundedRecord n event.2)

def physicalEvents (n : ℕ) (events : List (ℕ × ℕ)) : List (External n × External n) :=
  events.map (physicalEvent n)

theorem physicalEvent_keys {n : ℕ} (event : ℕ × ℕ)
    (bounds : event.1 ≤ 2*n ∧ event.2 ≤ 2*n) : eventKeys (physicalEvent n event)=event := by
  rcases event with ⟨winner,loser⟩
  simp only [physicalEvent,eventKeys,boundedRecord,Nat.min_eq_left bounds.1,Nat.min_eq_left bounds.2]

theorem physicalEvents_keys {n : ℕ} (events : List (ℕ × ℕ))
    (bounds : ∀ event ∈ events, event.1 ≤ 2*n ∧ event.2 ≤ 2*n) :
    (physicalEvents n events).map eventKeys=events := by
  simp only [physicalEvents,List.map_map]
  conv_rhs => rw [←List.map_id events]
  apply List.map_congr_left
  intro event member
  exact physicalEvent_keys event (bounds event member)

theorem hasChild_record_bound {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (owner : External n) (child : ℕ)
    (member : HasChild snapshot tree (Nat.le_refl n) 0 owner child) : child ≤ 2*n := by
  obtain ⟨edge,edgeMem,parent,key⟩ := member
  have bound := edge.child.isLt
  omega

theorem actual_run_event_bounds {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (source : External n) (rank : ℕ → ℕ) (events : List (ℕ × ℕ)) (roots finalRoots : List ℕ)
    (run : Run rank events roots finalRoots)
    (actualChildren : ∀ child, HasChild snapshot tree (Nat.le_refl n) 0 source child ↔ child ∈ roots) :
    ∀ event ∈ events, event.1 ≤ 2*n ∧ event.2 ≤ 2*n := by
  intro event member
  have endpoints := run.event_members event member
  exact ⟨hasChild_record_bound snapshot tree source event.1 ((actualChildren _).mpr endpoints.1),
    hasChild_record_bound snapshot tree source event.2 ((actualChildren _).mpr endpoints.2)⟩

/-- The exact actual schedule automatically has a bounded-record version
whose physical keys recover every original winner and loser verbatim. -/
theorem physicalEvents_actual_keys {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (source : External n) (rank : ℕ → ℕ) (events : List (ℕ × ℕ)) (roots finalRoots : List ℕ)
    (run : Run rank events roots finalRoots)
    (actualChildren : ∀ child, HasChild snapshot tree (Nat.le_refl n) 0 source child ↔ child ∈ roots) :
    (physicalEvents n events).map eventKeys=events :=
  physicalEvents_keys events (actual_run_event_bounds snapshot tree source rank events roots finalRoots
    run actualChildren)

end GreedyMerge.ActualLinks

#print axioms GreedyMerge.ActualLinks.physicalEvents_actual_keys
