import Greedy.AtomicAccess

/-! Sum identities for the two atomic side schedules and their physical links. -/

namespace Greedy.AtomicAccess

open Splay.Tree Splay.Tree.BST Splay.Rank
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.PlateauBridge
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open GreedyMerge.AccessConsolidation
open GreedyMerge.MappedConsolidation
open scoped BigOperators

theorem indexed_sum {Event : Type*} (events : List Event) (weight : Event → ℤ) :
    (∑ i : Fin events.length, weight (events.get i)) = (events.map weight).sum := by
  induction events with
  | nil => simp
  | cons event rest ih =>
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simpa only [List.get_eq_getElem, Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ,
        List.map_cons, List.sum_cons] using congrArg (fun value => weight event + value) ih

theorem sum_two_sides {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (geometry : AccessTrace.Geometry data source) (weight : ℕ × ℕ → ℤ) :
    (∑ i : Fin data.events.length, weight (eventKeys (data.events.get i))) =
      (∑ i : Fin (schedule data.owner data.left).length,
        weight (AtomOwner p.separator data.gapOwner ((schedule data.owner data.left).get i).1,
          AtomOwner p.separator data.gapOwner ((schedule data.owner data.left).get i).2)) +
      (∑ i : Fin (schedule data.owner data.right).length,
        weight (AtomOwner p.separator data.gapOwner ((schedule data.owner data.right).get i).1,
          AtomOwner p.separator data.gapOwner ((schedule data.owner data.right).get i).2)) := by
  rw [indexed_sum data.events (fun event => weight (eventKeys event)),
    indexed_sum (schedule data.owner data.left) (fun edge => weight
      (AtomOwner p.separator data.gapOwner edge.1, AtomOwner p.separator data.gapOwner edge.2)),
    indexed_sum (schedule data.owner data.right) (fun edge => weight
      (AtomOwner p.separator data.gapOwner edge.1, AtomOwner p.separator data.gapOwner edge.2))]
  have mapped : data.events.map (fun event => weight (eventKeys event)) =
      (mapEvents (AtomOwner p.separator data.gapOwner)
        (schedule data.owner data.left ++ schedule data.owner data.right)).map weight := by
    rw [← physical_keys data source geometry, List.map_map]
    rfl
  rw [mapped]
  simp only [mapEvents, List.map_append, List.map_map, List.sum_append, Function.comp_def]

theorem indexed_toFinset {Event : Type*} [DecidableEq Event] (events : List Event)
    (unique : events.Nodup) (weight : Event → ℤ) :
    (∑ i : Fin events.length, weight (events.get i)) = ∑ event ∈ events.toFinset, weight event := by
  rw [indexed_sum, List.sum_toFinset _ unique]

end Greedy.AtomicAccess
