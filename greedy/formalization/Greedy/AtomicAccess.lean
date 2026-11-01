import Greedy.AccessTrace

/-! Exact correspondence between atomic side schedules and physical links. -/

namespace Greedy.AtomicAccess

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.PlateauBridge
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.MappedConsolidation
open GreedyMerge.AccessConsolidation

theorem physical_keys {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (geometry : AccessTrace.Geometry data source) :
    data.events.map eventKeys = mapEvents (AtomOwner p.separator data.gapOwner)
      (schedule data.owner data.left ++ schedule data.owner data.right) := by
  apply physicalEvents_actual_keys (Snapshot.ofTree comparator) oldTree source comparator.externalDepth _
    (AccessTrace.roots data) (AccessTrace.survivors data)
  · exact run_map (two_sided_run _ data.owner data.left data.right data.projection data.localOwners)
  · exact geometry.children

theorem event_of_atom {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (geometry : AccessTrace.Geometry data source)
    (edge : ℕ × ℕ) (member : edge ∈ schedule data.owner data.left ++ schedule data.owner data.right) :
    ∃ event ∈ data.events, event.1.val = AtomOwner p.separator data.gapOwner edge.1 ∧
      event.2.val = AtomOwner p.separator data.gapOwner edge.2 := by
  have mapped : (AtomOwner p.separator data.gapOwner edge.1, AtomOwner p.separator data.gapOwner edge.2) ∈ data.events.map eventKeys := by
    rw [physical_keys data source geometry]
    exact List.mem_map.mpr ⟨edge, member, rfl⟩
  obtain ⟨event, eventMem, same⟩ := List.mem_map.mp mapped
  exact ⟨event, eventMem, congrArg Prod.fst same, congrArg Prod.snd same⟩

end Greedy.AtomicAccess
