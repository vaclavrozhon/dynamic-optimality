import Splay.Lazy.ComparisonTrace
import Splay.Lazy.SplaySequenceTrace

namespace Splay.Assumptions.NormalForm.ComparisonTrace

open Splay.Tree.BST

private def expandRuns {κ α : Type*} :
    List (κ × List α) → List (κ × α)
  | [] => []
  | (key, values) :: rest =>
      values.map (fun value => (key, value)) ++ expandRuns rest

private def groupRuns {κ α : Type*} [DecidableEq κ] :
    List (κ × α) → List (κ × List α)
  | [] => []
  | (key, value) :: rest =>
      match groupRuns rest with
      | [] => [(key, [value])]
      | (nextKey, values) :: groups =>
          if key = nextKey then
            (nextKey, value :: values) :: groups
          else
            (key, [value]) :: (nextKey, values) :: groups

private theorem expandRuns_groupRuns {κ α : Type*} [DecidableEq κ]
    (entries : List (κ × α)) :
    expandRuns (groupRuns entries) = entries := by
  induction entries with
  | nil =>
      rfl
  | cons entry entries ih =>
      obtain ⟨key, value⟩ := entry
      rw [groupRuns]
      cases grouped_eq : groupRuns entries with
      | nil =>
          have entries_nil : entries = [] := by
            have := ih
            rw [grouped_eq] at this
            simpa [expandRuns] using this.symm
          simp [entries_nil, expandRuns]
      | cons group groups =>
          obtain ⟨nextKey, values⟩ := group
          by_cases same : key = nextKey
          · subst nextKey
            simpa [grouped_eq, expandRuns] using ih
          · simp only [same, ↓reduceIte, expandRuns, List.map_cons,
              List.map_nil, List.singleton_append]
            simpa [grouped_eq, expandRuns] using ih

private theorem expandRuns_flatten_values {κ α : Type*}
    (groups : List (κ × List α)) :
    (expandRuns groups).map Prod.snd =
      groups.flatMap Prod.snd := by
  induction groups with
  | nil =>
      rfl
  | cons group groups ih =>
      obtain ⟨key, values⟩ := group
      simp [expandRuns, ih]

private theorem groupRuns_flatten_values {κ α : Type*} [DecidableEq κ]
    (entries : List (κ × α)) :
    (groupRuns entries).flatMap Prod.snd =
      entries.map Prod.snd := by
  rw [← expandRuns_flatten_values, expandRuns_groupRuns]

private theorem mem_expandRuns_of_mem {κ α : Type*}
    (groups : List (κ × List α))
    {group : κ × List α} (inGroups : group ∈ groups)
    {value : α} (inValues : value ∈ group.2) :
    (group.1, value) ∈ expandRuns groups := by
  induction groups with
  | nil =>
      simp at inGroups
  | cons head tail ih =>
      simp only [List.mem_cons] at inGroups
      rcases inGroups with rfl | inTail
      · simp [expandRuns, inValues]
      · exact List.mem_append_right _
          (ih inTail)

private theorem groupRuns_all_same_key {κ α : Type*} [DecidableEq κ]
    (entries : List (κ × α)) :
    ∀ group ∈ groupRuns entries,
      ∀ value ∈ group.2, (group.1, value) ∈ entries := by
  intro group inGroups value inValues
  have inExpanded : (group.1, value) ∈ expandRuns (groupRuns entries) :=
    mem_expandRuns_of_mem (groupRuns entries) inGroups inValues
  simpa [expandRuns_groupRuns] using inExpanded

private theorem groupRuns_values_nonempty {κ α : Type*} [DecidableEq κ]
    (entries : List (κ × α)) :
    ∀ group ∈ groupRuns entries, group.2 ≠ [] := by
  induction entries with
  | nil =>
      simp [groupRuns]
  | cons entry entries ih =>
      obtain ⟨key, value⟩ := entry
      simp only [groupRuns]
      cases grouped_eq : groupRuns entries with
      | nil =>
          simp
      | cons head tail =>
          obtain ⟨nextKey, values⟩ := head
          by_cases same : key = nextKey
          · simp only [same, ↓reduceIte, List.mem_cons]
            intro group inGroups
            rcases inGroups with rfl | inTail
            · simp
            · exact ih group (by
                rw [grouped_eq]
                exact List.mem_cons_of_mem _ inTail)
          · simp only [same, ↓reduceIte, List.mem_cons]
            intro group inGroups
            rcases inGroups with rfl | inRest
            · simp
            · exact ih group (by
                rw [grouped_eq]
                simpa only [List.mem_cons] using inRest)

private theorem groupRuns_keys_pairwise {κ α : Type*}
    [LinearOrder κ] [DecidableEq κ]
    (entries : List (κ × α))
    (ordered : entries.Pairwise (fun left right => left.1 ≤ right.1)) :
    (groupRuns entries).Pairwise
      (fun left right => left.1 < right.1) := by
  induction entries with
  | nil =>
      exact .nil
  | cons entry entries ih =>
      obtain ⟨key, value⟩ := entry
      rw [List.pairwise_cons] at ordered
      rw [groupRuns]
      cases grouped_eq : groupRuns entries with
      | nil =>
          simp
      | cons group groups =>
          obtain ⟨nextKey, values⟩ := group
          have tailOrdered := ih ordered.2
          rw [grouped_eq] at tailOrdered
          by_cases same : key = nextKey
          · subst nextKey
            simpa using tailOrdered
          · have key_le_next : key ≤ nextKey := by
              have nonempty_values : values ≠ [] :=
                groupRuns_values_nonempty entries
                  (nextKey, values) (by simp [grouped_eq])
              obtain ⟨first, first_mem⟩ :=
                List.exists_mem_of_ne_nil values nonempty_values
              have pair_mem :
                  (nextKey, first) ∈ entries :=
                groupRuns_all_same_key entries
                  (nextKey, values) (by simp [grouped_eq])
                  first first_mem
              exact ordered.1 (nextKey, first) pair_mem
            have key_lt_next : key < nextKey :=
              lt_of_le_of_ne key_le_next same
            simp only [same, ↓reduceIte]
            rw [List.pairwise_cons]
            refine ⟨?_, tailOrdered⟩
            intro later inLater
            simp only [List.mem_cons] at inLater
            rcases inLater with head_eq | inGroups
            · simpa [head_eq] using key_lt_next
            · rcases later with ⟨laterKey, laterValues⟩
              have next_le_later :
                  nextKey < laterKey := by
                rw [List.pairwise_cons] at tailOrdered
                exact tailOrdered.1
                  (laterKey, laterValues) inGroups
              exact key_lt_next.trans next_le_later

/-- One maximal chronological run of requests served at a common state. -/
structure RequestGroup {n : ℕ} {accesses : List (Fin n)}
    (trace : ComparisonTrace n accesses) where
  time : Fin (trace.rotationCount + 1)
  requestIndices : List (Fin accesses.length)
  requestIndices_nonempty : requestIndices ≠ []
  servedAt_eq :
    ∀ request ∈ requestIndices, trace.servedAt request = time

namespace RequestGroup

/-- The actual access keys in a chronological request run. -/
def requests {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses}
    (group : RequestGroup trace) : List (Fin n) :=
  group.requestIndices.map accesses.get

/-- Every request in a group is served at the root of its common state. -/
theorem serves {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses}
    (group : RequestGroup trace)
    {request : Fin n} (member : request ∈ group.requests) :
    (trace.state group.time).HasRoot request.val := by
  simp only [requests, List.mem_map] at member
  obtain ⟨index, inGroup, rfl⟩ := member
  rw [← group.servedAt_eq index inGroup]
  exact trace.serves index

end RequestGroup

private def timedRequestIndices {n : ℕ} {accesses : List (Fin n)}
    (trace : ComparisonTrace n accesses) :
    List (Fin (trace.rotationCount + 1) × Fin accesses.length) :=
  List.ofFn (fun request => (trace.servedAt request, request))

private def rawRequestGroups {n : ℕ} {accesses : List (Fin n)}
    (trace : ComparisonTrace n accesses) :
    List
      (Fin (trace.rotationCount + 1) ×
        List (Fin accesses.length)) :=
  groupRuns (timedRequestIndices trace)

private theorem rawRequestGroups_same_time {n : ℕ}
    {accesses : List (Fin n)}
    (trace : ComparisonTrace n accesses) :
    ∀ group ∈ rawRequestGroups trace,
      ∀ request ∈ group.2, trace.servedAt request = group.1 := by
  intro group inGroups request inGroup
  have timedMem :
      (group.1, request) ∈ timedRequestIndices trace :=
    groupRuns_all_same_key (timedRequestIndices trace)
      group (by simpa [rawRequestGroups] using inGroups)
      request inGroup
  simp only [timedRequestIndices, List.mem_ofFn] at timedMem
  obtain ⟨index, equal⟩ := timedMem
  have time_eq : trace.servedAt index = group.1 :=
    congrArg Prod.fst equal
  have request_eq : index = request :=
    congrArg Prod.snd equal
  simpa [request_eq] using time_eq

private noncomputable def requestGroups {n : ℕ}
    {accesses : List (Fin n)}
    (trace : ComparisonTrace n accesses) :
    List (RequestGroup trace) :=
  (rawRequestGroups trace).attach.map fun group =>
    { time := group.val.1
      requestIndices := group.val.2
      requestIndices_nonempty :=
        groupRuns_values_nonempty (timedRequestIndices trace)
          group.val (by
            simpa [rawRequestGroups] using group.property)
      servedAt_eq :=
        rawRequestGroups_same_time trace group.val group.property }

private theorem requestGroups_flatten_indices {n : ℕ}
    {accesses : List (Fin n)}
    (trace : ComparisonTrace n accesses) :
    (requestGroups trace).flatMap RequestGroup.requestIndices =
      List.ofFn (fun request : Fin accesses.length => request) := by
  rw [requestGroups]
  rw [List.flatMap_map]
  change
    List.flatten
        ((rawRequestGroups trace).attach.map
          (fun group => group.val.2)) =
      List.ofFn (fun request : Fin accesses.length => request)
  rw [List.attach_map_val]
  change
    (rawRequestGroups trace).flatMap Prod.snd =
      List.ofFn (fun request : Fin accesses.length => request)
  rw [rawRequestGroups, groupRuns_flatten_values,
    timedRequestIndices, List.map_ofFn]
  rfl

private theorem requestGroups_times_pairwise {n : ℕ}
    {accesses : List (Fin n)}
    (trace : ComparisonTrace n accesses) :
    (requestGroups trace).Pairwise
      (fun left right => left.time < right.time) := by
  have timedOrdered :
      (timedRequestIndices trace).Pairwise
        (fun left right => left.1 ≤ right.1) := by
    rw [timedRequestIndices, List.pairwise_ofFn]
    intro i j hij
    exact trace.servedInOrder (Fin.le_of_lt hij)
  have rawOrdered :=
    groupRuns_keys_pairwise
      (timedRequestIndices trace) timedOrdered
  have rawTimes :
      ((rawRequestGroups trace).map Prod.fst).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    simpa [rawRequestGroups] using rawOrdered
  have times_eq :
      (requestGroups trace).map RequestGroup.time =
        (rawRequestGroups trace).map Prod.fst := by
    rw [requestGroups, List.map_map]
    change
      (rawRequestGroups trace).attach.map
          (fun group => group.val.1) =
        (rawRequestGroups trace).map Prod.fst
    exact List.attach_map_val
  rw [← List.pairwise_map, times_eq]
  exact rawTimes

/--
A purely structural chronological interleaving of splay accesses and
comparison-tree rotations.

Before each same-time request group, the comparison tree follows the exact
contiguous segment of `trace.rotates`; the group itself is executed as one
dependent `SplaySequence`.  The final constructor consumes the remaining
comparison rotations through the final trace state.
-/
inductive Schedule {n : ℕ} {accesses : List (Fin n)}
    (trace : ComparisonTrace n accesses) :
    List (RequestGroup trace) →
      Fin (trace.rotationCount + 1) →
      Tree.BST 0 n → Tree.BST 0 n → Type
  | finish {time : Fin (trace.rotationCount + 1)}
      (tree : Tree.BST 0 n)
      (comparison :
        RotationExecution
          (trace.rotationCount - time.val)
          (trace.state time) trace.finalTree) :
      Schedule trace [] time tree tree
  | next {group : RequestGroup trace}
      {groups : List (RequestGroup trace)}
      {time : Fin (trace.rotationCount + 1)}
      {before middle after : Tree.BST 0 n}
      (ordered : time ≤ group.time)
      (comparison :
        RotationExecution
          (group.time.val - time.val)
          (trace.state time) (trace.state group.time))
      (splay :
        SplaySequence group.requests before middle)
      (tail : Schedule trace groups group.time middle after) :
      Schedule trace (group :: groups) time before after

namespace Schedule

/-- Requests served by the schedule, in chronological group order. -/
def servedRequests {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : Tree.BST 0 n}
    (_schedule : Schedule trace groups time before after) :
    List (Fin n) :=
  groups.flatMap RequestGroup.requests

/-- The exact number of comparison-tree rotations consumed by a schedule. -/
def comparisonRotationCount {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : Tree.BST 0 n} :
    Schedule trace groups time before after → ℕ
  | .finish (time := finishTime) _ _ =>
      trace.rotationCount - finishTime.val
  | .next (group := group) (time := startTime) _ _ _ tail =>
      group.time.val - startTime.val +
        tail.comparisonRotationCount

/-- A schedule consumes exactly the suffix of comparison rotations. -/
theorem comparisonRotationCount_eq {n : ℕ}
    {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : Tree.BST 0 n}
    (schedule : Schedule trace groups time before after) :
    schedule.comparisonRotationCount =
      trace.rotationCount - time.val := by
  induction schedule with
  | finish =>
      rfl
  | @next group groups time before middle after
      ordered comparison splay tail ih =>
      simp only [comparisonRotationCount, ih]
      have group_le :
          group.time.val ≤ trace.rotationCount := by
        omega
      have time_le : time.val ≤ group.time.val :=
        ordered
      omega

end Schedule

private theorem exists_schedule_from_groups {n : ℕ}
    {accesses : List (Fin n)}
    (trace : ComparisonTrace n accesses)
    (groups : List (RequestGroup trace))
    (ordered :
      groups.Pairwise (fun left right => left.time ≤ right.time))
    (start : Fin (trace.rotationCount + 1))
    (start_le :
      ∀ group ∈ groups, start ≤ group.time)
    (initialSplayTree : Tree.BST 0 n) :
    ∃ finalSplayTree : Tree.BST 0 n,
      Nonempty
        (Schedule trace groups start
          initialSplayTree finalSplayTree) := by
  induction groups generalizing start initialSplayTree with
  | nil =>
      refine ⟨initialSplayTree, ⟨.finish initialSplayTree ?_⟩⟩
      exact trace.toRotationExecution_between start
        (Fin.last trace.rotationCount) (Fin.le_last start)
  | cons group groups ih =>
      rw [List.pairwise_cons] at ordered
      have start_group : start ≤ group.time :=
        start_le group (by simp)
      obtain ⟨middle, ⟨splay⟩⟩ :=
        SplaySequence.exists_sequence initialSplayTree group.requests
      have group_le_tail :
          ∀ later ∈ groups, group.time ≤ later.time :=
        ordered.1
      obtain ⟨final, ⟨tail⟩⟩ :=
        ih ordered.2 group.time group_le_tail middle
      exact
        ⟨final, ⟨.next start_group
          (trace.toRotationExecution_between
            start group.time start_group)
          splay tail⟩⟩

/--
For every comparison trace and initial splay tree there is a chronological
structural schedule. Requests sharing a `servedAt` state form one group, the
flattened groups are exactly the original access list, every grouped request
is rooted
in its comparison state, and the schedule consumes exactly the original
number of comparison rotations.
-/
theorem exists_normalFormSchedule {n : ℕ}
    {accesses : List (Fin n)}
    (trace : ComparisonTrace n accesses)
    (initialSplayTree : Tree.BST 0 n) :
    ∃ (groups : List (RequestGroup trace))
        (finalSplayTree : Tree.BST 0 n)
        (schedule :
          Schedule trace groups 0
            initialSplayTree finalSplayTree),
      groups.flatMap RequestGroup.requests = accesses ∧
        groups.Pairwise
          (fun left right => left.time < right.time) ∧
        (∀ group ∈ groups,
          ∀ request ∈ group.requests,
            (trace.state group.time).HasRoot request.val) ∧
        schedule.comparisonRotationCount =
          trace.rotationCount := by
  let groups := requestGroups trace
  have orderedStrict := requestGroups_times_pairwise trace
  have ordered :
      groups.Pairwise
        (fun left right => left.time ≤ right.time) :=
    orderedStrict.imp (fun strict => Fin.le_of_lt strict)
  have start_le :
      ∀ group ∈ groups, (0 : Fin (trace.rotationCount + 1)) ≤ group.time := by
    intro group inGroups
    exact Fin.zero_le group.time
  obtain ⟨final, ⟨schedule⟩⟩ :=
    exists_schedule_from_groups trace groups ordered
      0 start_le initialSplayTree
  refine ⟨groups, final, schedule, ?_, orderedStrict, ?_, ?_⟩
  · change
      (requestGroups trace).flatMap
          (fun group =>
            group.requestIndices.map accesses.get) =
        accesses
    rw [← List.map_flatMap]
    rw [requestGroups_flatten_indices]
    rw [List.map_ofFn]
    exact List.ofFn_get accesses
  · intro group inGroups request inRequests
    exact group.serves inRequests
  · simpa using schedule.comparisonRotationCount_eq

end Splay.Assumptions.NormalForm.ComparisonTrace
