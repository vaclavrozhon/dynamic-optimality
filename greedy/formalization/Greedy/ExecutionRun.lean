import Greedy.ExecutionRotation
import Greedy.ComparisonSchedule

/-!
# A whole actual Greedy execution interleaved with the comparator

The run retains every concrete access schedule and every fresh comparator
macro. Its link count is exactly the geometric algorithm's link count.
The constructor below follows the shared comparison trace and derives
the total instance-birth budget from the local factories.
-/

namespace Greedy.Execution

open Splay.Tree Splay.Tree.BST Splay.Assumptions.NormalForm
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau

inductive Run {n : ℕ} (K : ℤ) : State n → State n → List (Fin n) → Type
  | done (state : State n) : Run K state state []
  | rotate {first last : State n} {after : BST 0 n} {depth : ℕ} {requests : List (Fin n)}
      (rotation : RotationAt depth first.comparator after) (data : RotationData first after rotation K)
      (valid : data.state.Valid) (rest : Run K data.state last requests) : Run K first last requests
  | access {first last : State n} {requests : List (Fin n)}
      (request : Fin n) (root : first.comparator.HasRoot request.val)
      (decomposition : Decomposition first.refined.tree request.val)
      (data : AccessScheduleData first.comparator first.refined.tree (afterRefinement first request).tree decomposition)
      (valid : (afterAccess first request K decomposition data).Valid)
      (rest : Run K (afterAccess first request K decomposition data) last requests) :
      Run K first last (request::requests)

namespace Run

noncomputable def links {n : ℕ} {K : ℤ} {first last : State n} {requests : List (Fin n)} : Run K first last requests → ℕ
  | .done _ => 0
  | .rotate _ _ _ rest => rest.links
  | .access _ _ _ data _ rest => data.events.length + rest.links

noncomputable def rotations {n : ℕ} {K : ℤ} {first last : State n} {requests : List (Fin n)} : Run K first last requests → ℕ
  | .done _ => 0
  | .rotate _ _ _ rest => rest.rotations + 1
  | .access _ _ _ _ _ rest => rest.rotations

noncomputable def births {n : ℕ} {K : ℤ} {first last : State n} {requests : List (Fin n)} : Run K first last requests → ℕ
  | .done _ => 0
  | .rotate _ data _ rest => data.journal.length + rest.births
  | .access (first := first) request _ _ _ _ rest =>
      rootConversionBirths (source request) first.blocks + rest.births

def Bounded {n : ℕ} {K : ℤ} {first last : State n} {requests : List (Fin n)}
    (height : ℕ) : Run K first last requests → Prop
  | .done state => state.comparator.height ≤ height
  | .rotate (first := first) _ _ _ rest => first.comparator.height ≤ height ∧ rest.Bounded height
  | .access (first := first) _ _ _ _ _ rest => first.comparator.height ≤ height ∧ rest.Bounded height

theorem links_eq {n : ℕ} {K : ℤ} {first last : State n} {requests : List (Fin n)}
    (run : Run K first last requests) : run.links = linksFrom first.surface first.time requests := by
  induction run with
  | done => rfl
  | rotate rotation data valid rest ih => exact ih
  | @access first last requests request root decomposition data valid rest ih =>
      have count := actual_access_link_count first.surface first.comparator first.refined.tree
        (afterRefinement first request).tree first.refined.owner first.refined.owners
        (root_minimum _ request root) first.refined.canonical decomposition data
      change data.events.length + rest.links = _
      rw [count, ih]
      rfl

theorem cost_identity {n : ℕ} {K : ℤ} {first last : State n} {requests : List (Fin n)}
    (run : Run K first last requests) :
    2 * costFrom first.surface first.time requests = 2*requests.length + run.links := by
  rw [run.links_eq]
  exact twice_costFrom _ _ _

end Run

theorem execute_plan {n : ℕ} {requests : List (Fin n)} (trace : ComparisonTrace n requests)
    (height : ℕ) (heightBound : ∀ time, (trace.state time).height ≤ height)
    (depthBound : ∀ step, trace.rotationDepth step ≤ 1)
    {start finish : Fin (trace.rotationCount+1)} {served : List (Fin n)} {count : ℕ}
    (plan : ComparisonSchedule.Plan trace start finish served count)
    (state : State n) (K : ℤ) (valid : state.Valid) (comparison : state.comparator = trace.state start) :
    ∃ last, ∃ run : Run K state last served,
      last.Valid ∧ last.comparator = trace.state finish ∧ run.rotations = count ∧
      run.births ≤ 2*served.length+99*count ∧ run.Bounded height ∧ state.next ≤ last.next := by
  induction plan generalizing state with
  | done time =>
      exact ⟨state, .done state, valid, comparison, rfl, by simp [Run.births],
        by simpa only [Run.Bounded, comparison] using heightBound time, le_refl _⟩
  | @rotate step finish served count rest ih =>
      have rotation : RotationAt (trace.rotationDepth step) state.comparator (trace.state step.succ) := by
        rw [comparison]
        exact trace.rotates step
      obtain ⟨data, afterValid, counter, birthBound, _clockBound, _support⟩ :=
        rotation_exists state _ rotation K valid
      obtain ⟨last, tail, lastValid, lastComparator, rotationCount, births, bounded, tailCounter⟩ :=
        ih data.state afterValid rfl
      have localBound : data.journal.length ≤ 99 := by
        have power := Nat.pow_le_pow_left (show trace.rotationDepth step+2 ≤ 3 by have := depthBound step; omega) 2
        norm_num at power
        omega
      refine ⟨last, .rotate rotation data afterValid tail, lastValid, lastComparator, ?_, ?_, ?_, counter.trans tailCounter⟩
      · simpa only [Run.rotations, rotationCount]
      · change data.journal.length + tail.births ≤ _
        omega
      · exact ⟨by simpa only [comparison] using heightBound step.castSucc, bounded⟩
  | @access start finish served count request root rest ih =>
      have rooted : state.comparator.HasRoot request.val := comparison.symm ▸ root
      obtain ⟨decomposition, data, afterValid, _linkCount⟩ := access_exists state request K valid rooted
      obtain ⟨last, tail, lastValid, lastComparator, rotationCount, births, bounded, tailCounter⟩ :=
        ih (afterAccess state request K decomposition data) afterValid comparison
      have headBound := rootConversionBirths_le_two (source request) state.blocks
      refine ⟨last, .access request rooted decomposition data afterValid tail, lastValid, lastComparator,
        rotationCount, ?_, ?_, ?_⟩
      · change rootConversionBirths (source request) state.blocks + tail.births ≤ _
        simp only [List.length_cons]
        omega
      · exact ⟨by simpa only [comparison] using heightBound start, bounded⟩
      · change state.next+2*(2*n+1) ≤ last.next at tailCounter
        omega

/-- The common comparison trace yields an actual complete Greedy run,
with no supplied global execution or birth budget. -/
theorem exists_shared_run {n : ℕ} (tree : BST 0 n) (requests : List (Fin n))
    (trace : ComparisonTrace n requests) (height : ℕ)
    (heightBound : ∀ time, (trace.state time).height ≤ height)
    (depthBound : ∀ step, trace.rotationDepth step ≤ 1) (K : ℤ) :
    ∃ last, ∃ run : Run K (initial tree (trace.state 0) K) last requests,
      last.Valid ∧ last.comparator = trace.state (Fin.last trace.rotationCount) ∧
      run.rotations = trace.rotationCount ∧ run.births ≤ 2*requests.length+99*trace.rotationCount ∧
      run.Bounded height ∧ 2*cost tree requests = 2*requests.length+run.links := by
  obtain ⟨plan⟩ := ComparisonSchedule.exists_plan trace
  obtain ⟨last, run, valid, comparator, rotations, births, bounded, _counter⟩ :=
    execute_plan trace height heightBound depthBound plan (initial tree (trace.state 0) K) K
      (initial_valid tree (trace.state 0) K) rfl
  exact ⟨last, run, valid, comparator, rotations, births, bounded, run.cost_identity⟩

end Greedy.Execution
