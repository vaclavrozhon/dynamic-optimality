import Splay.Lazy.NormalFormSchedule

/-!
# A chronological instruction stream for a shared comparison trace

Rotation instructions retain their exact indices in `ComparisonTrace`.
This preserves both height and rotation-depth bounds when the Greedy
execution is composed. Access instructions carry the actual root proof.
Repeated requests served at one comparison state require no rotation.
-/

namespace Greedy.ComparisonSchedule

open Splay.Assumptions.NormalForm
open Splay.Assumptions.NormalForm.ComparisonTrace

inductive Plan {n : ℕ} {requests : List (Fin n)} (trace : ComparisonTrace n requests) :
    Fin (trace.rotationCount+1) → Fin (trace.rotationCount+1) → List (Fin n) → ℕ → Type
  | done (time : Fin (trace.rotationCount+1)) : Plan trace time time [] 0
  | rotate {step : Fin trace.rotationCount} {finish : Fin (trace.rotationCount+1)}
      {served : List (Fin n)} {count : ℕ}
      (rest : Plan trace step.succ finish served count) :
      Plan trace step.castSucc finish served (count+1)
  | access {time finish : Fin (trace.rotationCount+1)} {served : List (Fin n)} {count : ℕ}
      (request : Fin n) (root : (trace.state time).HasRoot request.val)
      (rest : Plan trace time finish served count) :
      Plan trace time finish (request::served) count

theorem prepend_rotations {n : ℕ} {requests : List (Fin n)} (trace : ComparisonTrace n requests)
    (start steps : ℕ) (within : start+steps ≤ trace.rotationCount)
    (finish : Fin (trace.rotationCount+1)) (served : List (Fin n)) (count : ℕ)
    (tail : Plan trace ⟨start+steps, by omega⟩ finish served count) :
    Nonempty (Plan trace ⟨start, by omega⟩ finish served (steps+count)) := by
  induction steps generalizing start with
  | zero => simpa only [Nat.add_zero, Nat.zero_add] using (show Nonempty _ from ⟨tail⟩)
  | succ steps ih =>
      have endEq : (start+1)+steps = start+(steps+1) := by omega
      have tail' : Plan trace ⟨(start+1)+steps, by omega⟩ finish served count := by
        simpa only [endEq] using tail
      obtain ⟨rest⟩ := ih (start+1) (by omega) tail'
      let step : Fin trace.rotationCount := ⟨start, by omega⟩
      have result : Plan trace step.castSucc finish served ((steps+count)+1) := .rotate rest
      convert (show Nonempty _ from ⟨result⟩) using 1 <;> congr 1 <;> omega

theorem prepend_requests {n : ℕ} {requests : List (Fin n)} (trace : ComparisonTrace n requests)
    (time finish : Fin (trace.rotationCount+1)) (first rest : List (Fin n)) (count : ℕ)
    (rooted : ∀ request ∈ first, (trace.state time).HasRoot request.val)
    (tail : Plan trace time finish rest count) : Nonempty (Plan trace time finish (first++rest) count) := by
  induction first with
  | nil => exact ⟨tail⟩
  | cons request remaining ih =>
      obtain ⟨after⟩ := ih (fun req member => rooted req (List.mem_cons_of_mem _ member))
      exact ⟨.access request (rooted request (List.mem_cons_self)) after⟩

theorem groups_plan {n : ℕ} {requests : List (Fin n)} (trace : ComparisonTrace n requests)
    (groups : List (RequestGroup trace))
    (ordered : groups.Pairwise (fun first second => first.time ≤ second.time))
    (start : Fin (trace.rotationCount+1)) (before : ∀ group ∈ groups, start ≤ group.time) :
    Nonempty (Plan trace start (Fin.last trace.rotationCount) (groups.flatMap RequestGroup.requests)
      (trace.rotationCount-start.val)) := by
  induction groups generalizing start with
  | nil =>
      have endEq : start.val+(trace.rotationCount-start.val) = trace.rotationCount := by omega
      have tail : Plan trace ⟨start.val+(trace.rotationCount-start.val), by omega⟩
          (Fin.last trace.rotationCount) [] 0 := by
        simpa only [endEq, Fin.last] using Plan.done (trace := trace) (Fin.last trace.rotationCount)
      have result := prepend_rotations trace start.val (trace.rotationCount-start.val) (by omega)
        (Fin.last trace.rotationCount) [] 0 tail
      simpa only [Nat.add_zero, List.flatMap_nil, Fin.eta] using result
  | cons group groups ih =>
      obtain ⟨later, tailOrdered⟩ := List.pairwise_cons.mp ordered
      obtain ⟨tail⟩ := ih tailOrdered group.time later
      obtain ⟨afterRequests⟩ := prepend_requests trace group.time (Fin.last trace.rotationCount)
        group.requests (groups.flatMap RequestGroup.requests) _ (fun _ member => group.serves member) tail
      have startLe : start.val ≤ group.time.val := before group (List.mem_cons_self)
      have endEq : start.val + (group.time.val-start.val) = group.time.val := by omega
      have afterRequests' : Plan trace ⟨start.val+(group.time.val-start.val), by omega⟩
          (Fin.last trace.rotationCount) (group.requests++groups.flatMap RequestGroup.requests)
          (trace.rotationCount-group.time.val) := by
        simpa only [endEq, Fin.eta] using afterRequests
      have result := prepend_rotations trace start.val (group.time.val-start.val) (by omega)
        (Fin.last trace.rotationCount) _ _ afterRequests'
      have countEq : group.time.val-start.val + (trace.rotationCount-group.time.val) =
          trace.rotationCount-start.val := by omega
      simpa only [countEq, Fin.eta, List.flatMap_cons] using result

theorem exists_plan {n : ℕ} {requests : List (Fin n)} (trace : ComparisonTrace n requests) :
    Nonempty (Plan trace 0 (Fin.last trace.rotationCount) requests trace.rotationCount) := by
  obtain ⟨groups, _last, _schedule, serves, ordered, _rooted, _count⟩ :=
    trace.exists_normalFormSchedule (trace.state 0)
  have result := groups_plan trace groups (ordered.imp (fun h => le_of_lt h)) 0
    (fun _ _ => Fin.zero_le _)
  simpa only [serves, Fin.val_zero, Nat.sub_zero] using result

end Greedy.ComparisonSchedule
