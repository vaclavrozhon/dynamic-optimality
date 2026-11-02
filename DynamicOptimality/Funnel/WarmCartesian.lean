import DynamicOptimality.Funnel.Basic
import ChaCha.MTR

/-!
# The Cartesian tree of the requested keys

The history is written newest occurrence first. Its first key is the root;
the two children recursively retain the smaller and larger keys. Repeated
occurrences of the root disappear from both children. The construction uses
the existing ordinary MTR tree type and contains no cold, unrequested keys.
-/

namespace DynamicOptimality.Funnel.Warm

open ChaCha.MTR.Tree
open ChaCha.MTR

variable {α : Type*} [LinearOrder α]

omit [LinearOrder α] in
theorem length_induction {motive : List α → Prop}
    (step : ∀ history, (∀ smaller, smaller.length < history.length → motive smaller) →
      motive history) (history : List α) : motive history :=
  (measure List.length).wf.induction history step

def cartesian : List α → Tree α
  | [] => .empty
  | x :: rest => .node
      (cartesian (rest.filter (fun y => decide (y < x)))) x
      (cartesian (rest.filter (fun y => decide (x < y))))
termination_by history => history.length
decreasing_by
  all_goals
    simp_wf
    apply Nat.lt_succ_of_le
    calc
      _ ≤ rest.attach.length := List.length_filter_le _ _
      _ = rest.length := by simp

@[simp] theorem cartesian_nil : cartesian ([] : List α) = .empty := by rw [cartesian]

@[simp] theorem cartesian_cons (x : α) (rest : List α) :
    cartesian (x :: rest) = .node
      (cartesian (rest.filter (fun y => decide (y < x)))) x
      (cartesian (rest.filter (fun y => decide (x < y)))) := by rw [cartesian]

theorem mem_cartesian (history : List α) (key : α) :
    key ∈ inorder (cartesian history) ↔ key ∈ history := by
  induction history using length_induction with
  | step history ih =>
    cases history with
    | nil => simp [inorder]
    | cons x rest =>
      have leftLength : (rest.filter (fun y => decide (y < x))).length < (x::rest).length :=
        (List.length_filter_le _ _).trans_lt (by simp)
      have rightLength : (rest.filter (fun y => decide (x < y))).length < (x::rest).length :=
        (List.length_filter_le _ _).trans_lt (by simp)
      rw [cartesian_cons]
      simp only [inorder,List.mem_append,List.mem_singleton,
        ih _ leftLength,ih _ rightLength,List.mem_filter,decide_eq_true_eq,List.mem_cons]
      rcases lt_trichotomy key x with less | same | greater
      · simp [less,ne_of_lt less,not_lt_of_ge less.le]
      · simp [same]
      · simp [greater,ne_of_gt greater,not_lt_of_ge greater.le]

theorem ordered_cartesian (history : List α) : Ordered (cartesian history) := by
  induction history using length_induction with
  | step history ih =>
    cases history with
    | nil => simp [Ordered,inorder]
    | cons x rest =>
      have leftLength : (rest.filter (fun y => decide (y < x))).length < (x::rest).length :=
        (List.length_filter_le _ _).trans_lt (by simp)
      have rightLength : (rest.filter (fun y => decide (x < y))).length < (x::rest).length :=
        (List.length_filter_le _ _).trans_lt (by simp)
      have leftOrdered := ih _ leftLength
      have rightOrdered := ih _ rightLength
      rw [cartesian_cons]
      simp only [Ordered,inorder,List.pairwise_append,List.pairwise_singleton]
      refine ⟨⟨leftOrdered,trivial,?_⟩,rightOrdered,?_⟩
      · intro y hy z hz
        have yx : y < x := of_decide_eq_true
          (List.mem_filter.mp ((mem_cartesian _ _).mp hy)).2
        have same : z = x := List.mem_singleton.mp hz
        simpa only [same] using yx
      · intro y hy z hz
        have xz : x < z := (List.mem_filter.mp ((mem_cartesian _ _).mp hz)).2 |> of_decide_eq_true
        rcases List.mem_append.mp hy with hy | hy
        · have yx : y < x := (List.mem_filter.mp ((mem_cartesian _ _).mp hy)).2 |> of_decide_eq_true
          exact yx.trans xz
        · have same : y = x := List.mem_singleton.mp hy
          simpa only [same] using xz

end DynamicOptimality.Funnel.Warm
