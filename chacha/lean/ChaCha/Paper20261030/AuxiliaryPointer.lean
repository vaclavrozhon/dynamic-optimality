import ChaCha.Paper20261030.AuxiliaryBalanced
import ChaCha.PointerModel

/-!
# Actual pointer traces for balanced auxiliary searches

Forgetting cached sizes and values turns a library auxiliary tree into an
ordinary key tree. Successful search is realized by adjacent child/parent
moves and one service at the requested key. It returns to its initial root,
even when that root lies inside a larger tree.
-/

namespace ChaCha.Paper20261030.Auxiliary

open Std Std.DTreeMap.Internal
open ChaCha.MTR
open ChaCha.MTR.Pointer

variable {α : Type*} {β : α → Type*}

theorem trace_append {c d e : Cursor α} {xs ys : List α} {a b : Nat}
    (h : Trace c xs d a) (g : Trace d ys e b) : Trace c (xs ++ ys) e (a + b) := by
  induction h with
  | nil => simpa using g
  | step move rest ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Trace.step move (ih g)
  | serve at_key rest ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Trace.serve at_key (ih g)

def erase : Impl α β → MTR.Tree α
  | .leaf => .empty
  | .inner _ k _ l r => .node (erase l) k (erase r)

/-- Exact search cost includes the return path and the service operation. -/
theorem search_pointer_trace [Ord α] [LawfulEqOrd α] (x : α) (t : Impl α β)
    (found : searchResult x t = true) (ancestors : List (Frame α)) :
    ∃ cost, Trace ⟨erase t, ancestors⟩ [x] ⟨erase t, ancestors⟩ cost ∧
      cost + 1 = 2 * searchVisits x t := by
  induction t generalizing ancestors with
  | leaf => simp [searchResult] at found
  | inner sz k v l r ihl ihr =>
    cases hc : compare x k with
    | eq =>
      have hx : x = k := compare_eq_iff_eq.mp hc
      subst x
      refine ⟨1, Trace.serve (by rfl) (Trace.nil _), ?_⟩
      simp [searchVisits,hc]
    | lt =>
      have hf : searchResult x l = true := by simpa [searchResult,hc] using found
      obtain ⟨cost,trace,hcost⟩ := ihl hf (.left k (erase r) :: ancestors)
      cases l with
      | leaf => simp [searchResult] at hf
      | inner sl kl vl ll lr =>
        have back := Trace.step (Step.upLeft (erase (.inner sl kl vl ll lr)) (erase r) k ancestors)
          (Trace.nil _)
        have joined := trace_append trace back
        refine ⟨cost + 2, ?_, ?_⟩
        · simpa only [erase,List.append_nil,Nat.add_assoc] using
            Trace.step (Step.left (erase ll) (erase lr) (erase r) kl k ancestors) joined
        · simp only [searchVisits,hc] at hcost ⊢
          omega
    | gt =>
      have hf : searchResult x r = true := by simpa [searchResult,hc] using found
      obtain ⟨cost,trace,hcost⟩ := ihr hf (.right (erase l) k :: ancestors)
      cases r with
      | leaf => simp [searchResult] at hf
      | inner sr kr vr rl rr =>
        have back := Trace.step (Step.upRight (erase l) (erase (.inner sr kr vr rl rr)) k ancestors)
          (Trace.nil _)
        have joined := trace_append trace back
        refine ⟨cost + 2, ?_, ?_⟩
        · simpa only [erase,List.append_nil,Nat.add_assoc] using
            Trace.step (Step.right (erase l) (erase rl) (erase rr) k kr ancestors) joined
        · simp only [searchVisits,hc] at hcost ⊢
          omega

/-- The actual successful library search has an ordinary BST execution
with logarithmic cost, including returning to its root. -/
theorem search_pointer_log [Ord α] [LawfulEqOrd α] (x : α) {t : Impl α β}
    (balanced : t.Balanced) (found : t.contains x = true) :
    ∃ cost, Access x (erase t) (erase t) cost ∧
      cost + 1 ≤ 6 * Nat.clog 2 (t.size + 1) := by
  have hf : searchResult x t = true := (searchResult_eq_contains x t).trans found
  obtain ⟨cost,trace,hcost⟩ := search_pointer_trace x t hf []
  refine ⟨cost, ⟨Cursor.atRoot (erase t), rfl, trace⟩, ?_⟩
  have hv := searchVisits_log x balanced
  omega

end ChaCha.Paper20261030.Auxiliary
