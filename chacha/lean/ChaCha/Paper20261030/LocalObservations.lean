import ChaCha.Paper20261030.AuxiliaryPointer

/-!
# Charged tours of a bounded local record neighborhood

The auxiliary pointer model's service events are used here as observations
of auxiliary record keys, not as requests to the original-key algorithm.
An observation takes place at the actual cursor and costs one. The tour
visits every record in a fixed number of levels and returns to its start.
This supplies explicit navigation for local size/balance metadata access;
it does not yet instrument every branch of the auxiliary algorithms.
-/

namespace ChaCha.Paper20261030.Auxiliary

open ChaCha.MTR ChaCha.MTR.Pointer

variable {α : Type*}

def localKeys : Nat → MTR.Tree α → List α
  | 0,_ => []
  | _ + 1,.empty => []
  | d + 1,.node l k r => k :: (localKeys d l ++ localKeys d r)

theorem localKeys_empty (d : Nat) : localKeys d (.empty : MTR.Tree α) = [] := by cases d <;> rfl

theorem child_tour_left {l r : MTR.Tree α} {k : α} {ancestors : List (Frame α)}
    {xs : List α} {cost : Nat} (hl : l ≠ .empty)
    (h : Trace ⟨l,.left k r :: ancestors⟩ xs ⟨l,.left k r :: ancestors⟩ cost) :
    Trace ⟨.node l k r,ancestors⟩ xs ⟨.node l k r,ancestors⟩ (cost + 2) := by
  cases l with
  | empty => exact False.elim (hl rfl)
  | node a x b =>
    have up := Trace.step (Step.upLeft (.node a x b) r k ancestors) (Trace.nil _)
    simpa only [List.append_nil,Nat.add_assoc] using
      Trace.step (Step.left a b r x k ancestors) (trace_append h up)

theorem child_tour_right {l r : MTR.Tree α} {k : α} {ancestors : List (Frame α)}
    {xs : List α} {cost : Nat} (hr : r ≠ .empty)
    (h : Trace ⟨r,.right l k :: ancestors⟩ xs ⟨r,.right l k :: ancestors⟩ cost) :
    Trace ⟨.node l k r,ancestors⟩ xs ⟨.node l k r,ancestors⟩ (cost + 2) := by
  cases r with
  | empty => exact False.elim (hr rfl)
  | node a x b =>
    have up := Trace.step (Step.upRight l (.node a x b) k ancestors) (Trace.nil _)
    simpa only [List.append_nil,Nat.add_assoc] using
      Trace.step (Step.right l a b k x ancestors) (trace_append h up)

theorem local_observation_tour (depth : Nat) (t : MTR.Tree α) (ancestors : List (Frame α)) :
    ∃ cost, Trace ⟨t,ancestors⟩ (localKeys depth t) ⟨t,ancestors⟩ cost ∧
      cost ≤ 5 * (2 ^ depth - 1) := by
  induction depth generalizing t ancestors with
  | zero => exact ⟨0,Trace.nil _,by simp⟩
  | succ depth ih =>
    cases t with
    | empty => exact ⟨0,Trace.nil _,Nat.zero_le _⟩
    | node l k r =>
      have leftTour : ∃ cost, Trace ⟨.node l k r,ancestors⟩ (localKeys depth l)
          ⟨.node l k r,ancestors⟩ cost ∧ cost ≤ 5 * (2 ^ depth - 1) + 2 := by
        cases l with
        | empty => exact ⟨0,by simpa only [localKeys_empty] using Trace.nil _,Nat.zero_le _⟩
        | node a x b =>
          obtain ⟨cost,trace,hcost⟩ := ih (.node a x b) (.left k r :: ancestors)
          exact ⟨cost + 2,child_tour_left (by simp) trace,by omega⟩
      have rightTour : ∃ cost, Trace ⟨.node l k r,ancestors⟩ (localKeys depth r)
          ⟨.node l k r,ancestors⟩ cost ∧ cost ≤ 5 * (2 ^ depth - 1) + 2 := by
        cases r with
        | empty => exact ⟨0,by simpa only [localKeys_empty] using Trace.nil _,Nat.zero_le _⟩
        | node a x b =>
          obtain ⟨cost,trace,hcost⟩ := ih (.node a x b) (.right l k :: ancestors)
          exact ⟨cost + 2,child_tour_right (by simp) trace,by omega⟩
      obtain ⟨lc,lt,hl⟩ := leftTour
      obtain ⟨rc,rt,hr⟩ := rightTour
      refine ⟨lc + rc + 1,Trace.serve (by rfl) (trace_append lt rt),?_⟩
      have hp : 0 < 2 ^ depth := Nat.two_pow_pos depth
      rw [pow_succ]
      omega

/-- Three levels include a pivot, its children, and its grandchildren.
Every record observation and every adjacent navigation is charged. -/
theorem three_level_tour (t : MTR.Tree α) (ancestors : List (Frame α)) :
    ∃ cost, Trace ⟨t,ancestors⟩ (localKeys 3 t) ⟨t,ancestors⟩ cost ∧ cost ≤ 35 := by
  simpa using local_observation_tour 3 t ancestors

theorem four_level_tour (t : MTR.Tree α) (ancestors : List (Frame α)) :
    ∃ cost, Trace ⟨t,ancestors⟩ (localKeys 4 t) ⟨t,ancestors⟩ cost ∧ cost ≤ 75 := by
  simpa using local_observation_tour 4 t ancestors

end ChaCha.Paper20261030.Auxiliary
