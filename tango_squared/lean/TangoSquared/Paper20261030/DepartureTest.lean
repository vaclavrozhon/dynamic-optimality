import TangoSquared.Paper20261030.DepartureNeighbors
import TangoSquared.Paper20261030.DepthPreferences

/-!
# A unique local test for the first wrong preferred edge

A path record is an exit when its reference interval contains the request
and its preference disagrees with the request's side of its separator.
At most one path record passes this test. No record passes when the
request is already the preferred endpoint. Both statements use the
actual interval and preference fields, with no auxiliary-root header.
-/

namespace TangoSquared.Paper20261030.SeparatorPath

open PreferredProjection

def Exit (d : Nat) (e : Entry) : Prop :=
  e.2.1.lo ≤ d ∧ d ≤ e.2.1.hi ∧ e.2.2 ≠ decide (e.2.1.cut < d)

instance (d : Nat) (e : Entry) : Decidable (Exit d e) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem exit_left_preference (d : Nat) (s : DepthSplit) (h : Exit d ⟨s.cut,(s,false)⟩) : s.cut < d := by
  by_contra hn
  exact h.2.2 (by simp only [decide_eq_false hn])

theorem exit_right_preference (d : Nat) (s : DepthSplit) (h : Exit d ⟨s.cut,(s,true)⟩) : d ≤ s.cut := by
  by_contra hn
  have ht : s.cut < d := by omega
  exact h.2.2 (by simp only [decide_eq_true ht])

theorem exit_unique {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool) (d : Nat)
    {e f : Entry} (he : e ∈ word reference p) (hf : f ∈ word reference p)
    (ee : Exit d e) (ef : Exit d f) : e = f := by
  induction reference with
  | leaf => simp [word] at he
  | @node a b cut ha hb l r ihl ihr =>
    cases hp : p ⟨a,cut,b⟩
    · simp only [word,hp,Bool.false_eq_true,if_false,List.mem_append,List.mem_singleton] at he hf
      rcases he with he | rfl <;> rcases hf with hf | rfl
      · exact ihl he hf
      · have hb := l.node_bounds (mem_word l p he).1
        have hd := exit_left_preference d ⟨a,cut,b⟩ ef
        have hehi := ee.2.1
        simp only at hd
        omega
      · have hb := l.node_bounds (mem_word l p hf).1
        have hd := exit_left_preference d ⟨a,cut,b⟩ ee
        have hfhi := ef.2.1
        simp only at hd
        omega
      · rfl
    · simp only [word,hp,if_true,List.mem_cons] at he hf
      rcases he with rfl | he <;> rcases hf with rfl | hf
      · rfl
      · have hb := r.node_bounds (mem_word r p hf).1
        have hd := exit_right_preference d ⟨a,cut,b⟩ ee
        have hflo := ef.1
        simp only at hd
        omega
      · have hb := r.node_bounds (mem_word r p he).1
        have hd := exit_right_preference d ⟨a,cut,b⟩ ef
        have helo := ee.1
        simp only at hd
        omega
      · exact ihr he hf

theorem terminal_not_exit {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    {e : Entry} (he : e ∈ word reference p) : ¬ Exit (Secondary.decodeDepth reference p).terminal e := by
  induction reference with
  | leaf => simp [word] at he
  | @node a b cut ha hb l r ihl ihr =>
    cases hp : p ⟨a,cut,b⟩
    · have ht : (Secondary.decodeDepth (.node cut ha hb l r) p).terminal = (Secondary.decodeDepth l p).terminal := by
        simp only [Secondary.decodeDepth,PrefRouter.terminal,hp,Bool.false_eq_true,if_false]
      rw [ht]
      simp only [word,hp,Bool.false_eq_true,if_false,List.mem_append,List.mem_singleton] at he
      rcases he with he | rfl
      · exact ihl he
      · intro h
        have hd := exit_left_preference _ _ h
        have hb := (Secondary.decodeDepth_mem l p _).mp (PrefRouter.terminal_mem _)
        simp only at hd
        omega
    · have ht : (Secondary.decodeDepth (.node cut ha hb l r) p).terminal = (Secondary.decodeDepth r p).terminal := by
        simp only [Secondary.decodeDepth,PrefRouter.terminal,hp,if_true]
      rw [ht]
      simp only [word,hp,if_true,List.mem_cons] at he
      rcases he with rfl | he
      · intro h
        have hd := exit_right_preference _ _ h
        have hb := (Secondary.decodeDepth_mem r p _).mp (PrefRouter.terminal_mem _)
        simp only at hd
        omega
      · exact ihr he

end TangoSquared.Paper20261030.SeparatorPath
