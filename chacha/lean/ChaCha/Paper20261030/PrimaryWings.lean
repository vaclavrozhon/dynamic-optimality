import ChaCha.Paper20261030.AbstractTango
import ChaCha.Paper20261030.Restriction

/-!
# Original-key order of a primary path's two wings

An exit is the nonpreferred child subtree at one vertex of the current
preferred path. Exits are listed from the root toward the endpoint. Left
exits occur in this order in the original leaf word; right exits occur in
reverse order. Any depth-order routing tree on these exits can therefore
be projected into two wings and expanded with the original subtrees.
-/

namespace ChaCha.Paper20261030.PrimaryWings

open PreferredProjection RouterProjection

variable {α : Type*}

structure Exit (α : Type*) where
  leftOfEndpoint : Bool
  subtree : PrefRouter α
  deriving DecidableEq

def exits : PrefRouter α → List (Exit α)
  | .leaf _ => []
  | .fork false l r => ⟨false,r⟩ :: exits l
  | .fork true l r => ⟨true,l⟩ :: exits r

theorem leaf_partition (t : PrefRouter α) :
    t.leaves =
      ((exits t).filter (·.leftOfEndpoint)).flatMap (fun e => e.subtree.leaves) ++
        [t.terminal] ++
      (((exits t).filter (fun e => !e.leftOfEndpoint)).reverse).flatMap (fun e => e.subtree.leaves) := by
  induction t with
  | leaf key => rfl
  | fork bit l r ihl ihr =>
    cases bit
    · simpa [exits,PrefRouter.leaves,PrefRouter.terminal,List.filter_cons,List.append_assoc] using
          congrArg (fun word => word ++ r.leaves) ihl
    · simpa [exits,PrefRouter.leaves,PrefRouter.terminal,List.filter_cons,List.append_assoc] using
          congrArg (fun word => l.leaves ++ word) ihr

theorem leaves_positive (t : PrefRouter α) : 0 < t.leaves.length := by
  classical
  have hm := t.terminal_mem
  cases he : t.leaves with
  | nil => simp [he] at hm
  | cons => simp

theorem exit_smaller {t : PrefRouter α} {e : Exit α} (he : e ∈ exits t) :
    e.subtree.leaves.length < t.leaves.length := by
  induction t with
  | leaf key => simp [exits] at he
  | fork bit l r ihl ihr =>
    have hl := leaves_positive l
    have hr := leaves_positive r
    cases bit
    · simp only [exits,List.mem_cons] at he
      rcases he with rfl | he
      · simp only [PrefRouter.leaves,List.length_append]; omega
      · have hh := ihl he
        simp only [PrefRouter.leaves,List.length_append]
        omega
    · simp only [exits,List.mem_cons] at he
      rcases he with rfl | he
      · simp only [PrefRouter.leaves,List.length_append]; omega
      · have hh := ihr he
        simp only [PrefRouter.leaves,List.length_append]
        omega

theorem mirror_leaves {γ : Type*} (t : Router γ) :
    (Paper20261030.Router.mirror t).leaves = t.leaves.reverse := by
  induction t with
  | empty => rfl
  | leaf key => rfl
  | fork l r ihl ihr =>
    simp only [Paper20261030.Router.mirror,Router.leaves,List.reverse_append,ihl,ihr]

theorem substitute_leaves {γ : Type*} (f : γ → Router α) (t : Router γ) :
    (Paper20261030.Router.substitute f t).leaves = t.leaves.flatMap (fun key => (f key).leaves) := by
  induction t with
  | empty => rfl
  | leaf key => simp [Paper20261030.Router.substitute,Router.leaves]
  | fork l r ihl ihr =>
    simp only [Paper20261030.Router.substitute,Router.leaves_join,Router.leaves,
      List.flatMap_append,ihl,ihr]

def component (routing : Router (Exit α)) (endpoint : α) (payload : Exit α → Router α) : Router α :=
  ((Paper20261030.Router.substitute payload (routing.prune (·.leftOfEndpoint))).join (.leaf endpoint)).join
    (Paper20261030.Router.substitute payload
      (Paper20261030.Router.mirror (routing.prune (fun e => !e.leftOfEndpoint))))

/-- Conditional only on the actual port word and payload words: no
simulation or operation-cost hypothesis is used in this routing lemma. -/
theorem component_leaves (t : PrefRouter α) (routing : Router (Exit α))
    (hr : routing.leaves = exits t) (payload : Exit α → Router α)
    (hp : ∀ e ∈ exits t, (payload e).leaves = e.subtree.leaves) :
    (component routing t.terminal payload).leaves = t.leaves := by
  simp only [component,Router.leaves_join,Router.leaves,substitute_leaves,mirror_leaves,
    Router.leaves_prune,hr]
  have hleft := List.flatMap_congr (l := (exits t).filter (·.leftOfEndpoint))
    (f := fun e => (payload e).leaves) (g := fun e => e.subtree.leaves)
    (fun e he => hp e (List.mem_filter.mp he).1)
  have hright := List.flatMap_congr (l := ((exits t).filter (fun e => !e.leftOfEndpoint)).reverse)
    (f := fun e => (payload e).leaves) (g := fun e => e.subtree.leaves)
    (fun e he => hp e (List.mem_filter.mp (List.mem_reverse.mp he)).1)
  rw [hleft,hright]
  exact (leaf_partition t).symm

theorem substitute_full {γ : Type*} (f : γ → Router α) (t : Router γ)
    (hf : ∀ key, Paper20261030.Router.Full (f key)) :
    Paper20261030.Router.Full (Paper20261030.Router.substitute f t) := by
  induction t with
  | empty => trivial
  | leaf key => exact hf key
  | fork l r ihl ihr => exact Paper20261030.Router.full_join ihl ihr

theorem component_full (routing : Router (Exit α)) (endpoint : α) (payload : Exit α → Router α)
    (hp : ∀ e, Paper20261030.Router.Full (payload e)) :
    Paper20261030.Router.Full (component routing endpoint payload) :=
  Paper20261030.Router.full_join
    (Paper20261030.Router.full_join (substitute_full payload _ hp) True.intro)
    (substitute_full payload _ hp)

theorem component_nonempty (routing : Router (Exit α)) (endpoint : α) (payload : Exit α → Router α) :
    component routing endpoint payload ≠ .empty := by
  unfold component
  generalize Paper20261030.Router.substitute payload (routing.prune (·.leftOfEndpoint)) = l
  generalize Paper20261030.Router.substitute payload
    (Paper20261030.Router.mirror (routing.prune (fun e => !e.leftOfEndpoint))) = r
  cases l <;> cases r <;> simp [Router.join]

/-- A snapshot of the recursively expanded routing. The chosen routing
tree is supplied for each actual primary component; this definition makes
no dynamic update or operation-cost assertion. -/
def expand [DecidableEq α] (routing : PrefRouter α → Router (Exit α)) (t : PrefRouter α) : Router α :=
  component (routing t) t.terminal
    (fun e => if he : e ∈ exits t then expand routing e.subtree else .empty)
termination_by t.leaves.length
decreasing_by exact exit_smaller he

theorem expand_leaves [DecidableEq α] (routing : PrefRouter α → Router (Exit α))
    (hr : ∀ t, (routing t).leaves = exits t) (t : PrefRouter α) :
    (expand routing t).leaves = t.leaves := by
  rw [expand]
  apply component_leaves t _ (hr t)
  intro e he
  simp only [dif_pos he]
  exact expand_leaves routing hr e.subtree
termination_by t.leaves.length
decreasing_by exact exit_smaller he

theorem expand_full [DecidableEq α] (routing : PrefRouter α → Router (Exit α)) (t : PrefRouter α) :
    Paper20261030.Router.Full (expand routing t) := by
  rw [expand]
  apply component_full
  intro e
  split
  · exact expand_full routing e.subtree
  · trivial
termination_by t.leaves.length
decreasing_by exact exit_smaller (by assumption)

theorem expand_nonempty [DecidableEq α] (routing : PrefRouter α → Router (Exit α)) (t : PrefRouter α) :
    expand routing t ≠ .empty := by
  rw [expand]
  exact component_nonempty _ _ _

/-- The expanded representation has precisely one fewer internal routing
vertices than original leaves, with no additional leaves. -/
theorem expand_internal_count [DecidableEq α] (routing : PrefRouter α → Router (Exit α))
    (hr : ∀ t, (routing t).leaves = exits t) (t : PrefRouter α) :
    Paper20261030.Router.internalCount (expand routing t) + 1 = t.leaves.length := by
  have hc := Paper20261030.Router.full_leaf_count (expand routing t)
    (expand_full routing t) (expand_nonempty routing t)
  rw [expand_leaves routing hr t] at hc
  exact hc.symm

theorem expand_nodup [DecidableEq α] (routing : PrefRouter α → Router (Exit α))
    (hr : ∀ t, (routing t).leaves = exits t) (t : PrefRouter α) (hn : t.leaves.Nodup) :
    (expand routing t).leaves.Nodup := by
  rw [expand_leaves routing hr]
  exact hn

end ChaCha.Paper20261030.PrimaryWings
