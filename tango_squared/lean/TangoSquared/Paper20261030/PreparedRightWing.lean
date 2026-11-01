import TangoSquared.Paper20261030.PrimaryWings
import TangoSquared.Paper20261030.TangoRestriction

/-!
# Right outlets survive restriction at the prepared endpoint

After access has prepared an endpoint `d`, restricting an ordered
preferred tree to labels at least `d` deletes its left outlets and keeps
every right outlet as the same whole subtree. This is a structural part
of the prepared head-switch interface; it asserts no maintenance cost.
-/

namespace TangoSquared.PreferredProjection.PrefRouter

variable {α : Type*}

theorem prune_of_all_true (keep : α → Bool) (t : PrefRouter α)
    (h : ∀ key ∈ t.leaves, keep key = true) : t.prune keep = some t := by
  induction t with
  | leaf key => simp [prune,h key (by simp [leaves])]
  | fork bit l r ihl ihr =>
    have hl := ihl (fun key hk => h key (List.mem_append_left _ hk))
    have hr := ihr (fun key hk => h key (List.mem_append_right _ hk))
    simp [prune,hl,hr,combine]

theorem prune_of_all_false (keep : α → Bool) (t : PrefRouter α)
    (h : ∀ key ∈ t.leaves, keep key = false) : t.prune keep = none := by
  induction t with
  | leaf key => simp [prune,h key (by simp [leaves])]
  | fork bit l r ihl ihr =>
    have hl := ihl (fun key hk => h key (List.mem_append_left _ hk))
    have hr := ihr (fun key hk => h key (List.mem_append_right _ hk))
    simp [prune,hl,hr,combine]

end TangoSquared.PreferredProjection.PrefRouter

namespace TangoSquared.Paper20261030.PrimaryWings

open PreferredProjection

def leftExits (t : PrefRouter Nat) : List (Exit Nat) := (exits t).filter (·.leftOfEndpoint)

def rightExits (t : PrefRouter Nat) : List (Exit Nat) :=
  (exits t).filter (fun e => !e.leftOfEndpoint)

theorem prepared_suffix (t : PrefRouter Nat) (ordered : t.leaves.Pairwise (· < ·)) :
    ∃ u, t.prune (fun key => decide (t.terminal ≤ key)) = some u ∧
      u.terminal = t.terminal ∧ leftExits u = [] ∧ rightExits u = rightExits t := by
  induction t with
  | leaf key =>
    exact ⟨.leaf key,by simp [PrefRouter.prune,PrefRouter.terminal],rfl,rfl,rfl⟩
  | fork bit l r ihl ihr =>
    obtain ⟨hl,hr,hcross⟩ := List.pairwise_append.mp ordered
    cases bit
    · obtain ⟨l',hpl,ht,heL,heR⟩ := ihl hl
      have hpr : r.prune (fun key => decide (l.terminal ≤ key)) = some r := by
        apply PrefRouter.prune_of_all_true
        intro key hk
        have hh := hcross l.terminal l.terminal_mem key hk
        simp only [decide_eq_true_eq]
        omega
      refine ⟨.fork false l' r,?_,?_,?_,?_⟩
      · simp [PrefRouter.terminal,PrefRouter.prune,hpl,hpr,PrefRouter.combine]
      · simpa [PrefRouter.terminal] using ht
      · simpa only [leftExits,exits,List.filter_cons,Bool.false_eq_true,if_false] using heL
      · simpa only [rightExits,exits,List.filter_cons,Bool.not_false,if_true] using
          congrArg (fun rest => Exit.mk false r :: rest) heR
    · obtain ⟨r',hpr,ht,heL,heR⟩ := ihr hr
      have hpl : l.prune (fun key => decide (r.terminal ≤ key)) = none := by
        apply PrefRouter.prune_of_all_false
        intro key hk
        have hh := hcross key hk r.terminal r.terminal_mem
        simp only [decide_eq_false_iff_not]
        omega
      refine ⟨r',?_,?_,heL,?_⟩
      · simp [PrefRouter.terminal,PrefRouter.prune,hpl,hpr,PrefRouter.combine]
      · simpa [PrefRouter.terminal] using ht
      · simpa [rightExits,exits] using heR

end TangoSquared.Paper20261030.PrimaryWings
