import TangoSquared.Paper20261030.PrimaryAddresses

/-!
# Owners of the secondary writes at a head switch

An inner access at exit depth `d` writes intervals starting no deeper than
`d`. Before the switch, the current preferred-path endpoint and the target
key have identical owner addresses through that depth. Thus indexing those
writes by the target's ancestors agrees with the actual active path.
-/

namespace TangoSquared.PreferredProjection.PrefRouter

variable {α : Type*} [DecidableEq α]

theorem HeadStep.target_mem {x : α} {d : Nat} {t u : PrefRouter α}
    (h : HeadStep x d t u) : x ∈ t.leaves := by
  induction h with
  | leftRoot l r hx => exact List.mem_append_left _ hx
  | rightRoot l r hl hr => exact List.mem_append_right _ hr
  | leftDown r h ih => exact List.mem_append_left _ ih
  | rightDown l hl h ih => exact List.mem_append_right _ ih

theorem HeadStep.leaves {x : α} {d : Nat} {t u : PrefRouter α}
    (h : HeadStep x d t u) : u.leaves = t.leaves := by
  induction h with
  | leftRoot => rfl
  | rightRoot => rfl
  | leftDown r h ih => simp only [PrefRouter.leaves,ih]
  | rightDown l hl h ih => simp only [PrefRouter.leaves,ih]

theorem HeadStep.searchPath {x : α} {d : Nat} {t u : PrefRouter α}
    (h : HeadStep x d t u) (y : α) : u.searchPath y = t.searchPath y := by
  induction h with
  | leftRoot => rfl
  | rightRoot => rfl
  | leftDown r h ih => simp only [PrefRouter.searchPath,h.leaves,ih]
  | rightDown l hl h ih => simp only [PrefRouter.searchPath,h.leaves,ih]

theorem HeadStep.owner_prefix {x : α} {d : Nat} {t u : PrefRouter α}
    (h : HeadStep x d t u) (hn : t.leaves.Nodup) :
    (t.searchPath t.terminal).take d = (t.searchPath x).take d := by
  induction h with
  | leftRoot => rfl
  | rightRoot => rfl
  | @leftDown d l l' r h ih =>
    obtain ⟨hnl,_,_⟩ := List.nodup_append.mp hn
    have hx := h.target_mem
    have ht := terminal_mem l
    simpa only [PrefRouter.terminal,Bool.false_eq_true,↓reduceIte,PrefRouter.searchPath,if_pos hx,if_pos ht,
      List.take_succ_cons] using congrArg (false :: ·) (ih hnl)
  | @rightDown d r r' l hl h ih =>
    obtain ⟨hnl,hnr,hdis⟩ := List.nodup_append.mp hn
    have hx := h.target_mem
    have ht := terminal_mem r
    have htl : r.terminal ∉ l.leaves := fun hm => hdis _ hm _ ht rfl
    simpa only [PrefRouter.terminal,↓reduceIte,PrefRouter.searchPath,if_neg hl,if_pos hx,
      if_neg htl,if_pos ht,List.take_succ_cons] using congrArg (true :: ·) (ih hnr)

/-- Every memory touched by the inner exit access belongs to the same
primary owner whether read from the active endpoint or from the request. -/
theorem HeadStep.memory_owner {x : α} {d a : Nat} {t u : PrefRouter α}
    (h : HeadStep x d t u) (hn : t.leaves.Nodup) (ha : a ≤ d) :
    (t.searchPath t.terminal).take a = (t.searchPath x).take a := by
  have hp := congrArg (List.take a) (h.owner_prefix hn)
  simpa only [List.take_take,Nat.min_eq_left ha] using hp

end TangoSquared.PreferredProjection.PrefRouter
