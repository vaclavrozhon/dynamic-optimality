import TangoSquared.Paper20261030.ContextReassembly
import TangoSquared.Paper20261030.LocalProjectedRotation

/-! Executable reassembly of an exposed context. The generated instructions
depend only on its finite shape and block-presence bits. Whole block trees
occur only in the correctness theorem. Both normalization and reconstruction
have explicit instruction lists; reconstruction needs no execution history.
-/

namespace TangoSquared.Paper20261030.OrderedContext.Local

open RouterProjection ColoredStorage ProjectionLocal LocalProjectedRotation
open LocalRecordActions (Action)

variable {ι α ρ : Type*}

def present (bits : ι → Bool) : Router ι → Bool
  | .empty => false
  | .leaf key => bits key
  | .fork l r => present bits l || present bits r

theorem realize_present (blocks : ι → Projected α ρ) (t : Router ι) :
    (realize blocks t).isSome = present (fun key => (blocks key).isSome) t := by
  induction t <;> simp_all only [realize,present,join_isSome,Option.isSome_none]

def normalize (bits : ι → Bool) (t : Router ι) : List (Action ρ) :=
  match t with
  | .fork (.leaf key) r => liftRight (bits key) (present bits r) (normalize bits r)
  | .fork (.fork u v) r =>
      route (present bits u) (present bits v) (present bits r) ++
        normalize bits (.fork u (.fork v r))
  | _ => []
termination_by weight t
decreasing_by all_goals simp only [weight,Router.internalCount]; omega

def restore (bits : ι → Bool) (t : Router ι) : List (Action ρ) :=
  match t with
  | .fork (.leaf key) r => liftRight (bits key) (present bits r) (restore bits r)
  | .fork (.fork u v) r =>
      restore bits (.fork u (.fork v r)) ++
        routeLeft (present bits u) (present bits v) (present bits r)
  | _ => []
termination_by weight t
decreasing_by all_goals simp only [weight,Router.internalCount]; omega

theorem comb_present (blocks : ι → Projected α ρ) (t : Router ι) :
    (comb blocks t.leaves).isSome = (realize blocks t).isSome := by
  -- Presence depends only on the ordered block word, including empty blocks.
  have append (xs ys : List ι) :
      (comb blocks (xs++ys)).isSome = ((comb blocks xs).isSome || (comb blocks ys).isSome) := by
    induction xs with
    | nil => simp [comb]
    | cons key rest ih => simp only [List.cons_append,comb,join_isSome,ih,Bool.or_assoc]
  induction t with
  | empty => rfl
  | leaf key => simp [comb,realize,Router.leaves,join_isSome]
  | fork l r ihl ihr => simp only [Router.leaves,realize,append,join_isSome,ihl,ihr]

theorem normalize_run (blocks : ι → Projected α ρ) (t : Router ι) (full : Router.Full t) :
    Transforms (normalize (fun key => (blocks key).isSome) t)
      (realize blocks t) (comb blocks t.leaves) (2*weight t) := by
  cases t with
  | empty => trivial
  | leaf key =>
    simp only [normalize,realize,Router.leaves,comb]
    cases h : blocks key <;> exact LocalProjectedRotation.refl _ _
  | fork l r =>
    obtain ⟨nl,nr,fl,fr⟩ := full
    cases l with
    | empty => exact False.elim (nl rfl)
    | leaf key =>
      have body := (normalize_run blocks r fr).join_right (blocks key)
      simpa only [normalize,realize,Router.leaves,List.singleton_append,comb,realize_present,weight]
        using body.mono (by simp only [weight,Router.internalCount]; omega)
    | fork u v =>
      obtain ⟨nu,nv,fu,fv⟩ := fl
      have smaller := normalize_run blocks (.fork u (.fork v r)) ⟨nu,by simp,fu,⟨nv,nr,fv,fr⟩⟩
      have actual := (associate (realize blocks u) (realize blocks v) (realize blocks r)).trans smaller
      have words : (Router.fork u (.fork v r)).leaves = (Router.fork (.fork u v) r).leaves := by
        simp only [Router.leaves,List.append_assoc]
      rw [words] at actual
      simpa only [normalize,realize,realize_present] using
        actual.mono (by have := weight_rotate u v r; omega)
termination_by weight t
decreasing_by all_goals subst_vars; simp_all only [weight,Router.internalCount]; omega

theorem restore_run (blocks : ι → Projected α ρ) (t : Router ι) (full : Router.Full t) :
    Transforms (restore (fun key => (blocks key).isSome) t)
      (comb blocks t.leaves) (realize blocks t) (2*weight t) := by
  cases t with
  | empty => trivial
  | leaf key =>
    simp only [restore,realize,Router.leaves,comb]
    cases h : blocks key <;> exact LocalProjectedRotation.refl _ _
  | fork l r =>
    obtain ⟨nl,nr,fl,fr⟩ := full
    cases l with
    | empty => exact False.elim (nl rfl)
    | leaf key =>
      have body := (restore_run blocks r fr).join_right (blocks key)
      simpa only [restore,realize,Router.leaves,List.singleton_append,comb,
        comb_present,realize_present,weight] using
        body.mono (by simp only [weight,Router.internalCount]; omega)
    | fork u v =>
      obtain ⟨nu,nv,fu,fv⟩ := fl
      have smaller := restore_run blocks (.fork u (.fork v r)) ⟨nu,by simp,fu,⟨nv,nr,fv,fr⟩⟩
      have actual := smaller.trans (associate_left (realize blocks u) (realize blocks v) (realize blocks r))
      have words : (Router.fork u (.fork v r)).leaves = (Router.fork (.fork u v) r).leaves := by
        simp only [Router.leaves,List.append_assoc]
      rw [words] at actual
      simpa only [restore,realize,realize_present] using
        actual.mono (by have := weight_rotate u v r; omega)
termination_by weight t
decreasing_by all_goals subst_vars; simp_all only [weight,Router.internalCount]; omega

def reassemble (bits : ι → Bool) (before after : Router ι) : List (Action ρ) :=
  normalize bits before ++ restore bits after

theorem reassemble_run (blocks : ι → Projected α ρ) (before after : Router ι)
    (beforeFull : Router.Full before) (afterFull : Router.Full after)
    (ordered : before.leaves = after.leaves) :
    Transforms (reassemble (fun key => (blocks key).isSome) before after)
      (realize blocks before) (realize blocks after)
      (6*(Router.internalCount before+Router.internalCount after)) := by
  have first := normalize_run blocks before beforeFull
  have last := restore_run blocks after afterFull
  rw [← ordered] at last
  exact (first.trans last).mono (by have := weight_bound before; have := weight_bound after; omega)

end TangoSquared.Paper20261030.OrderedContext.Local
