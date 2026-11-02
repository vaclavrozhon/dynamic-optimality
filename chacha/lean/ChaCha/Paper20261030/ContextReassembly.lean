import ChaCha.Paper20261030.SourceReversal

/-!
# Linear-cost reassembly of exposed ordered contexts

A context is a full binary routing tree whose leaves name unchanged
blocks. A block may be absent in a particular projection. `realize`
substitutes those blocks and suppresses empty children, creating empty
connector-record lists at the remaining context vertices.

Normalize a context to the right comb by root rotations and descent
along its right spine. The potential `weight` decreases at a rotation
and at a descent; hence both rotations and cursor movements are charged.
The supplied block trees, including their stored records, are preserved.
Connector record removal/restoration is a separate operation.
-/

namespace ChaCha.Paper20261030.ProjectionLocal

theorem Rearranges.mono {α ρ : Type*} {a b : Projected α ρ} {m n : Nat}
    (h : Rearranges a b m) (bound : m ≤ n) : Rearranges a b n := by
  cases a <;> cases b
  · trivial
  · exact False.elim h
  · exact False.elim h
  · exact SourcePointer.Rearranges.mono h bound

end ChaCha.Paper20261030.ProjectionLocal

namespace ChaCha.Paper20261030.OrderedContext

open RouterProjection ColoredStorage ProjectionLocal

variable {ι α ρ : Type*}

def realize (blocks : ι → Projected α ρ) : Router ι → Projected α ρ
  | .empty => none
  | .leaf key => blocks key
  | .fork l r => join (realize blocks l) (realize blocks r)

def comb (blocks : ι → Projected α ρ) : List ι → Projected α ρ
  | [] => none
  | key :: rest => join (blocks key) (comb blocks rest)

def weight : Router ι → Nat
  | .empty => 0
  | .leaf _ => 0
  | .fork l r => 3 * Router.internalCount l + 1 + weight r

theorem weight_bound (t : Router ι) : weight t ≤ 3 * Router.internalCount t := by
  induction t with
  | empty => exact le_rfl
  | leaf => exact le_rfl
  | fork l r ihl ihr => simp only [weight,Router.internalCount]; omega

theorem weight_rotate (u v w : Router ι) :
    weight (.fork u (.fork v w)) + 2 = weight (.fork (.fork u v) w) := by
  simp only [weight,Router.internalCount]
  omega

theorem normalize (blocks : ι → Projected α ρ) (t : Router ι) (full : Router.Full t) :
    Rearranges (realize blocks t) (comb blocks t.leaves) (2 * weight t) := by
  cases t with
  | empty => exact rearranges_refl _ _
  | leaf key =>
    simp only [realize,Router.leaves,comb]
    cases h : blocks key <;> exact rearranges_refl _ _
  | fork l r =>
    obtain ⟨nonemptyLeft,nonemptyRight,fullLeft,fullRight⟩ := full
    cases l with
    | empty => exact False.elim (nonemptyLeft rfl)
    | leaf key =>
      have tail := normalize blocks r fullRight
      have lifted := tail.join_right (l := blocks key)
      simpa only [realize,Router.leaves,List.singleton_append,comb,weight] using
        lifted.mono (by simp only [weight,Router.internalCount]; omega)
    | fork u v =>
      obtain ⟨nu,nv,fu,fv⟩ := fullLeft
      have targetFull : Router.Full (.fork u (.fork v r)) :=
        ⟨nu,by simp,fu,⟨nv,nonemptyRight,fv,fullRight⟩⟩
      have normalized := normalize blocks (.fork u (.fork v r)) targetFull
      have rotate := join_associate (realize blocks u) (realize blocks v) (realize blocks r)
      have path := rotate.trans normalized
      have words : (Router.fork u (.fork v r)).leaves = (Router.fork (.fork u v) r).leaves := by
        simp only [Router.leaves,List.append_assoc]
      rw [words] at path
      exact path.mono (by have := weight_rotate u v r; omega)
termination_by weight t
decreasing_by
  all_goals subst_vars; simp_all only [weight,Router.internalCount]; omega

theorem reassemble (blocks : ι → Projected α ρ) (before after : Router ι)
    (beforeFull : Router.Full before) (afterFull : Router.Full after)
    (orderedBlocks : before.leaves = after.leaves) :
    Rearranges (realize blocks before) (realize blocks after)
      (6 * (Router.internalCount before + Router.internalCount after)) := by
  have first := normalize blocks before beforeFull
  have last := normalize blocks after afterFull
  rw [← orderedBlocks] at last
  apply (first.trans last.symm).mono
  have hb := weight_bound before
  have ha := weight_bound after
  omega

/-- For two full contexts on the same `k` nonempty placeholder positions,
all actual cursor work is bounded linearly in `k`, even if some projected
blocks are empty. -/
theorem reassemble_leaf_bound (blocks : ι → Projected α ρ) (before after : Router ι)
    (beforeFull : Router.Full before) (afterFull : Router.Full after)
    (orderedBlocks : before.leaves = after.leaves) (k : Nat)
    (beforeSize : before.leaves.length = k) :
    Rearranges (realize blocks before) (realize blocks after) (12 * k) := by
  have count_bound (t : Router ι) (full : Router.Full t) : Router.internalCount t ≤ t.leaves.length := by
    by_cases empty : t = .empty
    · subst t; exact le_rfl
    · have := Router.full_leaf_count t full empty
      omega
  apply (reassemble blocks before after beforeFull afterFull orderedBlocks).mono
  have hb := count_bound before beforeFull
  have ha := count_bound after afterFull
  rw [← orderedBlocks,beforeSize] at ha
  rw [beforeSize] at hb
  omega

end ChaCha.Paper20261030.OrderedContext
