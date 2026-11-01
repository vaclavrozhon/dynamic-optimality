import TangoSquared.Paper20261030.LocalHeadReassembly

/-! Bounds on the actual reassembly instruction lists. These bound the
control script, not the sizes of its record packets. Bounding all packets
and the transient physical record lists remains a separate invariant.
-/

namespace TangoSquared.Paper20261030.OrderedContext.Local

open RouterProjection ColoredStorage ProjectionLocal LocalProjectedRotation
open LocalRecordActions (Action)

variable {ι ρ : Type*}

theorem liftLeft_length (l r : Bool) (actions : List (Action ρ)) :
    (liftLeft l r actions).length ≤ actions.length+2 := by
  cases l <;> cases r <;> simp [liftLeft,LocalRecordActions.left]

theorem liftRight_length (l r : Bool) (actions : List (Action ρ)) :
    (liftRight l r actions).length ≤ actions.length+2 := by
  cases l <;> cases r <;> simp [liftRight,LocalRecordActions.right]

theorem route_length (a b c : Bool) : (route (ρ := ρ) a b c).length ≤ 1 := by
  cases a <;> cases b <;> cases c <;> simp [route]

theorem routeLeft_length (a b c : Bool) : (routeLeft (ρ := ρ) a b c).length ≤ 1 := by
  cases a <;> cases b <;> cases c <;> simp [routeLeft]

theorem routing_lengths (bits : ι → Bool) (t : Router ι) (full : Router.Full t) :
    (normalize (ρ := ρ) bits t).length ≤ 2*weight t ∧
    (restore (ρ := ρ) bits t).length ≤ 2*weight t := by
  cases t with
  | empty => simp [normalize,restore,weight]
  | leaf key => simp [normalize,restore,weight]
  | fork l r =>
    obtain ⟨nl,nr,fl,fr⟩ := full
    cases l with
    | empty => exact False.elim (nl rfl)
    | leaf key =>
      obtain ⟨hn,hr⟩ := routing_lengths bits r fr
      have ln := liftRight_length (bits key) (present bits r) (normalize (ρ := ρ) bits r)
      have lr := liftRight_length (bits key) (present bits r) (restore (ρ := ρ) bits r)
      simp only [normalize,restore,weight]
      constructor <;> omega
    | fork u v =>
      obtain ⟨nu,nv,fu,fv⟩ := fl
      obtain ⟨hn,hr⟩ := routing_lengths bits (.fork u (.fork v r)) ⟨nu,by simp,fu,⟨nv,nr,fv,fr⟩⟩
      have ln := route_length (ρ := ρ) (present bits u) (present bits v) (present bits r)
      have lr := routeLeft_length (ρ := ρ) (present bits u) (present bits v) (present bits r)
      have wt := weight_rotate u v r
      simp only [normalize,restore,List.length_append]
      constructor <;> omega
termination_by weight t
decreasing_by all_goals subst_vars; simp_all only [weight,Router.internalCount]; omega

theorem record_lengths (bits : ι → Bool) (t : Source ι (List ρ)) :
    (clear bits t).length ≤ 5*vertices t ∧ (install bits t).length ≤ 5*vertices t := by
  induction t with
  | leaf key records => simp [clear,install,vertices]
  | fork records l r ihl ihr =>
    have lc := liftLeft_length (present bits l.shape) (present bits r.shape) (clear bits l)
    have rc := liftRight_length (present bits l.shape) (present bits r.shape) (clear bits r)
    have li := liftLeft_length (present bits l.shape) (present bits r.shape) (install bits l)
    have ri := liftRight_length (present bits l.shape) (present bits r.shape) (install bits r)
    simp only [clear,install,List.length_append,List.length_cons,List.length_nil,vertices]
    constructor <;> omega

theorem decoratedActions_length (bits : ι → Bool) (before after : Source ι (List ρ))
    (ordered : before.shape.leaves = after.shape.leaves) :
    (decoratedActions bits before after).length ≤ 32*before.shape.leaves.length := by
  have bn := (routing_lengths bits before.shape (context_full before) (ρ := ρ)).1
  have ar := (routing_lengths bits after.shape (context_full after) (ρ := ρ)).2
  have bc := (record_lengths bits before).1
  have ai := (record_lengths bits after).2
  have bw := weight_bound before.shape
  have aw := weight_bound after.shape
  have bv := context_vertices before
  have av := context_vertices after
  have cb := Router.full_leaf_count before.shape (context_full before) (SourcePointer.source_nonempty before)
  have ca := Router.full_leaf_count after.shape (context_full after) (SourcePointer.source_nonempty after)
  rw [← ordered] at av ca
  simp only [decoratedActions,reassemble,List.length_append]
  omega

end TangoSquared.Paper20261030.OrderedContext.Local

namespace TangoSquared.Paper20261030.HeadBlocks.Local

theorem actions_length {ρ : Type*} (oldRight : Bool) (bits : Fin 8 → Bool)
    (oldRecords newRecords : List Bool → List ρ) :
    (actions oldRight bits oldRecords newRecords).length ≤ 256 := by
  have bound := OrderedContext.Local.decoratedActions_length bits
    (recordContext oldRecords [] (before oldRight)) (recordContext newRecords [] (after oldRight))
    (by rw [recordContext_shape,recordContext_shape]; exact block_order oldRight)
  simpa only [actions,recordContext_shape,block_count,Nat.reduceMul] using bound

end TangoSquared.Paper20261030.HeadBlocks.Local
