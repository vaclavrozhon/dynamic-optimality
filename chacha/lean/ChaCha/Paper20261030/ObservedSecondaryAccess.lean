import ChaCha.Paper20261030.SecondaryTerminalVisit
import ChaCha.Paper20261030.ClosedNeighborQueries

/-!
# Secondary source accesses including the observed selection queries

Before each physical repair, read the two query neighbors and the two
interval boundaries supplied by the selected departure record. Their
decoders and exact selection semantics are proved in the imported query
modules. Include the final no-departure query and the actual terminal
visit. All these observation phases appear in the charged source trace.

This supplies the secondary source-level cost bound. The unified local
interpreter for recursive balancing, prepared primary head switches,
colored storage and original-key BST compilation are separate tasks.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open PreferredProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

def observedRepairBound {a b : Nat} (reference : DepthTree a b) : Nat :=
  19700 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 300

theorem head_step_observed {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    {request depth : Nat} {after : PrefRouter Nat}
    (step : PrefRouter.HeadStep request depth (Secondary.decodeDepth reference p) after)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    ∃ (v : PreferredSplit p reference) (out : AuxiliaryComponent Nat Nat (Tagged Payload)),
      Secondary.decodeDepth reference (Function.update p v.split (!p v.split)) = after ∧
      Represents followsRight (source reference (Function.update p v.split (!p v.split))) out ∧
      observedExit request (neighbors request c.core) = some ⟨v.split.cut,(v.split,p v.split)⟩ ∧
      SourcePointer.Rearranges (closed c) (closed out) (observedRepairBound reference) := by
  obtain ⟨v,decode,selected⟩ := observed_head_selection reference p step c represented
  obtain ⟨hc,hp⟩ := represented.invariant
  have queries := query_three_charged request v.split.lo v.split.hi c hc hp
  obtain ⟨out,hout,repaired⟩ := flip_descendant_charged v.lo_le_cut v.cut_lt_hi v.left v.right
    reference p v.below c represented
  refine ⟨v,out,decode,hout,selected,(queries.trans repaired).mono ?_⟩
  have hsize := represented_size reference p c represented
  have hlog := Nat.clog_monotone 2 (Nat.add_le_add_right hsize 1)
  unfold observedRepairBound
  omega

theorem head_trace_observed {a b : Nat} (reference : DepthTree a b)
    {request : Nat} {before after : PrefRouter Nat} {depths : List Nat}
    (steps : PrefRouter.HeadTrace request before depths after)
    (p : DepthSplit → Bool) (decoded : Secondary.decodeDepth reference p = before)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    ∃ (q : DepthSplit → Bool) (out : AuxiliaryComponent Nat Nat (Tagged Payload)),
      Secondary.decodeDepth reference q = after ∧ Represents followsRight (source reference q) out ∧
      SourcePointer.Rearranges (closed c) (closed out) (depths.length * observedRepairBound reference) := by
  induction steps generalizing p c with
  | nil tree => exact ⟨p,c,decoded,represented,SourcePointer.rearranges_refl _ _⟩
  | cons step rest ih =>
    rw [← decoded] at step
    obtain ⟨v,middle,hmdecode,hmrep,selected,firstTrace⟩ := head_step_observed reference p step c represented
    obtain ⟨last,out,hdecode,hrep,lastTrace⟩ := ih (Function.update p v.split (!p v.split)) hmdecode middle hmrep
    refine ⟨last,out,hdecode,hrep,(firstTrace.trans lastTrace).mono ?_⟩
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm,Nat.le_refl]

theorem access_observed_visits_leaf {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (request : Nat) (valid : a ≤ request ∧ request ≤ b)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight (source reference (Secondary.intervalUpdate request p)) out ∧
      observedExit request (neighbors request out.core) = none ∧
      SourcePointer.VisitsLeaf request (closed c) (closed out)
        (((Secondary.decodeDepth reference p).accessFlips request + 1) * observedRepairBound reference) := by
  obtain ⟨q,out,decoded,hout,rearranged⟩ := head_trace_observed reference
    (PrefRouter.access_headTrace request (Secondary.decodeDepth reference p)) p rfl c represented
  have same := source_of_decode_eq reference q (Secondary.intervalUpdate request p)
    (decoded.trans (Secondary.decodeDepth_access reference p request).symm)
  rw [same] at hout
  rw [PrefRouter.exitDepths_length] at rearranged
  have endpoint : (Secondary.decodeDepth reference (Secondary.intervalUpdate request p)).terminal = request := by
    rw [Secondary.decodeDepth_access]
    exact PrefRouter.terminal_access _ _ ((Secondary.decodeDepth_mem reference p request).mpr valid)
  have stopped := observed_terminal_none reference (Secondary.intervalUpdate request p) out hout
  rw [endpoint] at stopped
  obtain ⟨hc,hp⟩ := hout.invariant
  have finalQuery := query_closed_charged request out hc hp
  have visited := visit_terminal reference (Secondary.intervalUpdate request p) request endpoint out hout
  refine ⟨out,hout,stopped,((visited.prepend finalQuery).prepend rearranged).mono ?_⟩
  rw [Nat.add_mul,Nat.one_mul]
  apply Nat.add_le_add_left
  have hsize := represented_size reference (Secondary.intervalUpdate request p) out hout
  have hlog := Nat.clog_monotone 2 (Nat.add_le_add_right hsize 1)
  unfold observedRepairBound
  omega

end ChaCha.Paper20261030.SecondaryDecomposition
