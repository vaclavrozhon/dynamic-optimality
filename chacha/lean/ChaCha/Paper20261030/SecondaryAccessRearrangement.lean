import ChaCha.Paper20261030.DecodedHeadPivot

/-!
# Composing the physical repairs for a complete secondary preference update

Every step in the existing first-wrong-edge trace is implemented by the
charged descendant repair. Thus the actual final representation has the
ordinary access preferences, and the total rearrangement cost is bounded
by the actual number of secondary flips times a logarithmic factor.

This theorem concerns the physical preference-update phase. Observed
departure/boundary selection, reaching the requested terminal, and the
full Cha-Cha simulation are still separate obligations.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open PreferredProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem source_of_decode_eq {a b : Nat} (reference : DepthTree a b) (p q : DepthSplit → Bool)
    (he : Secondary.decodeDepth reference p = Secondary.decodeDepth reference q) :
    source reference p = source reference q := by
  induction reference with
  | leaf => rfl
  | node cut ha hb l r ihl ihr =>
    obtain ⟨hp,hl,hr⟩ := PrefRouter.fork.inj he
    simp only [source,hp,ihl hl,ihr hr]

def repairBound {a b : Nat} (reference : DepthTree a b) : Nat :=
  19665 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 266

theorem head_step_charged {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    {request depth : Nat} {after : PrefRouter Nat}
    (step : PrefRouter.HeadStep request depth (Secondary.decodeDepth reference p) after)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    ∃ (q : DepthSplit → Bool) (out : AuxiliaryComponent Nat Nat (Tagged Payload)),
      Secondary.decodeDepth reference q = after ∧ Represents followsRight (source reference q) out ∧
      SourcePointer.Rearranges (closed c) (closed out) (repairBound reference) := by
  obtain ⟨v,decode⟩ := decoded_head_pivot reference p step
  obtain ⟨out,represented',trace⟩ := flip_descendant_charged v.lo_le_cut v.cut_lt_hi v.left v.right
    reference p v.below c represented
  exact ⟨Function.update p v.split (!p v.split),out,decode,represented',trace⟩

theorem head_trace_charged {a b : Nat} (reference : DepthTree a b)
    {request : Nat} {before after : PrefRouter Nat} {depths : List Nat}
    (steps : PrefRouter.HeadTrace request before depths after)
    (p : DepthSplit → Bool) (decoded : Secondary.decodeDepth reference p = before)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    ∃ (q : DepthSplit → Bool) (out : AuxiliaryComponent Nat Nat (Tagged Payload)),
      Secondary.decodeDepth reference q = after ∧ Represents followsRight (source reference q) out ∧
      SourcePointer.Rearranges (closed c) (closed out) (depths.length * repairBound reference) := by
  induction steps generalizing p c with
  | nil tree => exact ⟨p,c,decoded,represented,SourcePointer.rearranges_refl _ _⟩
  | cons step rest ih =>
    rw [← decoded] at step
    obtain ⟨q,middle,hmdecode,hmrep,firstTrace⟩ := head_step_charged reference p step c represented
    obtain ⟨last,out,hdecode,hrep,lastTrace⟩ := ih q hmdecode middle hmrep
    refine ⟨last,out,hdecode,hrep,(firstTrace.trans lastTrace).mono ?_⟩
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm,Nat.le_refl]

theorem access_rearrangement {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (request : Nat) (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight (source reference (Secondary.intervalUpdate request p)) out ∧
      SourcePointer.Rearranges (closed c) (closed out)
        ((Secondary.decodeDepth reference p).accessFlips request * repairBound reference) := by
  obtain ⟨q,out,decoded,represented',trace⟩ := head_trace_charged reference
    (PrefRouter.access_headTrace request (Secondary.decodeDepth reference p)) p rfl c represented
  have same : source reference q = source reference (Secondary.intervalUpdate request p) :=
    source_of_decode_eq reference q _ (decoded.trans (Secondary.decodeDepth_access reference p request).symm)
  rw [same] at represented'
  rw [PrefRouter.exitDepths_length] at trace
  exact ⟨out,represented',trace⟩

end ChaCha.Paper20261030.SecondaryDecomposition
