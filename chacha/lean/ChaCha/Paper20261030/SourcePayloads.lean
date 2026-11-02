import ChaCha.Paper20261030.SourceReversal

/-!
# Charged source execution with whole payload subtrees at its leaves

The physical record at an attachment root contains the source record
list, a delimiter, and the payload's old record list. Internal source
vertices have no delimiter. A decoder reads only the prefix preceding
the first delimiter; replacing that prefix retains all payload metadata.
The delimiter also distinguishes a logical source leaf from the physical
payload tree hanging there. Every write reads the reached physical record
before changing its prefix. Source operations lift with factor two.

A payload is opaque to the lifted execution. This module proves the
local substitution correspondence; a global bound on overlapping primary
headers must also be established for the complete representation.
-/

namespace ChaCha.Paper20261030.SourcePayloads

open ColoredStorage SourcePointer

variable {α β ρ : Type*}

def decode (records : List (Option ρ)) : List ρ :=
  (records.takeWhile Option.isSome).filterMap id

def replace (fresh : List ρ) (records : List (Option ρ)) : List (Option ρ) :=
  fresh.map some ++ records.dropWhile Option.isSome

theorem decode_internal (records : List ρ) : decode (records.map some) = records := by
  induction records <;> simp_all [decode]

theorem decode_attachment (records : List ρ) (payload : List (Option ρ)) :
    decode (records.map some ++ none :: payload) = records := by
  induction records <;> simp_all [decode]

theorem replace_internal (old fresh : List ρ) : replace fresh (old.map some) = fresh.map some := by
  have empty : (old.map some).dropWhile Option.isSome = [] := by
    induction old <;> simp_all
  simp only [replace,empty,List.append_nil]

theorem replace_attachment (old fresh : List ρ) (payload : List (Option ρ)) :
    replace fresh (old.map some ++ none :: payload) = fresh.map some ++ none :: payload := by
  have rest : (old.map some ++ none :: payload).dropWhile Option.isSome = none :: payload := by
    induction old <;> simp_all
  simp only [replace,rest]

def graft (payload : α → Source β (List (Option ρ))) : Source α (List ρ) → Source β (List (Option ρ))
  | .leaf key records => (payload key).setRoot (records.map some ++ none :: (payload key).rootRecord)
  | .fork records l r => .fork (records.map some) (graft payload l) (graft payload r)

theorem graft_root_decode (payload : α → Source β (List (Option ρ))) (t : Source α (List ρ)) :
    decode (graft payload t).rootRecord = t.rootRecord := by
  cases t with
  | leaf key records =>
    unfold graft
    cases h : payload key <;> exact decode_attachment records _
  | fork records l r => exact decode_internal records

theorem graft_write (payload : α → Source β (List (Option ρ))) (t : Source α (List ρ)) (fresh : List ρ) :
    graft payload (t.setRoot fresh) = (graft payload t).setRoot (replace fresh (graft payload t).rootRecord) := by
  cases t with
  | leaf key records =>
    simp only [Source.setRoot,graft]
    cases hp : payload key <;>
      simp only [Source.setRoot,Source.rootRecord,replace_attachment]
  | fork records l r =>
    simp only [Source.setRoot,graft,Source.rootRecord,replace_internal]

def frame (payload : α → Source β (List (Option ρ))) : Frame α (List ρ) → Frame β (List (Option ρ))
  | .left records r => .left (records.map some) (graft payload r)
  | .right l records => .right (graft payload l) (records.map some)

def cursor (payload : α → Source β (List (Option ρ))) (c : Cursor α (List ρ)) : Cursor β (List (Option ρ)) :=
  ⟨graft payload c.focus,c.ancestors.map (frame payload)⟩

theorem step (payload : α → Source β (List (Option ρ))) {before after : Cursor α (List ρ)}
    (operation : Step before after) :
    ∃ reads cost, Trace (cursor payload before) reads (cursor payload after) cost ∧ cost ≤ 2 := by
  cases operation with
  | left => exact ⟨[],1,.step (.left _ _ _ _) (.nil _),by decide⟩
  | right => exact ⟨[],1,.step (.right _ _ _ _) (.nil _),by decide⟩
  | upLeft => exact ⟨[],1,.step (.upLeft _ _ _ _) (.nil _),by decide⟩
  | upRight => exact ⟨[],1,.step (.upRight _ _ _ _) (.nil _),by decide⟩
  | rotateRight => exact ⟨[],1,.step (.rotateRight _ _ _ _ _ _) (.nil _),by decide⟩
  | rotateLeft => exact ⟨[],1,.step (.rotateLeft _ _ _ _ _ _) (.nil _),by decide⟩
  | write focus fresh ancestors =>
    refine ⟨[(graft payload focus).rootRecord],2,?_,le_rfl⟩
    simpa only [cursor,graft_write] using
      write_charged (graft payload focus) (replace fresh (graft payload focus).rootRecord)
        (ancestors.map (frame payload))

theorem trace (payload : α → Source β (List (Option ρ)))
    {before after : Cursor α (List ρ)} {sourceReads : List (List ρ)} {sourceCost : Nat}
    (execution : Trace before sourceReads after sourceCost) :
    ∃ reads cost, Trace (cursor payload before) reads (cursor payload after) cost ∧ cost ≤ 2 * sourceCost := by
  induction execution with
  | nil => exact ⟨[],0,.nil _,Nat.zero_le _⟩
  | step operation rest ih =>
    obtain ⟨firstReads,firstCost,firstTrace,firstBound⟩ := step payload operation
    obtain ⟨lastReads,lastCost,lastTrace,lastBound⟩ := ih
    exact ⟨_,_,firstTrace.append lastTrace,by omega⟩
  | read rest ih =>
    obtain ⟨reads,cost,trace,bound⟩ := ih
    exact ⟨_,_,.read trace,by omega⟩

theorem rearranges (payload : α → Source β (List (Option ρ)))
    {before after : Source α (List ρ)} {budget : Nat}
    (execution : SourcePointer.Rearranges before after budget) :
    SourcePointer.Rearranges (graft payload before) (graft payload after) (2 * budget) := by
  intro outside
  obtain ⟨sourceReads,sourceCost,sourceTrace,sourceBound⟩ := execution []
  obtain ⟨reads,cost,physicalTrace,bound⟩ := trace payload sourceTrace
  exact ⟨reads,cost,physicalTrace.extend outside,bound.trans (Nat.mul_le_mul_left 2 sourceBound)⟩

theorem graft_leaves (payload : α → Source β (List (Option ρ))) (t : Source α (List ρ)) :
    (graft payload t).shape.leaves = t.shape.leaves.flatMap (fun key => (payload key).shape.leaves) := by
  induction t with
  | leaf key records =>
    simp only [graft,SourcePointer.source_setRoot_shape,Source.shape,RouterProjection.Router.leaves,
      List.flatMap_cons,List.flatMap_nil,List.append_nil]
  | fork records l r ihl ihr =>
    simp only [graft,Source.shape,RouterProjection.Router.leaves,List.flatMap_append,ihl,ihr]

end ChaCha.Paper20261030.SourcePayloads
