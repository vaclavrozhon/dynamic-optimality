import ChaCha.Paper20261030.CompletePhysicalHeadExchange
import ChaCha.Paper20261030.CompletePhysicalRootExchange
import ChaCha.Paper20261030.PreparedSourceIntervals

/-!
# The complete physical trace of an actual prepared primary head step

For every boundary depth, including zero, the maintained secondary decompositions
produce the exact exposed fragments. Their leaf intervals give the port
agreements, and the physical trace includes all exposures, the exchange,
and both reconstructions. The result uses the exact `exchange` outputs.

The bound is linear in the logarithm of the secondary reference height.
Headers are supplied explicitly; local acquisition of their contents and
the complete online controller are not asserted by this trace theorem.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition
open PreferredProjection PrimaryWings PackedPrimary

variable {α τ : Type*} [DecidableEq α]

theorem prepared_physical_head_exchange_pos {b : Nat} (reference : DepthTree 0 b)
    (p q : DepthSplit → Bool) (d : Nat) (lower : 0 < d) (upper : d < b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = d)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = d)
    (active incomingComponent : AuxiliaryComponent Nat Nat (Tagged Payload))
    (activeRep : Represents followsRight (source reference p) active)
    (incomingRep : Represents followsRight
      (suffixSource reference q d ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) incomingComponent)
    {x : α} {before after : PrefRouter α} (step : PrefRouter.HeadStep x d before after)
    (distinct : before.leaves.Nodup) (values : Cached → τ)
    (payload : Exit α → Source α (List (Option τ)))
    (headers : Nat → PrefRouter α → Source Nat Cached → List τ) :
    ∃ (old incoming : PrefRouter α) (direction : Bool),
      portAt 0 (exits before) d = some ⟨direction,incoming⟩ ∧
      portAt 0 (exits after) d = some ⟨!direction,old⟩ ∧
      let out := exchange reference p d preparedP active incomingComponent activeRep
      SourcePointer.Rearranges
        (nestedTree values payload headers before incoming direction d (closed active) (closed incomingComponent))
        (nestedTree values payload headers after old (!direction) d (closed out.1) (closed out.2))
        (2016000*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+8000) ∧
      Represents followsRight (source reference (Secondary.spliceBits d p q)) out.1 ∧
      Represents followsRight (suffixSource reference p d ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) out.2 := by
  obtain ⟨common,old,incoming,direction,length,oldEnd,newEnd,beforeWord,afterWord⟩ := head_exit_decomposition step
  cases length
  obtain ⟨headPart,oldRest,incomingRest,low,oldHigh,incomingHigh,oldExpose,incomingExpose,newRestore,oldRestore,newRep,oldRep⟩ :=
    prepared_head_views reference p q common.length lower upper preparedP preparedQ active incomingComponent activeRep incomingRep
  have intervals := exposed_source_intervals reference p common.length active activeRep
    (closed headPart) oldRest.tree low oldHigh _ oldExpose
  have incomingIntervals := exposed_sentinel_partition reference q common.length
    ⟨Nat.zero_le _,Nat.le_of_lt upper⟩ incomingComponent incomingRest incomingRep incomingHigh _ incomingExpose
  have afterDistinct : after.leaves.Nodup := by rw [step.leaves]; exact distinct
  refine ⟨old,incoming,direction,?_,?_,?_,newRep,oldRep⟩
  · rw [beforeWord]; exact portAt_boundary _ _ _
  · rw [afterWord]; exact portAt_boundary _ _ _
  · have result := complete_physical_head_exchange before after old incoming common direction distinct afterDistinct
      oldEnd newEnd beforeWord afterWord values (closed headPart) oldRest.tree incomingRest.tree
      intervals.1 intervals.2 incomingIntervals.2 low oldHigh incomingHigh (terminalLeaf common.length).rootRecord
      payload headers (closed active) (closed incomingComponent) _ _ _ _ _ _
      oldExpose incomingExpose newRestore oldRestore
    exact result.mono (by omega)

theorem prepared_physical_root_exchange {b : Nat} (reference : DepthTree 0 b)
    (p q : DepthSplit → Bool) (upper : 0 < b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = 0)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = 0)
    (active incomingComponent : AuxiliaryComponent Nat Nat (Tagged Payload))
    (activeRep : Represents followsRight (source reference p) active)
    (incomingRep : Represents followsRight
      (suffixSource reference q 0 ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) incomingComponent)
    {x : α} {before after : PrefRouter α} (step : PrefRouter.HeadStep x 0 before after)
    (distinct : before.leaves.Nodup) (values : Cached → τ)
    (payload : Exit α → Source α (List (Option τ)))
    (headers : Nat → PrefRouter α → Source Nat Cached → List τ) :
    ∃ (old incoming : PrefRouter α) (direction : Bool),
      portAt 0 (exits before) 0 = some ⟨direction,incoming⟩ ∧
      portAt 0 (exits after) 0 = some ⟨!direction,old⟩ ∧
      let out := exchange reference p 0 preparedP active incomingComponent activeRep
      SourcePointer.Rearranges
        (nestedTree values payload headers before incoming direction 0 (closed active) (closed incomingComponent))
        (nestedTree values payload headers after old (!direction) 0 (closed out.1) (closed out.2))
        (2016000*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+8000) ∧
      Represents followsRight (source reference (Secondary.spliceBits 0 p q)) out.1 ∧
      Represents followsRight (suffixSource reference p 0 ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) out.2 := by
  obtain ⟨common,old,incoming,direction,length,oldEnd,newEnd,beforeWord,afterWord⟩ := head_exit_decomposition step
  have empty : common = [] := by simpa using length
  subst common
  obtain ⟨oldRest,incomingRest,oldHigh,incomingHigh,oldExpose,incomingExpose,newRestore,oldRestore,newRep,oldRep⟩ :=
    prepared_head_views_zero reference p q upper preparedP preparedQ active incomingComponent activeRep incomingRep
  have oldSuffixRep : Represents followsRight
      (suffixSource reference p 0 ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) active := by
    simpa only [suffixSource_minimum] using activeRep
  have oldIntervals := exposed_sentinel_partition reference p 0
    ⟨Nat.zero_le _,Nat.le_of_lt upper⟩ active oldRest oldSuffixRep oldHigh _ oldExpose
  have incomingIntervals := exposed_sentinel_partition reference q 0
    ⟨Nat.zero_le _,Nat.le_of_lt upper⟩ incomingComponent incomingRest incomingRep incomingHigh _ incomingExpose
  have afterDistinct : after.leaves.Nodup := by rw [step.leaves]; exact distinct
  refine ⟨old,incoming,direction,?_,?_,?_,newRep,oldRep⟩
  · rw [beforeWord]; exact portAt_boundary [] _ _
  · rw [afterWord]; exact portAt_boundary [] _ _
  · have result := complete_physical_root_exchange before after old incoming direction distinct afterDistinct
      oldEnd newEnd beforeWord afterWord values oldRest.tree incomingRest.tree oldIntervals.2 incomingIntervals.2
      oldHigh incomingHigh (terminalLeaf 0).rootRecord payload headers (closed active) (closed incomingComponent)
      _ _ _ _ _ _ oldExpose incomingExpose newRestore oldRestore
    exact result.mono (by omega)

theorem prepared_physical_head_exchange {b : Nat} (reference : DepthTree 0 b)
    (p q : DepthSplit → Bool) (d : Nat) (upper : d < b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = d)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = d)
    (active incomingComponent : AuxiliaryComponent Nat Nat (Tagged Payload))
    (activeRep : Represents followsRight (source reference p) active)
    (incomingRep : Represents followsRight
      (suffixSource reference q d ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) incomingComponent)
    {x : α} {before after : PrefRouter α} (step : PrefRouter.HeadStep x d before after)
    (distinct : before.leaves.Nodup) (values : Cached → τ)
    (payload : Exit α → Source α (List (Option τ)))
    (headers : Nat → PrefRouter α → Source Nat Cached → List τ) :
    ∃ (old incoming : PrefRouter α) (direction : Bool),
      portAt 0 (exits before) d = some ⟨direction,incoming⟩ ∧
      portAt 0 (exits after) d = some ⟨!direction,old⟩ ∧
      let out := exchange reference p d preparedP active incomingComponent activeRep
      SourcePointer.Rearranges
        (nestedTree values payload headers before incoming direction d (closed active) (closed incomingComponent))
        (nestedTree values payload headers after old (!direction) d (closed out.1) (closed out.2))
        (2016000*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+8000) ∧
      Represents followsRight (source reference (Secondary.spliceBits d p q)) out.1 ∧
      Represents followsRight (suffixSource reference p d ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) out.2 := by
  cases d with
  | zero =>
    exact prepared_physical_root_exchange reference p q upper preparedP preparedQ active incomingComponent
      activeRep incomingRep step distinct values payload headers
  | succ d =>
    exact prepared_physical_head_exchange_pos reference p q (d+1) (Nat.zero_lt_succ _) upper
      preparedP preparedQ active incomingComponent activeRep incomingRep step distinct values payload headers

end ChaCha.Paper20261030.SecondaryDecomposition
