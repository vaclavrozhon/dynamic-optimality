import ChaCha.Paper20261030.SplayAuxiliaryPreparedExecution
import ChaCha.Paper20261030.CompletePhysicalHeadExchange
import ChaCha.Paper20261030.CompletePhysicalRootExchange

/-!
# Original-key physical execution of a prepared splay exchange

The old and incoming auxiliaries are exposed by their actual bottom-up
splays. The existing constant-size two-color exchange then gives the
physical BST operation. The chosen output shapes require no rebuilding.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open ColoredStorage SecondaryDecomposition RawComponent Decomposition PreferredProjection
open PrimaryWings PackedPrimary

variable {α τ : Type*} [DecidableEq α]

 theorem PreparedExecution.physical {b d : Nat} (reference : DepthTree 0 b)
    (p q : DepthSplit → Bool) (valid : 0 ≤ d ∧ d ≤ b)
    {active incomingComponent out parked : RawComponent Nat Nat} {work : Nat}
    (activeRep : Represents cutKey followsRight (source reference p) active)
    (incomingRep : Represents cutKey followsRight (suffixSource reference q d valid) incomingComponent)
    (execution : PreparedExecution active incomingComponent d out parked work)
    {x : α} {before after : PrefRouter α} (step : PrefRouter.HeadStep x d before after)
    (distinct : before.leaves.Nodup) (values : Nat → τ)
    (payload : Exit α → Source α (List (Option τ)))
    (headers : Nat → PrefRouter α → Source Nat Nat → List τ) :
    ∃ (old incoming : PrefRouter α) (direction : Bool),
      portAt 0 (exits before) d = some ⟨direction,incoming⟩ ∧
      portAt 0 (exits after) d = some ⟨!direction,old⟩ ∧
      SourcePointer.Rearranges
        (nestedTree values payload headers before incoming direction d active.closed incomingComponent.closed)
        (nestedTree values payload headers after old (!direction) d out.closed parked.closed)
        (204*work+716) := by
  have afterDistinct : after.leaves.Nodup := by rw [step.leaves]; exact distinct
  cases execution with
  | @interior d left suffix oldTail newTail splitWork oldWork incomingWork positive split oldSplay incomingSplay oldExpose incomingExpose incomingPort oldPort =>
      obtain ⟨common,old,incoming,direction,length,oldEnd,newEnd,beforeWord,afterWord⟩ := head_exit_decomposition step
      cases length
      have intervals := exposed_depth_partition reference p common.length activeRep oldExpose
      have incomingIntervals := exposed_suffix_partition reference q common.length valid incomingRep incomingExpose
      have newClosed :
          (RawComponent.join (prefixPart left active.ports) (common.length-1)
            ⟨.node .empty common.length newTail,incomingComponent.ports⟩).closed =
          .fork (common.length-1) (prefixPart left active.ports).closed
            (.fork common.length (.leaf common.length common.length)
              (GapSource.encode newTail incomingComponent.ports 1)) := by
        rw [join_closed]
        simp only [closed,GapSource.encode,MTR.Tree.size,Nat.zero_add,incomingPort]
      have oldClosed :
          (RawComponent.mk (.node .empty common.length oldTail)
            (RawComponent.suffix left suffix active.ports).ports).closed =
          .fork common.length (.leaf common.length common.length)
            (GapSource.encode oldTail (RawComponent.suffix left suffix active.ports).ports 1) := by
        simp only [closed,GapSource.encode,MTR.Tree.size,Nat.zero_add,oldPort]
      refine ⟨old,incoming,direction,?_,?_,?_⟩
      · rw [beforeWord]; exact portAt_boundary _ _ _
      · rw [afterWord]; exact portAt_boundary _ _ _
      · have physical := complete_physical_head_exchange before after old incoming common direction
          distinct afterDistinct oldEnd newEnd beforeWord afterWord values
          (prefixPart left active.ports).closed
          (GapSource.encode oldTail (RawComponent.suffix left suffix active.ports).ports 1)
          (GapSource.encode newTail incomingComponent.ports 1)
          intervals.1 intervals.2 incomingIntervals
          (common.length-1) common.length common.length common.length payload headers
          active.closed incomingComponent.closed _ _
          (3*(splitWork+oldWork)+4) (3*incomingWork+1) 0 0
          oldExpose incomingExpose (SourcePointer.rearranges_refl _ 0) (SourcePointer.rearranges_refl _ 0)
        rw [← newClosed,← oldClosed] at physical
        exact physical.mono (by omega)
  | @minimum oldTail newTail oldWork incomingWork oldSplay incomingSplay oldExpose incomingExpose incomingPort oldPort =>
      obtain ⟨common,old,incoming,direction,length,oldEnd,newEnd,beforeWord,afterWord⟩ := head_exit_decomposition step
      have empty : common = [] := by simpa using length
      subst common
      have activeSuffix : Represents cutKey followsRight (suffixSource reference p 0 valid) active := by
        simpa only [suffixSource_minimum] using activeRep
      have oldIntervals := exposed_suffix_partition reference p 0 valid activeSuffix oldExpose
      have incomingIntervals := exposed_suffix_partition reference q 0 valid incomingRep incomingExpose
      have newClosed : (RawComponent.mk (.node .empty 0 newTail) incomingComponent.ports).closed =
          .fork 0 (.leaf 0 0) (GapSource.encode newTail incomingComponent.ports 1) := by
        simp only [closed,GapSource.encode,MTR.Tree.size,Nat.zero_add,incomingPort]
      have oldClosed : (RawComponent.mk (.node .empty 0 oldTail) active.ports).closed =
          .fork 0 (.leaf 0 0) (GapSource.encode oldTail active.ports 1) := by
        simp only [closed,GapSource.encode,MTR.Tree.size,Nat.zero_add,oldPort]
      refine ⟨old,incoming,direction,?_,?_,?_⟩
      · rw [beforeWord]; exact portAt_boundary [] _ _
      · rw [afterWord]; exact portAt_boundary [] _ _
      · have physical := complete_physical_root_exchange before after old incoming direction
          distinct afterDistinct oldEnd newEnd beforeWord afterWord values
          (GapSource.encode oldTail active.ports 1) (GapSource.encode newTail incomingComponent.ports 1)
          oldIntervals incomingIntervals 0 0 0 payload headers active.closed incomingComponent.closed _ _
          (3*oldWork+1) (3*incomingWork+1) 0 0
          oldExpose incomingExpose (SourcePointer.rearranges_refl _ 0) (SourcePointer.rearranges_refl _ 0)
        rw [← newClosed,← oldClosed] at physical
        exact physical.mono (by omega)

end ChaCha.Paper20261030.SplayAuxiliary
