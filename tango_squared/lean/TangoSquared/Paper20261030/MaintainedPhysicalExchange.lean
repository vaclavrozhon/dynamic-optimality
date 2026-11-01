import TangoSquared.Paper20261030.NestedPhysicalState

/-!
# Prepared head exchange on the complete maintained physical state

The two affected component entries are replaced by the exact cut/join
outputs. All other entries and their original-key subtrees are retained.
The local nested-tree trace therefore composes as a trace of the complete
physical representation, with the same charged cost.
-/

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open ColoredStorage AuxiliaryComponent BoundaryObservations PathDecomposition
open PreferredProjection PrimaryWings PackedPrimary PrimaryPhysical

variable {α : Type*} [DecidableEq α]

theorem maintained_prepared_exchange {height depth : Nat} (reference : DepthTree 0 height)
    (p q : DepthSplit → Bool) (upper : depth < height)
    (preparedP : (Secondary.decodeDepth reference p).terminal = depth)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = depth)
    {x : α} {before after : PrefRouter α} (step : PrefRouter.HeadStep x depth before after)
    (distinct : before.leaves.Nodup) (perfect : before.Perfect height) (components : Components α)
    (activeRep : Represents followsRight (source reference p) (components before.terminal))
    (incomingRep : Represents followsRight
      (suffixSource reference q depth ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) (components after.terminal)) :
    let out := exchange reference p depth preparedP (components before.terminal) (components after.terminal) activeRep
    SourcePointer.Rearranges (physicalState before components)
      (physicalState after (Function.update (Function.update components before.terminal out.2) after.terminal out.1))
      (2016000*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+8000) := by
  dsimp only
  let out := exchange reference p depth preparedP (components before.terminal) (components after.terminal) activeRep
  let updated := Function.update (Function.update components before.terminal out.2) after.terminal out.1
  let payload := storedPayload before.componentStart components
  obtain ⟨old,incoming,direction,oldPort,newPort,beforeValid,incomingValid,afterValid,oldValid,execution,_,_⟩ :=
    canonical_prepared_exchange reference p q depth upper preparedP preparedQ
      (components before.terminal) (components after.terminal) activeRep incomingRep step distinct perfect payload
  obtain ⟨oldEnd,newEnd⟩ := head_boundary_terminals step oldPort newPort
  have endpoints := step.endpoints_ne distinct
  have afterDistinct : after.leaves.Nodup := by rw [step.leaves]; exact distinct
  have oldMember : (⟨!direction,old⟩ : Exit α) ∈ exits after :=
    List.mem_of_getElem? (by simpa [portAt] using newPort)
  have sameEntries : ∀ key, key ≠ before.terminal → key ≠ after.terminal → components key = updated key := by
    intro key oldOther newOther
    simp only [updated,Function.update_of_ne newOther,Function.update_of_ne oldOther]
  have beforeView : physicalState before components =
      nestedTree Datum.record payload canonicalHeaders before incoming direction depth
        (closed (components before.terminal)) (closed (components after.terminal)) := by
    have view := storedTree_as_nested before.componentStart components before incoming direction depth
      (PrefRouter.componentStart_terminal before) (port_endpoint_start distinct oldPort) beforeValid
      (by simpa only [← newEnd] using incomingValid) payload (fun _ _ _ => rfl) (fun _ _ => rfl)
    simpa only [physicalState,← newEnd] using view
  have outerSame : ∀ exit ∈ exits after, exit ≠ ⟨!direction,old⟩ →
      storedPayload after.componentStart updated exit = payload exit := by
    intro exit member different
    have outsideOld : before.terminal ∉ exit.subtree.leaves := by
      intro inside
      have disjoint := exit_leaves_disjoint afterDistinct member oldMember different
      exact disjoint _ inside (oldEnd ▸ old.terminal_mem)
    have outsideNew := exit_excludes_terminal afterDistinct member
    exact (storedTree_head_frame step components updated outsideOld outsideNew sameEntries).symm
  have innerSame : ∀ exit ∈ exits old, storedPayload after.componentStart updated exit = payload exit := by
    intro exit member
    have oldDistinct := exit_leaves_nodup afterDistinct oldMember
    have outsideOld : before.terminal ∉ exit.subtree.leaves := by
      rw [oldEnd]
      exact exit_excludes_terminal oldDistinct member
    have outsideNew : after.terminal ∉ exit.subtree.leaves := by
      intro inside
      exact exit_excludes_terminal afterDistinct oldMember (exit_leaves_subset member _ inside)
    exact (storedTree_head_frame step components updated outsideOld outsideNew sameEntries).symm
  have afterView : physicalState after updated =
      nestedTree Datum.record payload canonicalHeaders after old (!direction) depth (closed out.1) (closed out.2) := by
    have outerValid : ValidInput 0 after (closed (updated after.terminal)) := by
      simpa only [updated,Function.update_self] using afterValid
    have innerValid : ValidInput (depth+1) old (closed (updated old.terminal)) := by
      simpa only [updated,← oldEnd,Function.update_of_ne endpoints,Function.update_self] using oldValid
    have view := storedTree_as_nested after.componentStart updated after old (!direction) depth
      (PrefRouter.componentStart_terminal after) (port_endpoint_start afterDistinct newPort)
      outerValid innerValid payload outerSame innerSame
    simpa only [physicalState,updated,← oldEnd,Function.update_self,Function.update_of_ne endpoints] using view
  change SourcePointer.Rearranges (physicalState before components) (physicalState after updated) _
  rw [beforeView,afterView]
  exact execution

end TangoSquared.Paper20261030.SecondaryDecomposition
