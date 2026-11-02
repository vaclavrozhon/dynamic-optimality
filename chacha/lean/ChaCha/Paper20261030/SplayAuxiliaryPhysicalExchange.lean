import ChaCha.Paper20261030.SplayAuxiliaryPhysicalViews
import ChaCha.Paper20261030.SplayAuxiliaryPreparedPhysical

/-! The local ordinary-splay head exchange acts on the complete original-key
physical state. All unrelated endpoint components remain literally unchanged. -/

namespace ChaCha.Paper20261030.SplayAuxiliary.Physical

open ColoredStorage SecondaryDecomposition Decomposition
open PreferredProjection PrimaryWings PackedPrimary PrimaryPhysical

variable {α : Type*} [DecidableEq α]

theorem maintained_prepared_exchange {height depth : Nat} (reference : DepthTree 0 height)
    (p q : DepthSplit → Bool) (upper : depth < height)
    {x : α} {before after : PrefRouter α} (step : PrefRouter.HeadStep x depth before after)
    (distinct : before.leaves.Nodup) (perfect : before.Perfect height) (components : Global.Table α)
    (activeOut parked : Global.Component) (work : Nat)
    (activeRep : Represents cutKey followsRight (source reference p) (components before.terminal).auxiliary)
    (incomingRep : Represents cutKey followsRight
      (suffixSource reference q depth ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) (components after.terminal).auxiliary)
    (outRep : Represents cutKey followsRight (source reference (Secondary.spliceBits depth p q)) activeOut.auxiliary)
    (parkedRep : Represents cutKey followsRight
      (suffixSource reference p depth ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) parked.auxiliary)
    (ordinary : PreparedExecution (components before.terminal).auxiliary (components after.terminal).auxiliary
      depth activeOut.auxiliary parked.auxiliary work) :
    SourcePointer.Rearranges (physicalState before components)
      (physicalState after (Function.update (Function.update components before.terminal parked) after.terminal activeOut))
      (204*work+716) := by
  let updated := Function.update (Function.update components before.terminal parked) after.terminal activeOut
  let payload := storedPayload before.componentStart components
  obtain ⟨old,incoming,direction,oldPort,newPort,execution⟩ :=
    ordinary.physical reference p q ⟨Nat.zero_le _,Nat.le_of_lt upper⟩ activeRep incomingRep step distinct
      Datum.record payload canonicalHeaders
  have afterPerfect := step.perfect perfect
  have beforeValid := (active_input before reference p (components before.terminal) activeRep
    (perfect_exits_length perfect)).leaves
  have incomingValid := (dormant_input incoming reference (Nat.zero_lt_succ depth) (by omega) q
    (components after.terminal) incomingRep (perfect_port_length perfect oldPort)).leaves
  have afterValid := (active_input after reference (Secondary.spliceBits depth p q) activeOut outRep
    (perfect_exits_length afterPerfect)).leaves
  have oldValid := (dormant_input old reference (Nat.zero_lt_succ depth) (by omega) p parked parkedRep
    (perfect_port_length afterPerfect newPort)).leaves
  change ValidInput 0 before (closed (components before.terminal)) at beforeValid
  change ValidInput (depth+1) incoming (closed (components after.terminal)) at incomingValid
  change ValidInput 0 after (closed activeOut) at afterValid
  change ValidInput (depth+1) old (closed parked) at oldValid
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
      nestedTree Datum.record payload canonicalHeaders after old (!direction) depth (closed activeOut) (closed parked) := by
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


end ChaCha.Paper20261030.SplayAuxiliary.Physical
