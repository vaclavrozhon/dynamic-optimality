import ChaCha.Paper20261030.SplayAuxiliaryReferencePorts
import ChaCha.Paper20261030.SplayAuxiliaryDecomposition
import ChaCha.Paper20261030.SourceRecordMap

/-!
# Equivalence of the source and ordinary-BST component invariants

Ghost reference records are mapped to physical separator keys. The adapter
preserves the entire physical BST, including all hanging components; it
changes neither auxiliary shapes nor the persistent potential inventory.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ColoredStorage
open MultiSplay EndpointEncoding ClassicalSwitch Global Global.Preferred
open ChaCha.MTR.Pointer (MarkedTree)
open RawComponent Decomposition

variable {α ρ κ : Type*}

theorem represented_realizes {key : ρ → κ} {right : ρ → Bool}
    {reference : Source α ρ} {c : RawComponent α κ}
    (represented : Represents key right reference c) :
    Realizes (referenceState right reference) (referenceCuts key reference)
      (referenceCuts id c.closed) := by
  cases hreference : reference with
  | leaf label record =>
      rw [hreference] at represented
      rw [represented.closed_leaf]
      exact .empty _
  | fork record l r =>
      rw [hreference] at represented
      have result : Component (referenceState right (.fork record l r))
          (referenceCuts key (.fork record l r)) (markedSource c.core c.ports) := by
        refine ⟨?_,?_⟩
        · rw [markedSource_skeleton,preferred_referenceCuts,auxiliary_map_inorder]
          exact represented.word
        · intro i entry found
          rw [← referenceEntries_raw, List.getElem?_map] at found
          obtain ⟨sourceEntry,sourceFound,same⟩ := Option.map_eq_some_iff.mp found
          subst entry
          have bound : i ≤ c.core.size := by
            obtain ⟨within,_⟩ := List.getElem?_eq_some_iff.mp sourceFound
            rw [referenceEntries_length,← represented.size] at within
            omega
          obtain ⟨child,childRep,childPort⟩ := represented.port_represented i bound
          have portEq := referenceEntries_port right (.fork record l r) sourceFound
          rw [← portEq] at childRep
          rw [markedSource_gapArray _ _ _ bound,childPort]
          rw [← referenceEntries_state right (.fork record l r) (List.mem_of_getElem? sourceFound)]
          exact represented_realizes childRep
      simpa only [markedSource_erase,closed] using result.realizes
termination_by (referenceCuts key reference).size
decreasing_by
  simp only [hreference]
  exact referenceEntries_smaller key right record l r (List.mem_of_getElem? sourceFound)

theorem represented_component {key : ρ → κ} {right : ρ → Bool}
    {reference : Source α ρ} {c : RawComponent α κ}
    (represented : Represents key right reference c) :
    Component (referenceState right reference) (referenceCuts key reference)
      (markedSource c.core c.ports) := by
  refine ⟨?_,?_⟩
  · rw [markedSource_skeleton,preferred_referenceCuts,auxiliary_map_inorder]
    exact represented.word
  · intro i entry found
    rw [← referenceEntries_raw,List.getElem?_map] at found
    obtain ⟨sourceEntry,sourceFound,same⟩ := Option.map_eq_some_iff.mp found
    subst entry
    have bound : i ≤ c.core.size := by
      obtain ⟨within,_⟩ := List.getElem?_eq_some_iff.mp sourceFound
      rw [referenceEntries_length,← represented.size] at within
      omega
    obtain ⟨child,childRep,childPort⟩ := represented.port_represented i bound
    have portEq := referenceEntries_port right reference sourceFound
    rw [← portEq] at childRep
    rw [markedSource_gapArray _ _ _ bound,childPort]
    rw [← referenceEntries_state right reference (List.mem_of_getElem? sourceFound)]
    exact represented_realizes childRep

/-- Recover source payloads from an arbitrary physically realized component
without changing any of its actual BST nodes. -/
theorem realizes_represented (key : ρ → κ) (right : ρ → Bool)
    (reference : Source α ρ) {physical : RawTree κ}
    (represented : Realizes (referenceState right reference) (referenceCuts key reference) physical) :
    ∃ c : RawComponent α κ, Represents key right reference c ∧
      referenceCuts id c.closed = physical := by
  classical
  cases hreference : reference with
  | leaf label record =>
      rw [hreference] at represented
      refine ⟨terminal (.leaf label (key record)),.leaf (.refl _),?_⟩
      exact represented.empty_eq.symm
  | fork record l r =>
      rw [hreference] at represented
      obtain ⟨actual,physicalEq,component⟩ := represented.expose
      have word : actual.skeleton.inorder =
          (PathPorts.skeleton right (.fork record l r)).inorder.map key := by
        simpa only [preferred_referenceCuts,auxiliary_map_inorder] using component.1
      have size : actual.skeleton.size = (PathPorts.skeleton right (.fork record l r)).size := by
        rw [← MTR.Tree.length_inorder,word,List.length_map,MTR.Tree.length_inorder]
      have children : ∀ i, i ≤ actual.skeleton.size → ∃ c : RawComponent α κ,
          Represents key right (PathPorts.port right (.fork record l r) i) c ∧
          referenceCuts id c.closed = actual.gapArray i := by
        intro i bound
        obtain ⟨address,found⟩ := referencePort_entry right (.fork record l r) i (by omega)
        have rawFound : (preferredHoles (referenceState right (.fork record l r))
            (referenceCuts key (.fork record l r)))[i]? =
            some (address,referenceCuts key (PathPorts.port right (.fork record l r) i)) := by
          rw [← referenceEntries_raw,List.getElem?_map,found]
          rfl
        have childRep := component.2 i _ rawFound
        rw [← referenceEntries_state right (.fork record l r) (List.mem_of_getElem? found)] at childRep
        exact realizes_represented key right (PathPorts.port right (.fork record l r) i) childRep
      let ports : Nat → Source α κ := fun i =>
        if bound : i ≤ actual.skeleton.size then (Classical.choose (children i bound)).closed
        else (Source.fork record l r).mapRecords key
      let c : RawComponent α κ := ⟨actual.skeleton,ports⟩
      have portSpec (i : Nat) (bound : i ≤ actual.skeleton.size) :
          ∃ child : RawComponent α κ,
            Represents key right (PathPorts.port right (.fork record l r) i) child ∧
            ports i = child.closed ∧ referenceCuts id (ports i) = actual.gapArray i := by
        refine ⟨Classical.choose (children i bound),(Classical.choose_spec (children i bound)).1,?_,?_⟩
        · simp only [ports,dif_pos bound]
        · simpa only [ports,dif_pos bound] using (Classical.choose_spec (children i bound)).2
      refine ⟨c,represents_of_word_ports key right (.fork record l r) c word ?_,?_⟩
      · intro i bound
        obtain ⟨child,childRep,childEq,_⟩ := portSpec i bound
        exact ⟨child,childRep,childEq⟩
      · change referenceCuts id (GapSource.encode actual.skeleton ports 0) = physical
        rw [referenceCuts_encode_id]
        calc
          MTR.Tree.graft actual.skeleton (fun i => referenceCuts id (ports i)) 0 = actual.erase := by
            apply actual.graft_skeleton
            intro i within
            have bound : i ≤ actual.skeleton.size := by rw [MarkedTree.holes_length] at within; omega
            obtain ⟨_,_,_,same⟩ := portSpec i bound
            simpa only [Nat.zero_add,MarkedTree.gapArray,List.getElem?_eq_getElem within,
              Option.getD_some] using same
          _ = physical := physicalEq
termination_by (referenceCuts key reference).size
decreasing_by
  simp only [hreference]
  exact referenceEntries_smaller key right record l r (List.mem_of_getElem? found)

/-- Exact equivalence, with source labels retained as ghost leaf payloads. -/
theorem source_realization_iff (key : ρ → κ) (right : ρ → Bool)
    (reference : Source α ρ) (physical : RawTree κ) :
    Realizes (referenceState right reference) (referenceCuts key reference) physical ↔
      ∃ c : RawComponent α κ, Represents key right reference c ∧
        referenceCuts id c.closed = physical := by
  constructor
  · exact realizes_represented key right reference
  · rintro ⟨c,represented,rfl⟩
    exact represented_realizes represented

end ChaCha.Paper20261030.SplayAuxiliary
