import ChaCha.Paper20261030.SplayAuxiliaryReferenceCore

/-!
# Exact indexed correspondence of source ports and preferred holes

The reference metadata and the raw BST invariant use the same inorder
port indices. No balancing or relabeling of physical separator keys is
involved in this correspondence.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ColoredStorage
open MultiSplay EndpointEncoding ClassicalSwitch Global Global.Preferred
open ChaCha.MTR.Pointer (MarkedTree)

variable {α ρ κ : Type*}

theorem referenceEntries_length (right : ρ → Bool) (reference : Source α ρ) :
    (referenceEntries right reference).length = (PathPorts.skeleton right reference).size+1 := by
  induction reference with
  | leaf => rfl
  | fork record l r ihl ihr =>
      cases direction : right record <;>
        simp [referenceEntries,PathPorts.skeleton,direction,MTR.Tree.size,ihl,ihr,Nat.add_comm]

theorem referenceEntries_port (right : ρ → Bool) (reference : Source α ρ)
    {i : Nat} {entry : ChaCha.Primary.Key × Source α ρ}
    (found : (referenceEntries right reference)[i]? = some entry) :
    entry.2 = PathPorts.port right reference i := by
  induction reference generalizing i entry with
  | leaf label record =>
      simp only [referenceEntries,List.getElem?_singleton] at found
      split at found
      · cases Option.some.inj found; rfl
      · contradiction
  | fork record l r ihl ihr =>
      cases direction : right record with
      | false =>
          simp only [referenceEntries,direction,Bool.false_eq_true,if_false] at found
          by_cases before : i < (referenceEntries right l).length
          · rw [List.getElem?_append_left (by simpa using before),List.getElem?_map] at found
            obtain ⟨e,child,same⟩ := Option.map_eq_some_iff.mp found
            subst entry
            have bound : i ≤ (PathPorts.skeleton right l).size := by
              rw [referenceEntries_length] at before; omega
            simpa only [PathPorts.port,direction,Bool.false_eq_true,if_false,if_pos bound]
              using ihl child
          · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_lt before),
              List.length_map,List.getElem?_singleton] at found
            split at found
            · rename_i index
              cases Option.some.inj found
              have bound : ¬ i ≤ (PathPorts.skeleton right l).size := by
                rw [referenceEntries_length] at before; omega
              simp only [PathPorts.port,direction,Bool.false_eq_true,if_false,if_neg bound]
            · contradiction
      | true =>
          simp only [referenceEntries,direction,if_true] at found
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero] at found
              cases Option.some.inj found
              simp only [PathPorts.port,direction,if_true]
          | succ i =>
              simp only [List.getElem?_cons_succ,List.getElem?_map] at found
              obtain ⟨e,child,same⟩ := Option.map_eq_some_iff.mp found
              subst entry
              simpa only [PathPorts.port,direction,if_true,Nat.succ_ne_zero,if_false,
                Nat.add_one_sub_one] using ihr child

theorem referencePort_entry (right : ρ → Bool) (reference : Source α ρ)
    (i : Nat) (bound : i ≤ (PathPorts.skeleton right reference).size) :
    ∃ address, (referenceEntries right reference)[i]? =
      some (address,PathPorts.port right reference i) := by
  have within : i < (referenceEntries right reference).length := by
    rw [referenceEntries_length]; omega
  have found := List.getElem?_eq_getElem within
  exact ⟨((referenceEntries right reference)[i]).1,
    by simpa only [← referenceEntries_port right reference found] using found⟩

theorem auxiliary_map_size (key : ρ → κ) (core : RawTree ρ) :
    (Auxiliary.map key core).size = core.size := by
  induction core <;> simp_all [Auxiliary.map,MTR.Tree.size]

theorem auxiliary_map_inorder (key : ρ → κ) (core : RawTree ρ) :
    (Auxiliary.map key core).inorder = core.inorder.map key := by
  induction core <;> simp_all [Auxiliary.map,MTR.Tree.inorder]

theorem referenceCuts_encode (key : ρ → κ) (core : RawTree ρ)
    (ports : Nat → Source α ρ) (base : Nat) :
    referenceCuts key (GapSource.encode core ports base) =
      MTR.Tree.graft (Auxiliary.map key core) (fun i => referenceCuts key (ports i)) base := by
  induction core generalizing base with
  | empty => rfl
  | node l record r ihl ihr =>
      simp only [GapSource.encode,referenceCuts,Auxiliary.map,MTR.Tree.graft,ihl,ihr,
        auxiliary_map_size]

theorem referenceCuts_encode_id (core : RawTree κ)
    (ports : Nat → Source α κ) (base : Nat) :
    referenceCuts id (GapSource.encode core ports base) =
      MTR.Tree.graft core (fun i => referenceCuts id (ports i)) base := by
  induction core generalizing base with
  | empty => rfl
  | node l record r ihl ihr =>
      simp only [GapSource.encode,referenceCuts,MTR.Tree.graft,ihl,ihr,id_eq]

/-- The raw marked tree obtained by erasing only source leaf payloads. -/
def markedSource (core : RawTree κ) (ports : Nat → Source α κ) : MarkedTree κ :=
  markedGraft core (fun i => referenceCuts id (ports i)) 0

@[simp] theorem markedSource_skeleton (core : RawTree κ) (ports : Nat → Source α κ) :
    (markedSource core ports).skeleton = core := markedGraft_skeleton _ _ _

@[simp] theorem markedSource_erase (core : RawTree κ) (ports : Nat → Source α κ) :
    (markedSource core ports).erase = referenceCuts id (GapSource.encode core ports 0) := by
  rw [markedSource,markedGraft_erase,referenceCuts_encode_id]

private theorem markedGraft_hole (core : RawTree κ) (ports : Nat → RawTree κ)
    (base i : Nat) (bound : i ≤ core.size) :
    (markedGraft core ports base).holes[i]? = some (ports (base+i)) := by
  induction core generalizing base i with
  | empty =>
      have zero : i = 0 := by simp only [MTR.Tree.size] at bound; omega
      subst i; rfl
  | node l record r ihl ihr =>
      simp only [markedGraft,MarkedTree.holes]
      by_cases left : i ≤ l.size
      · rw [List.getElem?_append_left (by
          rw [MarkedTree.holes_length,markedGraft_skeleton]; omega)]
        exact ihl base i left
      · rw [List.getElem?_append_right (by
          rw [MarkedTree.holes_length,markedGraft_skeleton]; omega),
          MarkedTree.holes_length,markedGraft_skeleton]
        have child := ihr (base+l.size+1) (i-(l.size+1)) (by
          simp only [MTR.Tree.size] at bound; omega)
        convert child using 1 <;> congr 2 <;> omega

@[simp] theorem markedSource_gapArray (core : RawTree κ) (ports : Nat → Source α κ)
    (i : Nat) (bound : i ≤ core.size) :
    (markedSource core ports).gapArray i = referenceCuts id (ports i) := by
  simp only [markedSource,MarkedTree.gapArray,
    markedGraft_hole core (fun i => referenceCuts id (ports i)) 0 i bound,
    Nat.zero_add,Option.getD_some]

end ChaCha.Paper20261030.SplayAuxiliary
