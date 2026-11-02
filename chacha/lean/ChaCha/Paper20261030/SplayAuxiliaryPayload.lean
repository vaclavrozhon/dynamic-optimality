import ChaCha.Paper20261030.SplayAuxiliaryReferencePorts
import ChaCha.Paper20261030.SplayAuxiliaryDecomposition
import ChaCha.Paper20261030.SourceRecordMap

/-!
# Original leaf payloads determine the source above a raw BST

A raw separator tree forgets the records stored at its inorder leaves.
The invariant retains their complete ordered word, so recovering a source
from its physical raw tree never invents or changes a payload.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ColoredStorage RawComponent Decomposition

variable {α ρ κ : Type*}

def leafPayloads : Source α ρ → List (α × ρ)
  | .leaf label record => [(label,record)]
  | .fork _ l r => leafPayloads l ++ leafPayloads r

theorem leafPayloads_length (source : Source α ρ) :
    (leafPayloads source).length = (referenceCuts id source).size+1 := by
  induction source <;> simp_all [leafPayloads,referenceCuts,MTR.Tree.size] <;> omega

theorem leafPayloads_map (key : ρ → κ) (source : Source α ρ) :
    leafPayloads (source.mapRecords key) = (leafPayloads source).map (fun e => (e.1,key e.2)) := by
  induction source <;> simp_all [leafPayloads,Source.mapRecords]

theorem leafPayloads_encode (core : RawTree ρ) (ports : Nat → Source α ρ) (base : Nat) :
    leafPayloads (GapSource.encode core ports base) =
      (List.range' base (core.size+1)).flatMap (fun i => leafPayloads (ports i)) := by
  induction core generalizing base with
  | empty => simp [GapSource.encode,leafPayloads,MTR.Tree.size,List.range']
  | node l record r ihl ihr =>
      simp only [GapSource.encode,leafPayloads,ihl,ihr,MTR.Tree.size]
      have size : l.size+1+r.size+1 = (l.size+1)+(r.size+1) := by omega
      rw [size]
      symm
      rw [← List.range'_append_1,List.flatMap_append]
      simp only [Nat.add_assoc]

theorem leafPayloads_closed (c : RawComponent α κ) :
    leafPayloads c.closed = c.portWord.flatMap leafPayloads := by
  simp only [closed,leafPayloads_encode,portWord,List.flatMap_map,Function.comp_def,
    ← List.range_eq_range']

theorem RawComponent.Equivalent.leafPayloads {a b : RawComponent α κ} (same : Equivalent a b) :
    leafPayloads a.closed = leafPayloads b.closed := by
  simp only [leafPayloads_closed,same.portWord]

theorem represented_leafPayloads {key : ρ → κ} {right : ρ → Bool}
    {reference : Source α ρ} {c : RawComponent α κ}
    (represented : Represents key right reference c) :
    leafPayloads c.closed = leafPayloads (reference.mapRecords key) := by
  induction represented with
  | leaf same => exact same.leafPayloads
  | left direction left right same ihl ihr =>
      rw [same.leafPayloads,append_closed]
      simp only [leafPayloads,ihl,ihr,Source.mapRecords]
  | right direction left right same ihl ihr =>
      rw [same.leafPayloads,prepend_closed]
      simp only [leafPayloads,ihl,ihr,Source.mapRecords]

/-- Full source equality from the physical separator tree and the exact
ordered payloads at its leaves. -/
theorem source_ext {a b : Source α κ}
    (physical : referenceCuts id a = referenceCuts id b)
    (payloads : leafPayloads a = leafPayloads b) : a = b := by
  induction a generalizing b with
  | leaf label record =>
      cases b with
      | leaf other value => simpa only [leafPayloads,List.singleton_inj,Prod.mk.injEq,
          Source.leaf.injEq] using payloads
      | fork => cases physical
  | fork record l r ihl ihr =>
      cases b with
      | leaf => cases physical
      | fork other l' r' =>
          simp only [referenceCuts,id_eq,MTR.Tree.node.injEq] at physical
          obtain ⟨leftEq,rfl,rightEq⟩ := physical
          have length : (leafPayloads l).length = (leafPayloads l').length := by
            rw [leafPayloads_length,leafPayloads_length,leftEq]
          have split := List.append_inj payloads length
          rw [ihl leftEq split.1,ihr rightEq split.2]

/-- Two represented sources with the same physical raw tree are literally
the same source, including every leaf record. -/
theorem represented_source_unique {key : ρ → κ} {right : ρ → Bool}
    {reference : Source α ρ} {a b : RawComponent α κ}
    (first : Represents key right reference a) (second : Represents key right reference b)
    (physical : referenceCuts id a.closed = referenceCuts id b.closed) : a.closed = b.closed := by
  apply source_ext physical
  rw [represented_leafPayloads first,represented_leafPayloads second]

end ChaCha.Paper20261030.SplayAuxiliary
