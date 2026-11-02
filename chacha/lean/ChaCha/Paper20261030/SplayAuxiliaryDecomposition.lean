import ChaCha.Paper20261030.SplayAuxiliaryComponent

/-!
# Preferred-path decomposition with separate reference metadata

`Represents key right reference component` identifies every physical key
and every hanging subtree. It permits any shape of the root auxiliary,
which is essential when ordinary splaying replaces balanced auxiliaries.
The port characterization exposes exactly the recursive invariant used
by the existing classical MultiSplay implementation.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary.Decomposition

open DynamicOptimality (RawTree)
open ColoredStorage RawComponent

variable {α κ ρ : Type*}

inductive Represents (key : ρ → κ) (right : ρ → Bool) :
    Source α ρ → RawComponent α κ → Prop
  | leaf {label record c} (same : Equivalent c (terminal (.leaf label (key record)))) :
      Represents key right (.leaf label record) c
  | left {record l r lc rc c} (direction : right record = false)
      (left : Represents key right l lc) (rightChild : Represents key right r rc)
      (same : Equivalent c (append lc (key record) (closed rc))) :
      Represents key right (.fork record l r) c
  | right {record l r lc rc c} (direction : right record = true)
      (leftChild : Represents key right l lc) (rightChild : Represents key right r rc)
      (same : Equivalent c (prepend (key record) (closed lc) rc)) :
      Represents key right (.fork record l r) c

theorem Represents.equivalent {key : ρ → κ} {right : ρ → Bool} {reference : Source α ρ}
    {c d : RawComponent α κ} (represented : Represents key right reference c)
    (same : Equivalent d c) : Represents key right reference d := by
  cases represented with
  | leaf equivalent => exact .leaf (same.trans equivalent)
  | left direction left right equivalent => exact .left direction left right (same.trans equivalent)
  | right direction left right equivalent => exact .right direction left right (same.trans equivalent)

theorem Represents.left_view {key : ρ → κ} {right : ρ → Bool} {record : ρ}
    {l r : Source α ρ} {c : RawComponent α κ}
    (represented : Represents key right (.fork record l r) c) (direction : right record = false) :
    ∃ lc rc, Represents key right l lc ∧ Represents key right r rc ∧
      Equivalent c (append lc (key record) (closed rc)) := by
  cases represented with
  | left _ left right same => exact ⟨_,_,left,right,same⟩
  | right opposite => simp [direction] at opposite

theorem Represents.right_view {key : ρ → κ} {right : ρ → Bool} {record : ρ}
    {l r : Source α ρ} {c : RawComponent α κ}
    (represented : Represents key right (.fork record l r) c) (direction : right record = true) :
    ∃ lc rc, Represents key right l lc ∧ Represents key right r rc ∧
      Equivalent c (prepend (key record) (closed lc) rc) := by
  cases represented with
  | left opposite => simp [direction] at opposite
  | right _ left right same => exact ⟨_,_,left,right,same⟩

theorem Represents.word {key : ρ → κ} {right : ρ → Bool} {reference : Source α ρ}
    {c : RawComponent α κ} (represented : Represents key right reference c) :
    c.core.inorder = (PathPorts.skeleton right reference).inorder.map key := by
  induction represented with
  | leaf same => exact same.word
  | left direction left right same ihl ihr =>
      rw [same.word,append_word,ihl]
      simp only [PathPorts.skeleton,direction,Bool.false_eq_true,if_false,MTR.Tree.inorder,
        List.append_nil,List.map_append,List.map_singleton]
  | right direction left right same ihl ihr =>
      rw [same.word,prepend_word,ihr]
      simp only [PathPorts.skeleton,direction,if_true,MTR.Tree.inorder,List.nil_append,
        List.singleton_append,List.map_cons]

theorem Represents.size {key : ρ → κ} {right : ρ → Bool} {reference : Source α ρ}
    {c : RawComponent α κ} (represented : Represents key right reference c) :
    c.core.size = (PathPorts.skeleton right reference).size := by
  rw [← MTR.Tree.length_inorder,represented.word,List.length_map,MTR.Tree.length_inorder]

theorem skeleton_height (right : ρ → Bool) (reference : Source α ρ) :
    (PathPorts.skeleton right reference).size ≤ reference.shape.height := by
  induction reference with
  | leaf => exact Nat.le_refl _
  | fork record left rightChild ihl ihr =>
      cases direction : right record <;>
        simp only [PathPorts.skeleton,direction,Bool.false_eq_true,if_false,if_true,MTR.Tree.size,
          Source.shape,RouterProjection.Router.height] <;> omega

theorem Represents.size_height {key : ρ → κ} {right : ρ → Bool} {reference : Source α ρ}
    {c : RawComponent α κ} (represented : Represents key right reference c) :
    c.core.size ≤ reference.shape.height := by
  rw [represented.size]
  exact skeleton_height right reference

def pathCore (key : ρ → κ) (right : ρ → Bool) : Source α ρ → RawTree κ
  | .leaf .. => .empty
  | .fork record l r =>
      if right record then .node .empty (key record) (pathCore key right r)
      else .node (pathCore key right l) (key record) .empty

theorem pathCore_word (key : ρ → κ) (right : ρ → Bool) (reference : Source α ρ) :
    (pathCore key right reference).inorder = (PathPorts.skeleton right reference).inorder.map key := by
  induction reference with
  | leaf => rfl
  | fork record l r ihl ihr =>
      cases direction : right record <;>
        simp [pathCore,PathPorts.skeleton,direction,MTR.Tree.inorder,ihl,ihr]

theorem pathCore_size (key : ρ → κ) (right : ρ → Bool) (reference : Source α ρ) :
    (pathCore key right reference).size = (PathPorts.skeleton right reference).size := by
  rw [← MTR.Tree.length_inorder,pathCore_word,List.length_map,MTR.Tree.length_inorder]

theorem Represents.closed_leaf {key : ρ → κ} {right : ρ → Bool} {label : α} {record : ρ}
    {c : RawComponent α κ} (represented : Represents key right (.leaf label record) c) :
    c.closed = .leaf label (key record) := by
  cases represented with
  | leaf same =>
      have size := same.size
      have port := same.ports 0 (Nat.zero_le _)
      rcases c with ⟨core,ports⟩
      cases core with
      | empty => exact port
      | node l root r => simp [terminal,MTR.Tree.size] at size

theorem Represents.port_represented {key : ρ → κ} {right : ρ → Bool} {reference : Source α ρ}
    {c : RawComponent α κ} (represented : Represents key right reference c)
    (i : Nat) (bound : i ≤ c.core.size) :
    ∃ component, Represents key right (PathPorts.port right reference i) component ∧
      c.ports i = component.closed := by
  induction represented generalizing i with
  | @leaf label record c same =>
      have zero : i = 0 := by have := same.size; simp only [terminal,MTR.Tree.size] at this; omega
      subst i
      refine ⟨terminal (.leaf label (key record)),.leaf (.refl _),?_⟩
      exact same.ports 0 (Nat.zero_le _)
  | @left record l r lc rc c direction hl hr same ihl ihr =>
      rw [same.ports i bound]
      simp only [PathPorts.port,direction,Bool.false_eq_true,if_false]
      by_cases before : i ≤ lc.core.size
      · have skeletonBound : i ≤ (PathPorts.skeleton right l).size := by rwa [← hl.size]
        simpa only [append,if_pos before,if_pos skeletonBound] using ihl i before
      · have skeletonBound : ¬ i ≤ (PathPorts.skeleton right l).size := by rwa [← hl.size]
        simp only [append,if_neg before,if_neg skeletonBound]
        exact ⟨rc,hr,rfl⟩
  | @right record l r lc rc c direction hl hr same ihl ihr =>
      rw [same.ports i bound]
      simp only [PathPorts.port,direction,if_true]
      by_cases zero : i = 0
      · simp only [prepend,if_pos zero]
        exact ⟨lc,hl,rfl⟩
      · have before : i-1 ≤ rc.core.size := by rw [same.size,prepend_size] at bound; omega
        simpa only [prepend,if_neg zero] using ihr (i-1) before

/-- The exact root word and recursive physical ports suffice; no balance
or particular auxiliary shape is assumed. -/
theorem represents_of_word_ports (key : ρ → κ) (right : ρ → Bool)
    (reference : Source α ρ) (c : RawComponent α κ)
    (word : c.core.inorder = (PathPorts.skeleton right reference).inorder.map key)
    (ports : ∀ i, i ≤ c.core.size → ∃ component,
      Represents key right (PathPorts.port right reference i) component ∧
      c.ports i = component.closed) : Represents key right reference c := by
  have size : c.core.size = (PathPorts.skeleton right reference).size := by
    rw [← MTR.Tree.length_inorder,word,List.length_map,MTR.Tree.length_inorder]
  induction reference generalizing c with
  | leaf label record =>
      obtain ⟨component,represented,port⟩ := ports 0 (Nat.zero_le _)
      refine .leaf ⟨word,?_⟩
      intro i bound
      have zero : i = 0 := by simp only [PathPorts.skeleton,MTR.Tree.size] at size; omega
      subst i
      exact port.trans represented.closed_leaf
  | fork record l r ihl ihr =>
      cases direction : right record
      · have total : c.core.size = (PathPorts.skeleton right l).size+1 := by
          simpa [PathPorts.skeleton,direction,MTR.Tree.size] using size
        let lc : RawComponent α κ := ⟨pathCore key right l,c.ports⟩
        have left : Represents key right l lc := by
          apply ihl lc (pathCore_word key right l)
          · intro i bound
            have childBound : i ≤ (PathPorts.skeleton right l).size := by
              simpa only [lc,pathCore_size] using bound
            obtain ⟨component,represented,port⟩ := ports i (by omega)
            refine ⟨component,?_,port⟩
            simpa only [PathPorts.port,direction,Bool.false_eq_true,if_false,if_pos childBound] using represented
          · exact pathCore_size key right l
        obtain ⟨rc,rightChild,last⟩ := ports ((PathPorts.skeleton right l).size+1) (by omega)
        have rightRep : Represents key right r rc := by
          simpa [PathPorts.port,direction] using rightChild
        refine .left direction left rightRep ⟨?_,?_⟩
        · rw [append_word,left.word,word]
          simp [PathPorts.skeleton,direction,MTR.Tree.inorder]
        · intro i bound
          by_cases before : i ≤ lc.core.size
          · simp only [append,if_pos before,lc]
          · have lastIndex : i = (PathPorts.skeleton right l).size+1 := by
              have childSize := left.size
              omega
            simp only [append,if_neg before]
            simpa only [lastIndex] using last
      · have total : c.core.size = (PathPorts.skeleton right r).size+1 := by
          simpa [PathPorts.skeleton,direction,MTR.Tree.size,Nat.add_comm] using size
        let rc : RawComponent α κ := ⟨pathCore key right r,fun i => c.ports (i+1)⟩
        have rightChild : Represents key right r rc := by
          apply ihr rc (pathCore_word key right r)
          · intro i bound
            have childBound : i ≤ (PathPorts.skeleton right r).size := by
              simpa only [rc,pathCore_size] using bound
            obtain ⟨component,represented,port⟩ := ports (i+1) (by omega)
            refine ⟨component,?_,port⟩
            simpa [PathPorts.port,direction] using represented
          · exact pathCore_size key right r
        obtain ⟨lc,left,first⟩ := ports 0 (Nat.zero_le _)
        have leftRep : Represents key right l lc := by
          simpa [PathPorts.port,direction] using left
        refine .right direction leftRep rightChild ⟨?_,?_⟩
        · rw [prepend_word,rightChild.word,word]
          simp [PathPorts.skeleton,direction,MTR.Tree.inorder]
        · intro i bound
          by_cases zero : i = 0
          · subst i
            simpa only [prepend,if_true] using first
          · simp only [prepend,if_neg zero,rc]
            congr 1
            omega

theorem represents_iff_word_ports (key : ρ → κ) (right : ρ → Bool)
    (reference : Source α ρ) (c : RawComponent α κ) :
    Represents key right reference c ↔
      c.core.inorder = (PathPorts.skeleton right reference).inorder.map key ∧
      (∀ i, i ≤ c.core.size → ∃ component,
        Represents key right (PathPorts.port right reference i) component ∧
        c.ports i = component.closed) :=
  ⟨fun represented => ⟨represented.word,represented.port_represented⟩,
    fun ⟨word,ports⟩ => represents_of_word_ports key right reference c word ports⟩

end ChaCha.Paper20261030.SplayAuxiliary.Decomposition
