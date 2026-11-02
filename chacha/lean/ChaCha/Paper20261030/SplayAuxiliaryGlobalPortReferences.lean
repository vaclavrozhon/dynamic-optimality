import ChaCha.Paper20261030.SplayAuxiliaryReferencePorts
import ChaCha.Paper20261030.SplayAuxiliarySplice

/-!
# Exact reference subtrees retained by a primary splice

The ordered off-path references split at the prepared terminal. Their
records, preferences, and leaf labels remain identical on both sides.
This stronger identity lets the global inventory retain descendant cores
without reconstructing or resetting their potential.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open ColoredStorage PreferredProjection SecondaryDecomposition

variable {α ρ : Type*}

def sourcePorts (right : ρ → Bool) (reference : Source α ρ) : List (Source α ρ) :=
  (referenceEntries right reference).map Prod.snd

@[simp] theorem sourcePorts_leaf (right : ρ → Bool) (label : α) (record : ρ) :
    sourcePorts right (.leaf label record) = [.leaf label record] := rfl

theorem sourcePorts_fork (right : ρ → Bool) (record : ρ) (left child : Source α ρ) :
    sourcePorts right (.fork record left child) =
      if right record then left :: sourcePorts right child else sourcePorts right left ++ [child] := by
  cases direction : right record <;>
    simp [sourcePorts,referenceEntries,direction,List.map_map]

theorem sourcePorts_length (right : ρ → Bool) (reference : Source α ρ) :
    (sourcePorts right reference).length = (PathPorts.skeleton right reference).size+1 := by
  simp only [sourcePorts,List.length_map,referenceEntries_length]

theorem terminalIndex_sourcePorts (right : Cached → Bool) (reference : Source Nat Cached) :
    PathDecomposition.terminalIndex right reference < (sourcePorts right reference).length := by
  rw [sourcePorts_length]
  have := PathDecomposition.terminalIndex_bound right reference
  omega

theorem suffix_sourcePorts {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (terminal : (Secondary.decodeDepth reference p).terminal = d) :
    sourcePorts followsRight (suffixSource reference p d valid) =
      (sourcePorts followsRight (source reference p)).drop
        (PathDecomposition.terminalIndex followsRight (source reference p)) := by
  induction reference with
  | leaf a =>
      have equal : a = d := by omega
      subst d
      rfl
  | @node a b cut ha hb left right ihl ihr =>
      cases bit : p ⟨a,cut,b⟩
      · have endpoint : (Secondary.decodeDepth left p).terminal = d := by
          simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,Bool.false_eq_true,if_false] using terminal
        have bounds := (Secondary.decodeDepth_mem left p d).mp
          (by rw [← endpoint]; exact PrefRouter.terminal_mem _)
        simp only [suffixSource,dif_pos bounds.2,source,sourcePorts_fork,
          PathDecomposition.terminalIndex,followsRight,bit,Bool.false_eq_true,if_false]
        rw [List.drop_append_of_le_length (Nat.le_of_lt (terminalIndex_sourcePorts _ _)),ihl bounds endpoint]
      · have endpoint : (Secondary.decodeDepth right p).terminal = d := by
          simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,if_true] using terminal
        have bounds := (Secondary.decodeDepth_mem right p d).mp
          (by rw [← endpoint]; exact PrefRouter.terminal_mem _)
        have notLeft : ¬ d ≤ cut := by omega
        simp only [suffixSource,dif_neg notLeft,source,sourcePorts_fork,
          PathDecomposition.terminalIndex,followsRight,bit,if_true,Nat.add_comm 1,List.drop_succ_cons]
        exact ihr bounds endpoint

theorem splice_sourcePorts {a b : Nat} (reference : DepthTree a b) (p q : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = d)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = d) :
    sourcePorts followsRight (splicedSource reference p q d valid) =
      (sourcePorts followsRight (source reference p)).take
        (PathDecomposition.terminalIndex followsRight (source reference p)) ++
      sourcePorts followsRight (suffixSource reference q d valid) := by
  induction reference with
  | leaf => rfl
  | @node a b cut ha hb left right ihl ihr =>
      have sameBit := (SeparatorPath.terminal_root_direction ha hb left right p d preparedP).trans
        (SeparatorPath.terminal_root_direction ha hb left right q d preparedQ).symm
      cases bit : p ⟨a,cut,b⟩
      · have qbit : q ⟨a,cut,b⟩ = false := sameBit.symm.trans bit
        have leftP : (Secondary.decodeDepth left p).terminal = d := by
          simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,Bool.false_eq_true,if_false] using preparedP
        have leftQ : (Secondary.decodeDepth left q).terminal = d := by
          simpa only [Secondary.decodeDepth,PrefRouter.terminal,qbit,Bool.false_eq_true,if_false] using preparedQ
        have bounds := (Secondary.decodeDepth_mem left p d).mp
          (by rw [← leftP]; exact PrefRouter.terminal_mem _)
        simp only [splicedSource,dif_pos bounds.2,suffixSource,source,sourcePorts_fork,
          PathDecomposition.terminalIndex,followsRight,bit,qbit,Bool.false_eq_true,if_false]
        rw [List.take_append_of_le_length (Nat.le_of_lt (terminalIndex_sourcePorts _ _)),
          ihl bounds leftP leftQ,List.append_assoc]
      · have qbit : q ⟨a,cut,b⟩ = true := sameBit.symm.trans bit
        have rightP : (Secondary.decodeDepth right p).terminal = d := by
          simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,if_true] using preparedP
        have rightQ : (Secondary.decodeDepth right q).terminal = d := by
          simpa only [Secondary.decodeDepth,PrefRouter.terminal,qbit,if_true] using preparedQ
        have bounds := (Secondary.decodeDepth_mem right p d).mp
          (by rw [← rightP]; exact PrefRouter.terminal_mem _)
        have notLeft : ¬ d ≤ cut := by omega
        simp only [splicedSource,dif_neg notLeft,suffixSource,source,sourcePorts_fork,
          PathDecomposition.terminalIndex,followsRight,bit,if_true,Nat.add_comm 1,List.take_succ_cons]
        rw [ihr bounds rightP rightQ]
        rfl

end ChaCha.Paper20261030.SplayAuxiliary
