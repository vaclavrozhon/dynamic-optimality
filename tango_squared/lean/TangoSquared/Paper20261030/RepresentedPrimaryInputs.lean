import TangoSquared.Paper20261030.PackedPrimaryRepresentation
import TangoSquared.Paper20261030.DecompositionLeaves

/-!
# Maintained secondary components supply the packed primary inputs

The active source has all depth leaves. A dormant source is the suffix
starting one position before its primary start, so its first depth is
the sentinel. These constructors use the actual closed balanced
representations, not an assumed projected leaf-word contract.
-/

namespace TangoSquared.Paper20261030.PackedPrimary

open PreferredProjection ColoredStorage PrimaryWings PrimaryPhysical
open AuxiliaryComponent BoundaryObservations PathDecomposition SecondaryDecomposition

variable {α : Type*} [DecidableEq α]

theorem filter_suffix_range (a b d : Nat) (bounds : a ≤ d ∧ d ≤ b) :
    (List.range' a (b+1-a)).filter (Secondary.suffixKeep d) = List.range' d (b+1-d) := by
  have split : List.range' a (b+1-a) = List.range' a (d-a) ++ List.range' d (b+1-d) := by
    have offset : a + (d-a) = d := by omega
    have lengths : d-a + (b+1-d) = b+1-a := by omega
    simpa only [offset,lengths] using (List.range'_append_1 (s := a) (m := d-a) (n := b+1-d)).symm
  rw [split,List.filter_append]
  have gone : (List.range' a (d-a)).filter (Secondary.suffixKeep d) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    have range := List.mem_range'.mp hx
    simp only [Secondary.suffixKeep,decide_eq_true_eq]
    omega
  have retained : (List.range' d (b+1-d)).filter (Secondary.suffixKeep d) = List.range' d (b+1-d) := by
    apply List.filter_eq_self.mpr
    intro x hx
    have range := List.mem_range'.mp hx
    simp only [Secondary.suffixKeep,decide_eq_true_eq]
    omega
  rw [gone,retained,List.nil_append]

def activeInput {b : Nat} (t : PrefRouter α) (reference : DepthTree 0 b)
    (p : DepthSplit → Bool) (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c)
    (pathLength : (exits t).length = b) : Input t Cached where
  start := 0
  source := closed c
  leaves := Or.inl (by simpa only [pathLength,Nat.sub_zero] using represented_leaf_word reference p c represented)

def dormantInput {b start : Nat} (t : PrefRouter α) (reference : DepthTree 0 b)
    (positive : 0 < start) (valid : start ≤ b) (p : DepthSplit → Bool)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference p (start-1) ⟨Nat.zero_le _,by omega⟩) c)
    (pathLength : (exits t).length = b-start) : Input t Cached where
  start := start
  source := closed c
  leaves := Or.inr ⟨positive,by
    rw [represented_suffix_leaf_word reference p (start-1) _ c represented,
      filter_suffix_range 0 b (start-1) ⟨Nat.zero_le _,by omega⟩,pathLength]
    have length : b+1-(start-1) = (b-start+1)+1 := by omega
    rw [length,List.range'_succ,show start-1+1 = start by omega]⟩

end TangoSquared.Paper20261030.PackedPrimary
