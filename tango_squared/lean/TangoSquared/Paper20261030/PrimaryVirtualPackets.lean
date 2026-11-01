import TangoSquared.Paper20261030.VirtualHeadPackets
import TangoSquared.Paper20261030.VirtualPackedCursor

/-! The actual depth intervals have the virtual-packet shapes used by
`VirtualHeadPackets.exchange`: prefixes below the boundary have no
virtual leaf, and an interval ending at completion has exactly one.
These facts are independent of the balanced routing shape.
-/

namespace TangoSquared.Paper20261030.PrimaryVirtualPackets

open ColoredStorage SourcePointer Structural PreferredProjection PrimaryWings PackedPrimary

variable {α ρ : Type*} [DecidableEq α]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem real_depth (start : Nat) (tree : PrefRouter α) (depth : Nat)
    (lower : start ≤ depth) (upper : depth < start+(exits tree).length) :
    color start tree depth ≠ none := by
  have valid : depth-start < (exits tree).length := by omega
  simp [color,portAt,lower,List.getElem?_eq_getElem valid]

theorem completion (start : Nat) (tree : PrefRouter α) :
    color start tree (start+(exits tree).length) = none := by
  simp only [color,portAt_completion,Option.map_none]

theorem absent_of_real (colors : Nat → Option Bool) (source : Source Nat ρ)
    (real : ∀ depth ∈ source.shape.leaves, colors depth ≠ none) :
    packed colors none source = none := by
  apply (packed_none_iff colors none source).mpr
  induction source with
  | leaf key record =>
    simpa only [Source.support,Finset.mem_singleton,eq_comm] using real key (by simp only [Source.shape,RouterProjection.Router.leaves,List.mem_singleton])
  | fork record left right ihl ihr =>
    apply Finset.notMem_union.mpr
    exact ⟨ihl (fun depth member => real depth (List.mem_append_left _ member)),
      ihr (fun depth member => real depth (List.mem_append_right _ member))⟩

theorem prefix_absent (tree : PrefRouter α) (source : Source Nat ρ)
    (below : ∀ depth ∈ source.shape.leaves, depth < (exits tree).length) :
    packed (color 0 tree) none source = none :=
  absent_of_real _ source (fun depth member => real_depth 0 tree depth (Nat.zero_le _)
    (by simpa only [Nat.zero_add] using below depth member))

theorem leaf_of_word (colors : Nat → Option Bool) (source : Source Nat ρ) (bottom : Nat)
    (word : source.shape.leaves.filter (fun depth => decide (colors depth = none)) = [bottom]) :
    ∃ records, packed colors none source = some (.leaf bottom records) := by
  have leaves := packed_leaves colors none source
  rw [word] at leaves
  change optionalLeaves (packed colors none source) = [bottom] at leaves
  cases found : packed colors none source with
  | none =>
    rw [found] at leaves
    simp only [optionalLeaves,reduceCtorEq] at leaves
  | some actual =>
    change optionalLeaves (packed colors none source) = [bottom] at leaves
    rw [found] at leaves
    change actual.shape.leaves = [bottom] at leaves
    obtain ⟨key,records,equal⟩ := actual.one_leaf (by rw [leaves]; change 1 ≤ 1; decide)
    subst actual
    have same : key = bottom := by simpa only [Source.shape,RouterProjection.Router.leaves,List.cons.injEq,and_true] using leaves
    subst key
    exact ⟨records,rfl⟩

theorem interval_virtual_word (start : Nat) (tree : PrefRouter α) (first : Nat)
    (lower : start ≤ first) (upper : first ≤ start+(exits tree).length) :
    (List.range' first (start+(exits tree).length+1-first)).filter
      (fun depth => decide (color start tree depth = none)) = [start+(exits tree).length] := by
  let bottom := start+(exits tree).length
  have size : bottom+1-first = (bottom-first)+1 := by omega
  have endpoint : first+(bottom-first) = bottom := by omega
  change (List.range' first (bottom+1-first)).filter _ = [bottom]
  rw [size,← List.range'_append_1,List.filter_append,endpoint]
  have absent : (List.range' first (bottom-first)).filter
      (fun depth => decide (color start tree depth = none)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro depth member
    obtain ⟨le,lt⟩ := List.mem_range'_1.mp member
    have no := real_depth start tree depth (by omega) (by dsimp only [bottom] at *; omega)
    exact fun impossible => no (of_decide_eq_true impossible)
  rw [absent]
  simp only [List.nil_append,List.range'_succ,List.range'_zero,List.filter_cons,List.filter_nil,
    bottom,completion,decide_true,if_true]

theorem interval_packet (start : Nat) (tree : PrefRouter α) (first : Nat) (source : Source Nat ρ)
    (lower : start ≤ first) (upper : first ≤ start+(exits tree).length)
    (leaves : source.shape.leaves = List.range' first (start+(exits tree).length+1-first)) :
    ∃ records, packed (color start tree) none source = some (.leaf (start+(exits tree).length) records) := by
  apply leaf_of_word
  rw [leaves]
  exact interval_virtual_word start tree first lower upper

end TangoSquared.Paper20261030.PrimaryVirtualPackets
