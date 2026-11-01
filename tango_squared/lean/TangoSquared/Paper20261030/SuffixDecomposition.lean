import TangoSquared.Paper20261030.SuffixSource
import TangoSquared.Paper20261030.AdjacentExposure

/-!
# Balanced dormant components and their prepared boundary

The maintained decomposition also applies to the suffix-restricted
reference. Its root core is precisely the full prepared path's record
word filtered at the sentinel. Original record identities are retained.
The sentinel is the first actual port; exposing its separator costs one
balanced split and does not enter any attached component.
-/

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open PreferredProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem represented_suffix_word {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (terminal : (Secondary.decodeDepth reference p).terminal = d)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference p d valid) c) :
    c.core.toListModel = ((SeparatorPath.word reference p).filter (fun e => decide (d ≤ e.1))).map markEntry := by
  rw [represented.word,suffixSource_word reference p d valid terminal]

theorem represented_suffix_ordered {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (terminal : (Secondary.decodeDepth reference p).terminal = d)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference p d valid) c) : c.core.Ordered := by
  change c.core.toListModel.Pairwise _
  rw [represented_suffix_word reference p d valid terminal c represented,List.pairwise_map]
  simpa only [markEntry,Nat.compare_eq_lt] using
    (SeparatorPath.keys_increasing reference p).filter (fun e => decide (d ≤ e.1))

theorem represented_suffix_size {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference p d valid) c) :
    c.core.size ≤ (LocalReferences.depthReference reference).height :=
  represented.size_height.trans (suffixSource_height reference p d valid)

theorem represented_sentinel_port {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (terminal : (Secondary.decodeDepth reference p).terminal = d)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference p d valid) c) :
    c.ports 0 = terminalLeaf d := by
  have port := represented.terminal_port
  obtain ⟨index,leaf⟩ := suffixSource_terminalIndex reference p d valid terminal
  rwa [index,leaf] at port

theorem represented_suffix_minimum {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (terminal : (Secondary.decodeDepth reference p).terminal = d)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference p d valid) c) :
    ∀ e ∈ c.core.toListModel, d ≤ e.1 := by
  intro e he
  rw [represented_suffix_word reference p d valid terminal c represented] at he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  exact of_decide_eq_true (List.mem_filter.mp hf).2

theorem represented_suffix_boundary_found {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (terminal : (Secondary.decodeDepth reference p).terminal = d) (upper : d < b)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference p d valid) c) : searchResult d c.core = true := by
  obtain ⟨e,he,key⟩ := SeparatorPath.terminal_upper_separator reference p d terminal upper
  have present : markEntry e ∈ c.core.toListModel := by
    rw [represented_suffix_word reference p d valid terminal c represented]
    exact List.mem_map.mpr ⟨e,List.mem_filter.mpr ⟨he,by simp [key]⟩,rfl⟩
  have found : searchResult e.1 c.core = true := by
    rw [searchResult_eq_contains,contains_eq_containsKey
      (represented_suffix_ordered reference p d valid terminal c represented)]
    exact Std.Internal.List.containsKey_of_mem present
  rwa [key] at found

theorem expose_prepared_sentinel {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (terminal : (Secondary.decodeDepth reference p).terminal = d) (upper : d < b)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference p d valid) c) :
    ∃ (right : AuxiliaryComponent Nat Nat (Tagged Payload)) (boundary : Cached),
      boundary.2.1 = d ∧ Clean right.core ∧ MarkedPorts right ∧
      SourcePointer.Rearranges (closed c) (.fork boundary (terminalLeaf d) right.tree)
        (5730 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 2) := by
  have ordered := represented_suffix_ordered reference p d valid terminal c represented
  have minimum := represented_suffix_minimum reference p d valid terminal c represented
  have found := represented_suffix_boundary_found reference p d valid terminal upper c represented
  obtain ⟨clean,marked⟩ := represented.invariant
  have exposed := minimum_expose_charged c ordered d found minimum
  have index : gapIndex d c.core = 0 := by
    rw [gapIndex_at_split c ordered d found,minimum_left_empty c ordered d found minimum]
    rfl
  rw [index,represented_sentinel_port reference p d valid terminal c represented] at exposed
  refine ⟨cutRight c d found,(c.core.size,⟨d,(splitAt d c.core c.balanced found).value⟩),rfl,
    (clean_split c clean d found).2.2,marked_cutRight c marked d found,?_⟩
  apply ((open_charged c clean marked).trans exposed).mono
  have size := represented_suffix_size reference p d valid c represented
  have logarithm := Nat.clog_monotone 2 (Nat.add_le_add_right size 1)
  omega

end TangoSquared.Paper20261030.SecondaryDecomposition
