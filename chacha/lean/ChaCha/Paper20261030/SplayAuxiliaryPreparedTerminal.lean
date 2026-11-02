import ChaCha.Paper20261030.SplayAuxiliarySpliceReference
import ChaCha.Paper20261030.SplayAuxiliaryReferencePorts
import ChaCha.Paper20261030.PreparedSeparators
import ChaCha.Paper20261030.SourceRecordMap

/-! The prepared terminal is an exact port of an arbitrary-shape splay
auxiliary. Its index is determined by the ordered separator word. -/

namespace ChaCha.Paper20261030.SplayAuxiliary

open ColoredStorage SecondaryDecomposition RawComponent Decomposition
open PreferredProjection

 theorem represented_core_ordered {reference : Source Nat Cached}
    {c : RawComponent Nat Nat} (represented : Represents cutKey followsRight reference c)
    (ordered : (referenceCuts cutKey reference).Ordered) : c.core.Ordered := by
  have word : c.core.inorder =
      (MultiSplay.ClassicalSwitch.preferred (referenceState followsRight reference)
        (referenceCuts cutKey reference)).inorder := by
    rw [preferred_referenceCuts,auxiliary_map_inorder]
    exact represented.word
  change c.core.inorder.Pairwise (· < ·)
  rw [word]
  exact ordered.sublist (MultiSplay.ClassicalSwitch.preferred_sublist _ _)

 theorem represented_terminalIndex_bound {reference : Source Nat Cached}
    {c : RawComponent Nat Nat} (represented : Represents cutKey followsRight reference c) :
    PathDecomposition.terminalIndex followsRight reference ≤ c.core.size := by
  rw [represented.size]
  exact PathDecomposition.terminalIndex_bound _ _

 theorem represented_terminal_port {reference : Source Nat Cached}
    {c : RawComponent Nat Nat} (represented : Represents cutKey followsRight reference c) :
    c.ports (PathDecomposition.terminalIndex followsRight reference) =
      (PathDecomposition.terminalSource followsRight reference).mapRecords cutKey := by
  induction represented with
  | leaf same => exact same.ports 0 (Nat.zero_le _)
  | @left record l r lc rc c direction hl hr same ihl ihr =>
      have index := represented_terminalIndex_bound hl
      have within : PathDecomposition.terminalIndex followsRight l ≤ c.core.size := by
        rw [same.size,append_size]; omega
      simp only [PathDecomposition.terminalIndex,PathDecomposition.terminalSource,
        direction,Bool.false_eq_true,if_false]
      rw [same.ports _ within]
      simpa only [append,if_pos index] using ihl
  | @right record l r lc rc c direction hl hr same ihl ihr =>
      have index := represented_terminalIndex_bound hr
      have within : 1+PathDecomposition.terminalIndex followsRight r ≤ c.core.size := by
        rw [same.size,prepend_size]; omega
      simp only [PathDecomposition.terminalIndex,PathDecomposition.terminalSource,
        direction,if_true]
      rw [same.ports _ within]
      simpa only [prepend,show ¬1+PathDecomposition.terminalIndex followsRight r=0 by omega,
        if_false,Nat.add_sub_cancel_left] using ihr

 theorem prepared_terminal_port {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (prepared : (Secondary.decodeDepth reference p).terminal = d)
    {c : RawComponent Nat Nat} (represented : Represents cutKey followsRight (source reference p) c) :
    c.ports (PathDecomposition.terminalIndex followsRight (source reference p)) = .leaf d d := by
  rw [represented_terminal_port represented,terminalSource_eq,prepared]
  rfl

 theorem prepared_terminal_rank {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (prepared : (Secondary.decodeDepth reference p).terminal = d)
    {c : RawComponent Nat Nat} (represented : Represents cutKey followsRight (source reference p) c) :
    PathDecomposition.terminalIndex followsRight (source reference p) =
      (c.core.inorder.filter (fun key => decide (key < d))).length := by
  rw [represented_keys reference p represented,List.filter_map,List.length_map]
  exact terminalIndex_rank reference p d prepared

 theorem prepared_lower_member {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (prepared : (Secondary.decodeDepth reference p).terminal = d) (lower : a < d)
    {c : RawComponent Nat Nat} (represented : Represents cutKey followsRight (source reference p) c) :
    d-1 ∈ c.core.inorder := by
  obtain ⟨entry,present,key⟩ := SeparatorPath.terminal_lower_separator reference p d prepared lower
  rw [represented_keys reference p represented]
  exact List.mem_map.mpr ⟨entry,present,by omega⟩

 theorem prepared_upper_member {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (prepared : (Secondary.decodeDepth reference p).terminal = d) (upper : d < b)
    {c : RawComponent Nat Nat} (represented : Represents cutKey followsRight (source reference p) c) :
    d ∈ c.core.inorder := by
  obtain ⟨entry,present,key⟩ := SeparatorPath.terminal_upper_separator reference p d prepared upper
  rw [represented_keys reference p represented]
  exact List.mem_map.mpr ⟨entry,present,key⟩

end ChaCha.Paper20261030.SplayAuxiliary
