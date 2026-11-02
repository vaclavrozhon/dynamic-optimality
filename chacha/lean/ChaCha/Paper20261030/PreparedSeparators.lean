import ChaCha.Paper20261030.TerminalRank
import ChaCha.Paper20261030.ExactSplitWords

/-!
# The two separators adjacent to a prepared terminal

A preferred path ending at depth `d` contains separator `d` whenever a
larger leaf exists, and separator `d-1` whenever a smaller leaf exists.
These are actual records of every balanced component representing that
path. Thus the boundary exposures used by a prepared primary switch
search for existing keys, including the separate left-endpoint case.
-/

namespace ChaCha.Paper20261030.SeparatorPath

open PreferredProjection

theorem terminal_upper_separator {a b : Nat} (reference : DepthTree a b)
    (p : DepthSplit → Bool) (d : Nat)
    (terminal : (Secondary.decodeDepth reference p).terminal = d) (upper : d < b) :
    ∃ e ∈ word reference p, e.1 = d := by
  induction reference with
  | leaf a => simp only [Secondary.decodeDepth,PrefRouter.terminal] at terminal; omega
  | @node a b cut ha hb l r ihl ihr =>
    cases bit : p ⟨a,cut,b⟩
    · have endpoint : (Secondary.decodeDepth l p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,Bool.false_eq_true,if_false] using terminal
      have bounds := (Secondary.decodeDepth_mem l p d).mp
        (by rw [← endpoint]; exact PrefRouter.terminal_mem _)
      by_cases equal : d = cut
      · refine ⟨⟨cut,(⟨a,cut,b⟩,false)⟩,?_,equal.symm⟩
        simp [word,bit]
      · obtain ⟨e,he,hd⟩ := ihl endpoint (by omega)
        exact ⟨e,by simp [word,bit,he],hd⟩
    · have endpoint : (Secondary.decodeDepth r p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,if_true] using terminal
      obtain ⟨e,he,hd⟩ := ihr endpoint upper
      exact ⟨e,by simp [word,bit,he],hd⟩

theorem terminal_lower_separator {a b : Nat} (reference : DepthTree a b)
    (p : DepthSplit → Bool) (d : Nat)
    (terminal : (Secondary.decodeDepth reference p).terminal = d) (lower : a < d) :
    ∃ e ∈ word reference p, e.1 + 1 = d := by
  induction reference with
  | leaf a => simp only [Secondary.decodeDepth,PrefRouter.terminal] at terminal; omega
  | @node a b cut ha hb l r ihl ihr =>
    cases bit : p ⟨a,cut,b⟩
    · have endpoint : (Secondary.decodeDepth l p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,Bool.false_eq_true,if_false] using terminal
      obtain ⟨e,he,hd⟩ := ihl endpoint lower
      exact ⟨e,by simp [word,bit,he],hd⟩
    · have endpoint : (Secondary.decodeDepth r p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,if_true] using terminal
      have bounds := (Secondary.decodeDepth_mem r p d).mp
        (by rw [← endpoint]; exact PrefRouter.terminal_mem _)
      by_cases equal : cut + 1 = d
      · refine ⟨⟨cut,(⟨a,cut,b⟩,true)⟩,?_,equal⟩
        simp [word,bit]
      · obtain ⟨e,he,hd⟩ := ihr endpoint (by omega)
        exact ⟨e,by simp [word,bit,he],hd⟩

end ChaCha.Paper20261030.SeparatorPath

namespace ChaCha.Paper20261030.SecondaryDecomposition

open Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem prepared_upper_found {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (terminal : (Secondary.decodeDepth reference p).terminal = d) (upper : d < b)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) : searchResult d c.core = true := by
  obtain ⟨e,he,hd⟩ := SeparatorPath.terminal_upper_separator reference p d terminal upper
  have present : markEntry e ∈ c.core.toListModel := by
    rw [represented_word reference p c represented]
    exact List.mem_map.mpr ⟨e,he,rfl⟩
  have found : searchResult e.1 c.core = true := by
    rw [searchResult_eq_contains,Std.DTreeMap.Internal.Impl.contains_eq_containsKey
      (represented_ordered reference p c represented)]
    exact Std.Internal.List.containsKey_of_mem present
  simpa only [markEntry,hd] using found

theorem prepared_lower_found {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (terminal : (Secondary.decodeDepth reference p).terminal = d) (lower : a < d)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) : searchResult (d-1) c.core = true := by
  obtain ⟨e,he,hd⟩ := SeparatorPath.terminal_lower_separator reference p d terminal lower
  have present : markEntry e ∈ c.core.toListModel := by
    rw [represented_word reference p c represented]
    exact List.mem_map.mpr ⟨e,he,rfl⟩
  have found : searchResult e.1 c.core = true := by
    rw [searchResult_eq_contains,Std.DTreeMap.Internal.Impl.contains_eq_containsKey
      (represented_ordered reference p c represented)]
    exact Std.Internal.List.containsKey_of_mem present
  have key : e.1 = d-1 := by omega
  simpa only [markEntry,key] using found

end ChaCha.Paper20261030.SecondaryDecomposition
