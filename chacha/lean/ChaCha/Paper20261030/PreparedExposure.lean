import ChaCha.Paper20261030.PreparedSeparators
import ChaCha.Paper20261030.AdjacentExposure

/-!
# Charged preparation of the primary head-switch boundary

For an actual represented secondary path ending at `d`, expose the two
adjacent separators around its terminal port. The output is a constant
binary context on the entire lower-depth fragment, the exact terminal,
and the entire upper-depth fragment. The endpoint case needs one split.
These are preparation traces, not yet the exchange of two primary paths.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem expose_prepared_interior {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (terminal : (Secondary.decodeDepth reference p).terminal = d)
    (lower : a < d) (upper : d < b)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    ∃ (left right : AuxiliaryComponent Nat Nat (Tagged Payload)) (low high : Cached),
      low.2.1 = d-1 ∧ high.2.1 = d ∧
      Clean left.core ∧ MarkedPorts left ∧ Clean right.core ∧ MarkedPorts right ∧
      SourcePointer.Rearranges (closed c)
        (.fork low left.tree (.fork high (terminalLeaf d) right.tree))
        (11460 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 4) := by
  have ordered := represented_ordered reference p c represented
  obtain ⟨clean,marked⟩ := represented.invariant
  have fl := prepared_lower_found reference p d terminal lower c represented
  have fu := prepared_upper_found reference p d terminal upper c represented
  have next : d-1+1 = d := by omega
  have fh : searchResult ((d-1)+1) (cutRight c (d-1) fl).core = true := by
    rw [next]
    exact higher_found_right c ordered (d-1) d (by omega) fl fu
  have exposed := adjacent_expose_charged c ordered (d-1) fl fh
  simp only [next] at exposed
  rw [represented_terminal_port reference p d terminal c represented] at exposed
  let right := cutRight (cutRight c (d-1) fl) d (by simpa only [next] using fh)
  refine ⟨cutLeft c (d-1) fl,right,
    (c.core.size,⟨d-1,(splitAt (d-1) c.core c.balanced fl).value⟩),
    ((cutRight c (d-1) fl).core.size,
      ⟨d-1+1,(splitAt (d-1+1) (cutRight c (d-1) fl).core (cutRight c (d-1) fl).balanced fh).value⟩),
    rfl,next,(clean_split c clean (d-1) fl).2.1,marked_cutLeft c marked (d-1) fl,
    (clean_split _ (clean_split c clean (d-1) fl).2.2 d _).2.2,
    marked_cutRight _ (marked_cutRight c marked (d-1) fl) d _,?_⟩
  apply ((open_charged c clean marked).trans exposed).mono
  have size := represented_size reference p c represented
  have logarithm := Nat.clog_monotone 2 (Nat.add_le_add_right size 1)
  omega

theorem expose_prepared_minimum {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (terminal : (Secondary.decodeDepth reference p).terminal = a) (upper : a < b)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    ∃ (right : AuxiliaryComponent Nat Nat (Tagged Payload)) (boundary : Cached),
      boundary.2.1 = a ∧ Clean right.core ∧ MarkedPorts right ∧
      SourcePointer.Rearranges (closed c) (.fork boundary (terminalLeaf a) right.tree)
        (5730 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 2) := by
  have ordered := represented_ordered reference p c represented
  obtain ⟨clean,marked⟩ := represented.invariant
  have found := prepared_upper_found reference p a terminal upper c represented
  have minimum : ∀ e ∈ c.core.toListModel, a ≤ e.1 := by
    intro e he
    rw [represented_word reference p c represented] at he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    exact (SeparatorPath.key_bounds reference p hf).1
  have exposed := minimum_expose_charged c ordered a found minimum
  rw [represented_terminal_port reference p a terminal c represented] at exposed
  refine ⟨cutRight c a found,(c.core.size,⟨a,(splitAt a c.core c.balanced found).value⟩),rfl,
    (clean_split c clean a found).2.2,marked_cutRight c marked a found,?_⟩
  apply ((open_charged c clean marked).trans exposed).mono
  have size := represented_size reference p c represented
  have logarithm := Nat.clog_monotone 2 (Nat.add_le_add_right size 1)
  omega

end ChaCha.Paper20261030.SecondaryDecomposition
