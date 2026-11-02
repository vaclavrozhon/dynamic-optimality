import ChaCha.Paper20261030.SecondaryDecomposition

/-!
# A complete reference-root preference flip on the physical representation

For either old preference, the actual one-cursor trace changes exactly
the root split bit and preserves the maintained representation of every
other reference record. The new core is again balanced, ordered, bounded
by reference height, clean internally, and marked at all entrances.
Interior departures still require the context-lifting proof.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem flip_root_charged {a b cut : Nat} (ha : a ≤ cut) (hb : cut < b)
    (l : DepthTree a cut) (r : DepthTree (cut + 1) b) (p : DepthSplit → Bool)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source (.node cut ha hb l r) p) c) :
    ∃ d : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight
        (source (.node cut ha hb l r) (Function.update p ⟨a,cut,b⟩ (!p ⟨a,cut,b⟩))) d ∧
      SourcePointer.Rearranges (closed c) (closed d)
        (6225 * Nat.clog 2 ((LocalReferences.depthReference (.node cut ha hb l r)).height + 1) + 90) := by
  let reference := DepthTree.node cut ha hb l r
  let K := (LocalReferences.depthReference reference).height
  have hc := represented_size reference p c represented
  have ordered := represented_ordered reference p c represented
  have hclog := Nat.clog_monotone 2 (Nat.add_le_add_right hc 1)
  cases hd : p ⟨a,cut,b⟩
  · have dir : followsRight (0,⟨cut,((⟨a,cut,b⟩,p ⟨a,cut,b⟩),false)⟩) = false := hd
    obtain ⟨lc,rc,hl,hr,same⟩ := represented.left_view dir
    obtain ⟨d,represented',trace⟩ := left_head_repair followsRight
      (0,⟨cut,((⟨a,cut,b⟩,p ⟨a,cut,b⟩),false)⟩) (source l p) (source r p) lc rc c hl hr same
      dir rfl ordered ((⟨a,cut,b⟩,true),false) rfl rfl
    refine ⟨d,?_,trace.mono ?_⟩
    · simpa only [hd,Bool.not_false,source_flip_root] using represented'
    · have hrsize := represented_size r p rc hr
      have hrheight : (LocalReferences.depthReference r).height ≤ K := by
        simp only [K,reference,LocalReferences.depthReference,RouterProjection.Router.height]
        omega
      have hrlog := Nat.clog_monotone 2 (show rc.core.size + 1 ≤ K + 1 by omega)
      dsimp only [K,reference] at hclog hrlog
      omega
  · have dir : followsRight (0,⟨cut,((⟨a,cut,b⟩,p ⟨a,cut,b⟩),false)⟩) = true := hd
    obtain ⟨lc,rc,hl,hr,same⟩ := represented.right_view dir
    obtain ⟨d,represented',trace⟩ := right_head_repair followsRight
      (0,⟨cut,((⟨a,cut,b⟩,p ⟨a,cut,b⟩),false)⟩) (source l p) (source r p) lc rc c hl hr same
      dir rfl ordered ((⟨a,cut,b⟩,false),false) rfl rfl
    refine ⟨d,?_,trace.mono ?_⟩
    · simpa only [hd,Bool.not_true,source_flip_root] using represented'
    · have hlsize := represented_size l p lc hl
      have hlheight : (LocalReferences.depthReference l).height ≤ K := by
        simp only [K,reference,LocalReferences.depthReference,RouterProjection.Router.height]
        omega
      have hllog := Nat.clog_monotone 2 (show lc.core.size + 1 ≤ K + 1 by omega)
      dsimp only [K,reference] at hclog hllog
      omega

end ChaCha.Paper20261030.SecondaryDecomposition
