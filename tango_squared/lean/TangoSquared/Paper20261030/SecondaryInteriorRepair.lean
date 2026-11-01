import TangoSquared.Paper20261030.SecondaryHeadRepair
import TangoSquared.Paper20261030.SecondaryContext
import TangoSquared.Paper20261030.ContextRepair

/-!
# A charged physical preference flip at any preferred-path descendant

The descendant's reference-root flip is lifted through its unchanged
preferred context. The actual split cores match the represented reference
components, and the final joins preserve the representation of the entire
secondary reference. The cost is logarithmic in reference height, uses
one source cursor, and includes all balancing and entry-marker writes.

The descendant is specified as an input here. Locating the first departure
by actual observations and composing the whole access remain separate.
-/

namespace TangoSquared.Paper20261030.SeparatorPath

theorem Descendant.height_le {p : DepthSplit → Bool} {a b x y : Nat}
    {reference : DepthTree a b} {subtree : DepthTree x y}
    (below : Descendant p reference subtree) :
    (LocalReferences.depthReference subtree).height ≤ (LocalReferences.depthReference reference).height := by
  induction below with
  | refl => exact Nat.le_refl _
  | left ha hb l r subtree bit below ih =>
    simp only [LocalReferences.depthReference,RouterProjection.Router.height]
    omega
  | right ha hb l r subtree bit below ih =>
    simp only [LocalReferences.depthReference,RouterProjection.Router.height]
    omega

end TangoSquared.Paper20261030.SeparatorPath

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem flip_descendant_charged {a b x y pivot : Nat} (hx : x ≤ pivot) (hy : pivot < y)
    (left : DepthTree x pivot) (right : DepthTree (pivot + 1) y)
    (reference : DepthTree a b) (p : DepthSplit → Bool)
    (below : SeparatorPath.Descendant p reference (.node pivot hx hy left right))
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight
        (source reference (Function.update p ⟨x,pivot,y⟩ (!p ⟨x,pivot,y⟩))) out ∧
      SourcePointer.Rearranges (closed c) (closed out)
        (19665 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 266) := by
  let subtree := DepthTree.node pivot hx hy left right
  let q := Function.update p ⟨x,pivot,y⟩ (!p ⟨x,pivot,y⟩)
  let K := (LocalReferences.depthReference reference).height
  obtain ⟨sub,frames,hs,same,hbefore,hafter,hplug⟩ := descendant_context below c represented
  have agree : ∀ s, s ∉ subtree.nodes → q s = p s := by
    intro s hn
    have hne : s ≠ ⟨x,pivot,y⟩ := by
      intro he
      subst s
      exact hn (by simp [subtree,DepthTree.nodes])
    exact Function.update_of_ne hne _ _
  have hc := represented_size reference p c represented
  have ordered := represented_ordered reference p c represented
  have hnew : (PreferredContext.plug (source subtree q) frames).shape.height ≤ K := by
    rw [hplug q agree,source_shape]
  have hlog := Nat.clog_monotone 2 (Nat.add_le_add_right below.height_le 1)
  have repair : ∀ actual : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight (source subtree p) actual →
      ∃ fresh : AuxiliaryComponent Nat Nat (Tagged Payload),
        Represents followsRight (source subtree q) fresh ∧
        SourcePointer.Rearranges (closed actual) (closed fresh) (6225 * Nat.clog 2 (K + 1) + 90) := by
    intro actual ha
    obtain ⟨fresh,hf,trace⟩ := flip_root_charged hx hy left right p actual ha
    refine ⟨fresh,hf,trace.mono ?_⟩
    dsimp only [K]
    omega
  obtain ⟨out,hout,trace⟩ := repair_context (source subtree p) (source subtree q) sub c frames hs same ordered
    (6225 * Nat.clog 2 (K + 1) + 90) repair K hc hnew
  refine ⟨out,?_,trace.mono ?_⟩
  · rw [hplug q agree] at hout
    exact hout
  · dsimp only [K]
    omega

end TangoSquared.Paper20261030.SecondaryDecomposition
