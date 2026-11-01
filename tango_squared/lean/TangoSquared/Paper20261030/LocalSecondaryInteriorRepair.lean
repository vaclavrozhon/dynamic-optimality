import TangoSquared.Paper20261030.LocalSecondaryHeadRepair
import TangoSquared.Paper20261030.LocalContextRepair
import TangoSquared.Paper20261030.SecondaryInteriorRepair
import TangoSquared.Paper20261030.ObservedCutBoundaries

/-! The local secondary repair at a preferred descendant. Its boundary
parameters are exactly the two neighbor-query answers for the interval
stored in the departure record. The fixed head-flip subprogram is run
through at most two boundary wrappers, preserving the whole reference. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition SourceLocalProgram

theorem flip_descendant_controller {a b x y pivot : Nat} (hx : x ≤ pivot) (hy : pivot < y)
    (left : DepthTree x pivot) (right : DepthTree (pivot+1) y)
    (reference : DepthTree a b) (p : DepthSplit → Bool)
    (below : SeparatorPath.Descendant p reference (.node pivot hx hy left right))
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) component) (outside) :
    let lower := (neighbors x component.core).1.map (fun entry => entry.1)
    let upper := (neighbors y component.core).2.map (fun entry => entry.1)
    let repair := PreferenceFlipController.program pivot (!p ⟨x,pivot,y⟩) togglePayload
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight (source reference (Function.update p ⟨x,pivot,y⟩ (!p ⟨x,pivot,y⟩))) out ∧
      ∃ reads cost, Run (IntervalRepairController.program lower upper repair (.opening .start))
        (IntervalRepairController.initial lower upper repair (.opening .start)) ⟨closed component,outside⟩ .done ⟨closed out,outside⟩ reads cost ∧
        cost ≤ 130830*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+958 := by
  dsimp only
  let subtree := DepthTree.node pivot hx hy left right
  let q := Function.update p ⟨x,pivot,y⟩ (!p ⟨x,pivot,y⟩)
  let K := (LocalReferences.depthReference reference).height
  let repair := PreferenceFlipController.program pivot (!p ⟨x,pivot,y⟩) togglePayload
  obtain ⟨sub,frames,subRep,same,beforeBound,afterBound,plug⟩ := descendant_context below component represented
  have agree : ∀ split, split ∉ subtree.nodes → q split = p split := by
    intro split absent
    have different : split ≠ ⟨x,pivot,y⟩ := by
      intro equal
      subst split
      exact absent (by simp [subtree,DepthTree.nodes])
    exact Function.update_of_ne different _ _
  have size := represented_size reference p component represented
  have ordered := represented_ordered reference p component represented
  have newSize : (PreferredContext.plug (source subtree q) frames).shape.height ≤ K := by
    rw [plug q agree,source_shape]
  have rank := Nat.clog_monotone 2 (Nat.add_le_add_right below.height_le 1)
  have correct : ∀ actual : AuxiliaryComponent Nat Nat (Tagged Payload), Represents followsRight (source subtree p) actual →
      ∃ fresh : AuxiliaryComponent Nat Nat (Tagged Payload), Represents followsRight (source subtree q) fresh ∧
        ∃ last reads cost, Run repair (.opening .start) ⟨closed actual,[]⟩ last ⟨closed fresh,[]⟩ reads cost ∧
          cost ≤ 42210*Nat.clog 2 (K+1)+322 := by
    intro actual actualRep
    obtain ⟨fresh,freshRep,reads,cost,run,bound⟩ := flip_root_controller hx hy left right p actual actualRep []
    exact ⟨fresh,freshRep,.done,reads,cost,run,by dsimp only [K]; omega⟩
  obtain ⟨out,outRep,reads,cost,run,bound⟩ := repair_context_controller (source subtree p) (source subtree q) sub component frames
    subRep same ordered repair (.opening .start) (42210*Nat.clog 2 (K+1)+322) correct K size newSize outside
  have boundaries := context_boundary_neighbors subtree p component sub frames same ordered subRep
    (by omega) beforeBound afterBound
  rw [← boundaries.1,← boundaries.2] at run
  rw [plug q agree] at outRep
  exact ⟨out,outRep,reads,cost,run,by dsimp only [K] at bound; omega⟩

end TangoSquared.Paper20261030.SecondaryDecomposition
