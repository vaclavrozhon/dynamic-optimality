import ChaCha.Paper20261030.LocalDecompositionHeadRepair
import ChaCha.Paper20261030.SecondaryHeadRepair

/-! A secondary reference-root flip executed by a fixed local program.
The update toggles only the preference bit of the observed head payload;
its stored split interval is preserved. -/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition SourceLocalProgram

def togglePayload (_ : Nat) (value : DepthSplit×Bool) : DepthSplit×Bool := (value.1,!value.2)

theorem flip_root_controller {a b cut : Nat} (ha : a ≤ cut) (hb : cut < b)
    (l : DepthTree a cut) (r : DepthTree (cut+1) b) (p : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source (.node cut ha hb l r) p) component) (outside) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight (source (.node cut ha hb l r) (Function.update p ⟨a,cut,b⟩ (!p ⟨a,cut,b⟩))) out ∧
      ∃ reads cost, Run (PreferenceFlipController.program cut (!p ⟨a,cut,b⟩) togglePayload) (.opening .start)
        ⟨closed component,outside⟩ .done ⟨closed out,outside⟩ reads cost ∧
        cost ≤ 42210*Nat.clog 2 ((LocalReferences.depthReference (.node cut ha hb l r)).height+1)+322 := by
  let reference := DepthTree.node cut ha hb l r
  let K := (LocalReferences.depthReference reference).height
  have size := represented_size reference p component represented
  have ordered := represented_ordered reference p component represented
  have rank := Nat.clog_monotone 2 (Nat.add_le_add_right size 1)
  cases direction : p ⟨a,cut,b⟩
  · have old : followsRight (0,⟨cut,((⟨a,cut,b⟩,p ⟨a,cut,b⟩),false)⟩) = false := direction
    obtain ⟨lc,rc,hl,hr,same⟩ := represented.left_view old
    obtain ⟨out,output,reads,cost,run,bound⟩ := left_head_controller followsRight
      (0,⟨cut,((⟨a,cut,b⟩,p ⟨a,cut,b⟩),false)⟩) (source l p) (source r p) lc rc component hl hr same
      old rfl ordered togglePayload (by change (!p ⟨a,cut,b⟩) = true; rw [direction]; rfl) outside
    have incomingSize := represented_size r p rc hr
    have incomingHeight : (LocalReferences.depthReference r).height ≤ K := by
      simp only [K,reference,LocalReferences.depthReference,RouterProjection.Router.height]
      omega
    have incomingRank := Nat.clog_monotone 2 (show rc.core.size+1 ≤ K+1 by omega)
    refine ⟨out,?_,reads,cost,?_,by dsimp only [K,reference] at rank incomingRank; omega⟩
    · simpa only [togglePayload,direction,Bool.not_false,source_flip_root] using output
    · simpa only [direction,Bool.not_false] using run
  · have old : followsRight (0,⟨cut,((⟨a,cut,b⟩,p ⟨a,cut,b⟩),false)⟩) = true := direction
    obtain ⟨lc,rc,hl,hr,same⟩ := represented.right_view old
    obtain ⟨out,output,reads,cost,run,bound⟩ := right_head_controller followsRight
      (0,⟨cut,((⟨a,cut,b⟩,p ⟨a,cut,b⟩),false)⟩) (source l p) (source r p) lc rc component hl hr same
      old rfl ordered togglePayload (by change (!p ⟨a,cut,b⟩) = false; rw [direction]; rfl) outside
    have incomingSize := represented_size l p lc hl
    have incomingHeight : (LocalReferences.depthReference l).height ≤ K := by
      simp only [K,reference,LocalReferences.depthReference,RouterProjection.Router.height]
      omega
    have incomingRank := Nat.clog_monotone 2 (show lc.core.size+1 ≤ K+1 by omega)
    refine ⟨out,?_,reads,cost,?_,by dsimp only [K,reference] at rank incomingRank; omega⟩
    · simpa only [togglePayload,direction,Bool.not_true,source_flip_root] using output
    · simpa only [direction,Bool.not_true] using run

end ChaCha.Paper20261030.SecondaryDecomposition
