import MultiSplay.ComparatorIncomingSeam

/-! # The two seam operations preserve genuine owner memory

The detached old tail and the incoming tail have the ordinary suffix
convention at `d+1`. Their genuine interval bits are unchanged. The input
to attachment already has the existing separator `d`; neither operation
adds a sentinel to the independent tail's actual key set.
-/

namespace MultiSplay.ComparatorStableSuffix

open TangoSquared
open Paper20261030
open ColoredStorage Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open SecondaryDecomposition
open ComparatorSuffix
open Secondary (intervalUpdate)

theorem detach_stable_charged {a b : Nat} (reference : DepthTree a b)
    (start d : Nat) (earlier : start ≤ d) (valid : a ≤ d ∧ d < b)
    (memory : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (suffixSource reference (intervalUpdate d (bits start memory)) d ⟨valid.1,by omega⟩) component) :
    ∃ (tail : AuxiliaryComponent Nat Nat (Tagged Payload)) (boundary : Cached),
      boundary.2.1 = d ∧
      Represents followsRight
        (suffixSource reference (bits (d+1) memory) (d+1) ⟨by omega,by omega⟩) tail ∧
      SourcePointer.Rearranges (closed component)
        (.fork boundary (terminalLeaf d) (closed tail))
        (12450 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 96) := by
  obtain ⟨tail,boundary,key,tailRep,run⟩ := ComparatorPreparedSuffix.expose_tail_charged
    reference (intervalUpdate d (bits start memory)) d ⟨valid.1,by omega⟩
    (prepared_terminal reference start d memory ⟨valid.1,by omega⟩) valid.2 component represented
  rw [prepared_tail_source reference start d earlier _ memory] at tailRep
  exact ⟨tail,boundary,key,tailRep,run⟩

theorem attach_stable_charged {a b : Nat} (reference : DepthTree a b)
    (start d : Nat) (earlier : start ≤ d) (valid : a ≤ d ∧ d < b)
    (memory : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (suffixSource reference (bits (d+1) memory) (d+1) ⟨by omega,by omega⟩) component) :
    ∃ (pivot : Cached) (out : AuxiliaryComponent Nat Nat (Tagged Payload)),
      pivot.2.1 = d ∧ entry pivot = false ∧ followsRight pivot = false ∧
      Represents followsRight
        (suffixSource reference (intervalUpdate d (bits start memory)) d ⟨valid.1,by omega⟩) out ∧
      SourcePointer.Rearranges (.fork pivot (terminalLeaf d) (closed component)) (closed out)
        (7215 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 178) := by
  have ordered := represented_stable_ordered reference (d+1) ⟨by omega,by omega⟩ memory component represented
  have preparedRep : Represents followsRight
      (suffixSource reference (intervalUpdate d (bits start memory)) (d+1) ⟨by omega,by omega⟩) component := by
    rw [prepared_tail_source reference start d earlier _ memory]
    exact represented
  exact ComparatorIncomingSeam.attach_charged reference (intervalUpdate d (bits start memory)) d valid
    (prepared_terminal reference start d memory ⟨valid.1,by omega⟩) component preparedRep ordered

/-- The actual preparation consumes a separator already present at the
root. Its right child is exactly the old independent incoming tail. -/
theorem attach_stable_program {a b : Nat} (reference : DepthTree a b)
    (start d : Nat) (earlier : start ≤ d) (valid : a ≤ d ∧ d < b)
    (memory : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (suffixSource reference (bits (d+1) memory) (d+1) ⟨by omega,by omega⟩) component) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight
        (suffixSource reference (intervalUpdate d (bits start memory)) d ⟨valid.1,by omega⟩) out ∧
      ∃ work ≤ 12 * (7215 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 179),
        CommonForest.Program [.node .empty d (GapBST.gaps (closed component))] []
          [GapBST.gaps (closed out)] work := by
  obtain ⟨pivot,out,_,_,_,outRep,run⟩ := attach_stable_charged reference start d earlier valid memory component represented
  obtain ⟨work,bound,program⟩ := ComparatorGap.rearranges_program run
  refine ⟨out,outRep,work,by omega,?_⟩
  exact program

end MultiSplay.ComparatorStableSuffix
