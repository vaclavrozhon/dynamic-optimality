import ChaCha.Paper20261030.PrimaryPhysicalRootKernel

/-! All four source transformations and the physical exchange at depth zero. -/

namespace ChaCha.Paper20261030.PackedPrimary

open ColoredStorage PreferredProjection PrimaryWings HeadBlocks

variable {α ρ τ : Type*} [DecidableEq α]

theorem complete_physical_root_exchange
    (before after old incoming : PrefRouter α) (direction : Bool)
    (beforeDistinct : before.leaves.Nodup) (afterDistinct : after.leaves.Nodup)
    (oldEnd : before.terminal = old.terminal) (newEnd : after.terminal = incoming.terminal)
    (beforeWord : exits before = ⟨direction,incoming⟩ :: exits old)
    (afterWord : exits after = ⟨!direction,old⟩ :: exits incoming)
    (values : ρ → τ) (oldTail newTail : Source Nat ρ)
    (oldDepths : ∀ d ∈ oldTail.shape.leaves, 0 < d)
    (newDepths : ∀ d ∈ newTail.shape.leaves, 0 < d)
    (oldHigh newHigh terminal : ρ)
    (payload : Exit α → Source α (List (Option τ)))
    (headers : Nat → PrefRouter α → Source Nat ρ → List τ)
    (oldSource incomingSource newSource dormantSource : Source Nat ρ)
    (oldCost incomingCost newCost dormantCost : Nat)
    (oldExpose : SourcePointer.Rearranges oldSource
      (.fork oldHigh (.leaf 0 terminal) oldTail) oldCost)
    (incomingExpose : SourcePointer.Rearranges incomingSource
      (.fork newHigh (.leaf 0 terminal) newTail) incomingCost)
    (newRestore : SourcePointer.Rearranges
      (.fork newHigh (.leaf 0 terminal) newTail) newSource newCost)
    (oldRestore : SourcePointer.Rearranges
      (.fork oldHigh (.leaf 0 terminal) oldTail) dormantSource dormantCost) :
    SourcePointer.Rearranges
      (nestedTree values payload headers before incoming direction 0 oldSource incomingSource)
      (nestedTree values payload headers after old (!direction) 0 newSource dormantSource)
      (68*(oldCost+incomingCost+newCost+dormantCost)+376) := by
  let d := 0
  let oldView := Source.fork oldHigh (.leaf d terminal) oldTail
  let incomingView := Source.fork newHigh (.leaf d terminal) newTail
  let fullOld := oldView
  let fullNew := incomingView
  let tree := nestedTree values payload headers
  have first : SourcePointer.Rearranges
      (tree before incoming direction d oldSource incomingSource)
      (tree before incoming direction d fullOld incomingSource) (68*oldCost+12) := by
    let child := (encoding (d+1) incoming payload (headers (d+1) incoming incomingSource)).tree values incomingSource
    exact (encoding 0 before (Function.update payload ⟨direction,incoming⟩ child)
      (headers 0 before oldSource)).source_rearranges values (headers 0 before fullOld) oldExpose
  have incomingExecution : SourcePointer.Rearranges
      ((encoding (d+1) incoming payload (headers (d+1) incoming incomingSource)).tree values incomingSource)
      ((encoding (d+1) incoming payload (headers (d+1) incoming incomingView)).tree values incomingView)
      (68*incomingCost+12) :=
    (encoding (d+1) incoming payload (headers (d+1) incoming incomingSource)).source_rearranges
      values (headers (d+1) incoming incomingView) incomingExpose
  have second : SourcePointer.Rearranges
      (tree before incoming direction d fullOld incomingSource)
      (tree before incoming direction d fullOld incomingView) (68*incomingCost+32) := by
    exact root_payload_rearranges before incoming beforeDistinct (exits old) direction beforeWord
      payload (headers 0 before fullOld) values oldTail
      (fun depth member => Nat.ne_of_gt (oldDepths depth member)) oldHigh terminal incomingExecution
  have middle : SourcePointer.Rearranges
      (tree before incoming direction d fullOld incomingView)
      (tree after old (!direction) d fullNew oldView) 288 :=
    decomposed_physical_root_kernel before after old incoming direction beforeDistinct afterDistinct
      oldEnd newEnd beforeWord afterWord values oldTail newTail oldDepths newDepths
      oldHigh newHigh terminal payload (headers 0 before fullOld) (headers 0 after fullNew)
      (headers (d+1) old oldView) (headers (d+1) incoming incomingView)
  have oldExecution : SourcePointer.Rearranges
      ((encoding (d+1) old payload (headers (d+1) old oldView)).tree values oldView)
      ((encoding (d+1) old payload (headers (d+1) old dormantSource)).tree values dormantSource)
      (68*dormantCost+12) :=
    (encoding (d+1) old payload (headers (d+1) old oldView)).source_rearranges
      values (headers (d+1) old dormantSource) oldRestore
  have fourth : SourcePointer.Rearranges
      (tree after old (!direction) d fullNew oldView)
      (tree after old (!direction) d fullNew dormantSource) (68*dormantCost+32) := by
    exact root_payload_rearranges after old afterDistinct (exits incoming) (!direction) afterWord
      payload (headers 0 after fullNew) values newTail
      (fun depth member => Nat.ne_of_gt (newDepths depth member)) newHigh terminal oldExecution
  have last : SourcePointer.Rearranges
      (tree after old (!direction) d fullNew dormantSource)
      (tree after old (!direction) d newSource dormantSource) (68*newCost+12) := by
    let child := (encoding (d+1) old payload (headers (d+1) old dormantSource)).tree values dormantSource
    exact (encoding 0 after (Function.update payload ⟨!direction,old⟩ child)
      (headers 0 after fullNew)).source_rearranges values (headers 0 after newSource) newRestore
  exact ((((first.trans second).trans middle).trans fourth).trans last).mono (by omega)

end ChaCha.Paper20261030.PackedPrimary
