import ChaCha.Paper20261030.ExposedPayloadOperations

/-!
# Composing all stages of a physical head exchange

The initial tree contains the actual incoming component at its boundary
exit; the final tree contains the rebuilt old component there. Both source
exposures, both reconstructions, and the constant-size physical exchange
are included. Header contents are explicit functions of each source view.
This is a root-to-root trace theorem; the bounded local controller is a
separate obligation.
-/

namespace ChaCha.Paper20261030.PackedPrimary

open ColoredStorage PreferredProjection PrimaryWings HeadBlocks

variable {α ρ τ : Type*} [DecidableEq α]

def nestedTree (values : ρ → τ) (payload : Exit α → Source α (List (Option τ)))
    (headers : Nat → PrefRouter α → Source Nat ρ → List τ)
    (outer inner : PrefRouter α) (direction : Bool) (depth : Nat)
    (outerSource innerSource : Source Nat ρ) : Source α (List (Option τ)) :=
  let child := (encoding (depth+1) inner payload (headers (depth+1) inner innerSource)).tree values innerSource
  (encoding 0 outer (Function.update payload ⟨direction,inner⟩ child)
    (headers 0 outer outerSource)).tree values outerSource

theorem complete_physical_head_exchange
    (before after old incoming : PrefRouter α) (common : List (Exit α)) (direction : Bool)
    (beforeDistinct : before.leaves.Nodup) (afterDistinct : after.leaves.Nodup)
    (oldEnd : before.terminal = old.terminal) (newEnd : after.terminal = incoming.terminal)
    (beforeWord : exits before = common ++ ⟨direction,incoming⟩ :: exits old)
    (afterWord : exits after = common ++ ⟨!direction,old⟩ :: exits incoming)
    (values : ρ → τ) (headPart oldTail newTail : Source Nat ρ)
    (prefixDepths : ∀ d ∈ headPart.shape.leaves, d < common.length)
    (oldDepths : ∀ d ∈ oldTail.shape.leaves, common.length < d)
    (newDepths : ∀ d ∈ newTail.shape.leaves, common.length < d)
    (low oldHigh newHigh terminal : ρ)
    (payload : Exit α → Source α (List (Option τ)))
    (headers : Nat → PrefRouter α → Source Nat ρ → List τ)
    (oldSource incomingSource newSource dormantSource : Source Nat ρ)
    (oldCost incomingCost newCost dormantCost : Nat)
    (oldExpose : SourcePointer.Rearranges oldSource
      (.fork low headPart (.fork oldHigh (.leaf common.length terminal) oldTail)) oldCost)
    (incomingExpose : SourcePointer.Rearranges incomingSource
      (.fork newHigh (.leaf common.length terminal) newTail) incomingCost)
    (newRestore : SourcePointer.Rearranges
      (.fork low headPart (.fork newHigh (.leaf common.length terminal) newTail)) newSource newCost)
    (oldRestore : SourcePointer.Rearranges
      (.fork oldHigh (.leaf common.length terminal) oldTail) dormantSource dormantCost) :
    SourcePointer.Rearranges
      (nestedTree values payload headers before incoming direction common.length oldSource incomingSource)
      (nestedTree values payload headers after old (!direction) common.length newSource dormantSource)
      (68*(oldCost+incomingCost+newCost+dormantCost)+376) := by
  let d := common.length
  let oldView := Source.fork oldHigh (.leaf d terminal) oldTail
  let incomingView := Source.fork newHigh (.leaf d terminal) newTail
  let fullOld := Source.fork low headPart oldView
  let fullNew := Source.fork low headPart incomingView
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
    exact exposed_payload_rearranges before incoming beforeDistinct common (exits old) direction beforeWord
      payload (headers 0 before fullOld) values headPart oldTail
      (fun depth member => Nat.ne_of_lt (prefixDepths depth member))
      (fun depth member => Nat.ne_of_gt (oldDepths depth member)) low oldHigh terminal incomingExecution
  have middle : SourcePointer.Rearranges
      (tree before incoming direction d fullOld incomingView)
      (tree after old (!direction) d fullNew oldView) 288 :=
    decomposed_physical_head_kernel before after old incoming common direction beforeDistinct afterDistinct
      oldEnd newEnd beforeWord afterWord values headPart oldTail newTail prefixDepths oldDepths newDepths
      low oldHigh newHigh terminal payload (headers 0 before fullOld) (headers 0 after fullNew)
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
    exact exposed_payload_rearranges after old afterDistinct common (exits incoming) (!direction) afterWord
      payload (headers 0 after fullNew) values headPart newTail
      (fun depth member => Nat.ne_of_lt (prefixDepths depth member))
      (fun depth member => Nat.ne_of_gt (newDepths depth member)) low newHigh terminal oldExecution
  have last : SourcePointer.Rearranges
      (tree after old (!direction) d fullNew dormantSource)
      (tree after old (!direction) d newSource dormantSource) (68*newCost+12) := by
    let child := (encoding (d+1) old payload (headers (d+1) old dormantSource)).tree values dormantSource
    exact (encoding 0 after (Function.update payload ⟨!direction,old⟩ child)
      (headers 0 after fullNew)).source_rearranges values (headers 0 after newSource) newRestore
  exact ((((first.trans second).trans middle).trans fourth).trans last).mono (by omega)

end ChaCha.Paper20261030.PackedPrimary
