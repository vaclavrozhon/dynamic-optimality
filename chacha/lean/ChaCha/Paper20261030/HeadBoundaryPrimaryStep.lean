import ChaCha.Paper20261030.HeadBoundaryObservation
import ChaCha.Paper20261030.PrimaryExitDistinctness

/-! The boundary calculation uses exactly the colors prescribed by an
actual primary head step. Depths below the boundary form the retained
prefix; depths above it belong to the unchanged old/incoming tails.
The actual exit-list decomposition discharges the color-agreement
hypotheses of the five-record repair.
-/

namespace ChaCha.Paper20261030.PackedPrimary

open ColoredStorage PreferredProjection PrimaryWings Structural

variable {α ρ ι : Type*} [DecidableEq α]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem head_step_colors {x : α} {depth : Nat} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep x depth before after) :
    ∃ (old incoming : PrefRouter α) (direction : Bool),
      color 0 before depth = some direction ∧
      color (depth+1) incoming depth = none ∧
      color 0 after depth = some (!direction) ∧
      color (depth+1) old depth = none ∧
      (∀ key, key < depth → color 0 before key = color 0 after key) ∧
      (∀ key, depth < key → color 0 before key = color (depth+1) old key) ∧
      (∀ key, depth < key → color (depth+1) incoming key = color 0 after key) := by
  obtain ⟨common,old,incoming,direction,length,_,_,beforeWord,afterWord⟩ := head_exit_decomposition step
  subst depth
  refine ⟨old,incoming,direction,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [color,beforeWord,portAt_boundary,Option.map_some]
  · simp [color,portAt]
  · simp only [color,afterWord,portAt_boundary,Option.map_some]
  · simp [color,portAt]
  · intro key below
    simp only [color,beforeWord,afterWord,portAt_prefix common _ key below]
  · intro key above
    simp only [color,beforeWord,portAt_tail common _ _ key above]
  · intro key above
    simp only [color,afterWord,portAt_tail common _ _ key above]

theorem head_step_boundary_views {x : α} {depth : Nat} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep x depth before after) (identifier : ρ → ι)
    (low oldHigh incomingHigh oldTerminal incomingTerminal : ρ)
    (prefixTree oldTail incomingTail : Source Nat ρ)
    (prefixDepths : ∀ key ∈ prefixTree.shape.leaves, key < depth)
    (oldDepths : ∀ key ∈ oldTail.shape.leaves, depth < key)
    (incomingDepths : ∀ key ∈ incomingTail.shape.leaves, depth < key) :
    ∃ (old incoming : PrefRouter α) (records : HeadBoundary.Records ρ ι (Option Bool)),
      HeadBoundary.fromObservations identifier
        (BoundaryReadController.activeResult identifier (color 0 before) low oldHigh oldTerminal depth prefixTree oldTail)
        (BoundaryReadController.sentinelResult identifier (color (depth+1) incoming)
          incomingHigh incomingTerminal depth incomingTail) = some records ∧
      HeadBoundary.activeTree records depth (annotate identifier (color 0 before) (some (identifier low)) prefixTree)
        (annotate identifier (color (depth+1) incoming) (some (identifier incomingHigh)) incomingTail) =
        annotate identifier (color 0 after) none
          (.fork low prefixTree (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)) ∧
      HeadBoundary.dormantTree records depth (annotate identifier (color 0 before) (some (identifier oldHigh)) oldTail) =
        annotate identifier (color (depth+1) old) none (.fork oldHigh (.leaf depth oldTerminal) oldTail) := by
  obtain ⟨old,incoming,direction,oldExit,sentinel,newExit,newSentinel,prefixColors,oldColors,incomingColors⟩ := head_step_colors step
  obtain ⟨records,calculated,activeExact,dormantExact⟩ :=
    HeadBoundary.observed_views identifier (color 0 before) (color (depth+1) incoming)
      (color 0 after) (color (depth+1) old) low oldHigh incomingHigh oldTerminal incomingTerminal
      depth prefixTree oldTail incomingTail direction oldExit sentinel newExit newSentinel
      (fun key member => prefixColors key (prefixDepths key member))
      (fun key member => oldColors key (oldDepths key member))
      (fun key member => incomingColors key (incomingDepths key member))
  exact ⟨old,incoming,records,calculated,activeExact,dormantExact⟩

end ChaCha.Paper20261030.PackedPrimary
