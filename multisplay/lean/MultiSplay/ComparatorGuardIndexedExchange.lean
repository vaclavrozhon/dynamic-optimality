import MultiSplay.ComparatorGuardExchange
import MultiSplay.ComparatorGuardBoundaries

/-! # The local projected exchange on an actual indexed reference path -/

namespace MultiSplay.ComparatorGuard

open DynamicOptimality ChaCha Paper20261030
open EndpointEncoding ClassicalSwitch ColoredStorage PreferredProjection PrimaryWings
open ComparatorPrimary (routing signature projected)
open Primary (Key)
open CommonForest

def childRouter {lo pivot hi : Nat} (state : State)
    (left : BST lo pivot) (right : BST (pivot+1) hi) (side : Bool) : PrefRouter Nat :=
  if side then routing (below state true) right else routing (below state false) left

theorem focus_signature {lo pivot hi : Nat} (state : State)
    (left : BST lo pivot) (right : BST (pivot+1) hi) :
    signature (routing state (.node left right)) =
      (state [],sideBoundary (state []) pivot hi)::signature (childRouter state left right (state [])) := by
  cases side : state [] <;>
    simp [routing,signature,exits,side,sideBoundary,childRouter,ComparatorPrimary.lastGap_routing]

theorem focus_toggle_signature {lo pivot hi : Nat} (state : State)
    (left : BST lo pivot) (right : BST (pivot+1) hi) :
    signature (routing (toggle state []) (.node left right)) =
      (!(state []),sideBoundary (!(state [])) pivot hi)::signature (childRouter state left right (!(state []))) := by
  cases side : state [] <;>
    simp [routing,signature,exits,toggle,side,sideBoundary,childRouter,
      ComparatorPrimary.lastGap_routing,below_toggle_empty]

theorem focus_terminal {lo pivot hi : Nat} (state : State)
    (left : BST lo pivot) (right : BST (pivot+1) hi) :
    (routing state (.node left right)).terminal = (childRouter state left right (state [])).terminal := by
  cases side : state [] <;> simp [routing,childRouter,side,PrefRouter.terminal]

theorem focus_toggle_terminal {lo pivot hi : Nat} (state : State)
    (left : BST lo pivot) (right : BST (pivot+1) hi) :
    (routing (toggle state []) (.node left right)).terminal =
      (childRouter state left right (!(state []))).terminal := by
  cases side : state [] <;> simp [routing,childRouter,side,PrefRouter.terminal,toggle,below_toggle_empty]

theorem child_last {lo pivot hi : Nat} (state : State)
    (left : BST lo pivot) (right : BST (pivot+1) hi) (side : Bool)
    (start count : Nat) (source : Source Nat Unit)
    (keys : source.shape.leaves = List.range' start count)
    (enough : (exits (childRouter state left right side)).length ≤ count) :
    GapBST.lastKey (projected start (childRouter state left right side) source) =
      sideBoundary (!side) pivot hi := by
  cases side
  · exact projected_last (below state false) left start count source keys enough
  · exact projected_last (below state true) right start count source keys enough

/-- The real selected path supplies every port and both canonical guards.
The tail sources may include arbitrarily many virtual completion depths. -/
theorem indexed_exchange_service {lo hi bottom pivot top : Nat}
    {state : State} {reference : BST lo hi} {address : Key} {spine : Spine Nat}
    {left : BST bottom pivot} {right : BST (pivot+1) top}
    (path : IndexedPath state reference address spine (.node left right))
    (start count : Nat) (kept : Option (Source Nat Unit)) (oldTail incomingTail : Source Nat Unit)
    (keptKeys : kept.toList.flatMap (fun tree => tree.shape.leaves) = List.range' start address.length)
    (oldKeys : oldTail.shape.leaves = List.range' (start+address.length+1) count)
    (incomingKeys : incomingTail.shape.leaves = List.range' (start+address.length+1) count)
    (oldEnough : (exits (childRouter (restrict state address) left right ((restrict state address) []))).length ≤ count)
    (incomingEnough : (exits (childRouter (restrict state address) left right (!((restrict state address) [])))).length ≤ count) :
    ∃ work ≤ 294,
      Program [GapBST.gaps (projected start (routing state reference)
          (ComparatorStableSuffix.exchangeShape kept (start+address.length) oldTail)),
        GapBST.gaps (projected (start+address.length+1)
          (childRouter (restrict state address) left right (!((restrict state address) []))) incomingTail)]
      (ClassicalSwitch.word ((restrict state address) []) spine.lower spine.upper
        (GapBST.gaps (projected (start+address.length+1)
          (childRouter (restrict state address) left right ((restrict state address) [])) oldTail)).inorder
        (GapBST.gaps (projected (start+address.length+1)
          (childRouter (restrict state address) left right (!((restrict state address) []))) incomingTail)).inorder pivot)
      [GapBST.gaps (projected start (routing (toggle state address) reference)
          (ComparatorStableSuffix.exchangeShape kept (start+address.length) incomingTail)),
        GapBST.gaps (projected (start+address.length+1)
          (childRouter (restrict state address) left right ((restrict state address) [])) oldTail)] work := by
  obtain ⟨front,length,beforePorts,afterPorts,beforeTerminal,afterTerminal⟩ := path.signatures
  rw [focus_signature] at beforePorts
  rw [focus_toggle_signature] at afterPorts
  have beforeEnd := beforeTerminal.trans (focus_terminal (restrict state address) left right)
  have afterEnd := afterTerminal.trans (focus_toggle_terminal (restrict state address) left right)
  obtain ⟨work,bound,run⟩ := exchange_service (routing state reference) (routing (toggle state address) reference)
    (childRouter (restrict state address) left right ((restrict state address) []))
    (childRouter (restrict state address) left right (!((restrict state address) [])))
    start front ((restrict state address) []) pivot top kept oldTail incomingTail
    beforePorts afterPorts beforeEnd afterEnd (by simpa only [length] using keptKeys)
    (by simpa only [length] using range_leaves_lower (start+address.length+1) count oldTail oldKeys)
    (by simpa only [length] using range_leaves_lower (start+address.length+1) count incomingTail incomingKeys)
    (by simpa only [length] using (child_last (restrict state address) left right ((restrict state address) [])
      (start+address.length+1) count oldTail oldKeys oldEnough))
    (by simpa only [length,Bool.not_not] using (child_last (restrict state address) left right (!((restrict state address) []))
      (start+address.length+1) count incomingTail incomingKeys incomingEnough))
  have guards := path.prefixWing_boundaries start kept keptKeys
  rw [guards.1,guards.2,length] at run
  exact ⟨work,bound,run⟩

end MultiSplay.ComparatorGuard
