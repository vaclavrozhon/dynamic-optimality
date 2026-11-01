import MultiSplay.ComparatorGuardLocalFacts
import MultiSplay.ComparatorGuardReflected

/-! # Exact local exchange on literal projected source trees -/

namespace MultiSplay.ComparatorGuard

open TangoSquared Paper20261030 ColoredStorage PreferredProjection
open ComparatorPrimary (signature projected)
open CommonForest

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

def sideBoundary (side : Bool) (pivot upper : Nat) : Nat := if side then pivot else upper

def activeSource (side : Bool) (left right tailLeft tailRight : Block Nat)
    (terminal pivot upper : Nat) : Plain Nat :=
  if side then rightSource left right tailLeft tailRight terminal pivot
  else leftSource left right tailLeft tailRight terminal upper

theorem active_exposed (start : Nat) (primary : PrefRouter Nat)
    (kept : Option (Source Nat Unit)) (depth pivot upper : Nat) (tail : Source Nat Unit) (side : Bool)
    (color : PackedPrimary.color start primary depth = some side)
    (label : ComparatorPrimary.lastGap (PackedPrimary.label start primary depth).subtree = sideBoundary side pivot upper) :
    eraseRecords (projected start primary (ComparatorStableSuffix.exchangeShape kept depth tail)) =
      activeSource side (prefixWing start primary true kept)
        ((prefixWing start primary false kept).map Source.mirror)
        (boundaryWing start primary true tail) ((boundaryWing start primary false tail).map Source.mirror)
        primary.terminal pivot upper := by
  cases side
  · exact exposed_left start primary kept depth upper tail color label
  · exact exposed_right start primary kept depth pivot tail color label

theorem active_block_service (left right oldLeft oldRight incomingLeft incomingRight : Block Nat)
    (oldTerminal incomingTerminal pivot upper : Nat) (side : Bool)
    (oldLast : GapBST.lastKey (componentBlock oldLeft oldRight oldTerminal) = sideBoundary (!side) pivot upper)
    (incomingLast : GapBST.lastKey (componentBlock incomingLeft incomingRight incomingTerminal) = sideBoundary side pivot upper) :
    ∃ work ≤ 294,
      Program [GapBST.gaps (activeSource side left right oldLeft oldRight oldTerminal pivot upper),
        GapBST.gaps (componentBlock incomingLeft incomingRight incomingTerminal)]
      (ClassicalSwitch.word side (lowerBoundary left) (upperBoundary upper right)
        (GapBST.gaps (componentBlock oldLeft oldRight oldTerminal)).inorder
        (GapBST.gaps (componentBlock incomingLeft incomingRight incomingTerminal)).inorder pivot)
      [GapBST.gaps (activeSource (!side) left right incomingLeft incomingRight incomingTerminal pivot upper),
        GapBST.gaps (componentBlock oldLeft oldRight oldTerminal)] work := by
  cases side
  · simpa only [activeSource,Bool.false_eq_true,if_false,Bool.not_false,if_true,
      ClassicalSwitch.word] using
      left_block_service left right oldLeft oldRight incomingLeft incomingRight oldTerminal incomingTerminal
        pivot upper oldLast incomingLast
  · exact right_block_service left right oldLeft oldRight incomingLeft incomingRight oldTerminal incomingTerminal
      pivot upper oldLast incomingLast

/-- The only hypotheses concern concrete reference ports and literal
source words. The output is an actual original-key forest program. -/
theorem exchange_service (before after old incoming : PrefRouter Nat)
    (start : Nat) (front : List (Bool × Nat)) (side : Bool) (pivot upper : Nat)
    (kept : Option (Source Nat Unit)) (oldTail incomingTail : Source Nat Unit)
    (beforePorts : signature before = front ++ (side,sideBoundary side pivot upper)::signature old)
    (afterPorts : signature after = front ++ (!side,sideBoundary (!side) pivot upper)::signature incoming)
    (beforeTerminal : before.terminal = old.terminal) (afterTerminal : after.terminal = incoming.terminal)
    (keptKeys : kept.toList.flatMap (fun tree => tree.shape.leaves) = List.range' start front.length)
    (oldBelow : ∀ key ∈ oldTail.shape.leaves, start+front.length+1 ≤ key)
    (incomingBelow : ∀ key ∈ incomingTail.shape.leaves, start+front.length+1 ≤ key)
    (oldLast : GapBST.lastKey (projected (start+front.length+1) old oldTail) = sideBoundary (!side) pivot upper)
    (incomingLast : GapBST.lastKey (projected (start+front.length+1) incoming incomingTail) = sideBoundary side pivot upper) :
    ∃ work ≤ 294,
      Program [GapBST.gaps (projected start before
          (ComparatorStableSuffix.exchangeShape kept (start+front.length) oldTail)),
        GapBST.gaps (projected (start+front.length+1) incoming incomingTail)]
      (ClassicalSwitch.word side (lowerBoundary (prefixWing start before true kept))
        (upperBoundary upper ((prefixWing start before false kept).map Source.mirror))
        (GapBST.gaps (projected (start+front.length+1) old oldTail)).inorder
        (GapBST.gaps (projected (start+front.length+1) incoming incomingTail)).inorder pivot)
      [GapBST.gaps (projected start after
          (ComparatorStableSuffix.exchangeShape kept (start+front.length) incomingTail)),
        GapBST.gaps (projected (start+front.length+1) old oldTail)] work := by
  have oldWings : ∀ wing, boundaryWing start before wing oldTail =
      boundaryWing (start+front.length+1) old wing oldTail := by
    intro wing
    apply boundaryWing_tail start (start+front.length+1) before old
      (front++[(side,sideBoundary side pivot upper)]) wing oldTail
    · simpa only [List.append_assoc,List.singleton_append] using beforePorts
    · simp [List.length_append,Nat.add_assoc]
    · exact oldBelow
  have incomingWings : ∀ wing, boundaryWing start after wing incomingTail =
      boundaryWing (start+front.length+1) incoming wing incomingTail := by
    intro wing
    apply boundaryWing_tail start (start+front.length+1) after incoming
      (front++[(!side,sideBoundary (!side) pivot upper)]) wing incomingTail
    · simpa only [List.append_assoc,List.singleton_append] using afterPorts
    · simp [List.length_append,Nat.add_assoc]
    · exact incomingBelow
  have common : ∀ wing, prefixWing start before wing kept = prefixWing start after wing kept := by
    intro wing
    exact prefixWing_congr start before after front _ _ kept wing beforePorts afterPorts keptKeys
  have beforeBoundary := signature_boundary start before front _ side (sideBoundary side pivot upper) beforePorts
  have afterBoundary := signature_boundary start after front _ (!side) (sideBoundary (!side) pivot upper) afterPorts
  have first := active_exposed start before kept (start+front.length) pivot upper oldTail side
    beforeBoundary.1 beforeBoundary.2
  have last := active_exposed start after kept (start+front.length) pivot upper incomingTail (!side)
    afterBoundary.1 afterBoundary.2
  rw [oldWings true,oldWings false,beforeTerminal] at first
  rw [← common true,← common false,incomingWings true,incomingWings false,afterTerminal] at last
  obtain ⟨work,bound,run⟩ := active_block_service
    (prefixWing start before true kept) ((prefixWing start before false kept).map Source.mirror)
    (boundaryWing (start+front.length+1) old true oldTail)
    ((boundaryWing (start+front.length+1) old false oldTail).map Source.mirror)
    (boundaryWing (start+front.length+1) incoming true incomingTail)
    ((boundaryWing (start+front.length+1) incoming false incomingTail).map Source.mirror)
    old.terminal incoming.terminal pivot upper side
    (by rw [← projected_erase,last_eraseRecords]; exact oldLast)
    (by rw [← projected_erase,last_eraseRecords]; exact incomingLast)
  rw [← first,← last,← projected_erase,← projected_erase] at run
  simpa only [gaps_eraseRecords] using (show ∃ work ≤ 294, _ from ⟨work,bound,run⟩)

end MultiSplay.ComparatorGuard
