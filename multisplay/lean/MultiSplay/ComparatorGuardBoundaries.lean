import MultiSplay.ComparatorGuardPorts
import MultiSplay.ComparatorGuardPortSelection
import MultiSplay.ClassicalSwitchMarked

/-! # The projected prefix blocks are the actual ancestor guards

The left prefix lists lower ancestors directly. The right prefix lists gap
boundaries: prepending the current upper endpoint and deleting the final
external boundary recovers the upper ancestors. This distinction ensures
that no external endpoint is mistaken for a real guard key.
-/

namespace MultiSplay.ComparatorGuard

open DynamicOptimality TangoSquared Paper20261030
open EndpointEncoding ClassicalSwitch ColoredStorage PreferredProjection PrimaryWings
open ComparatorPrimary (routing signature lastGap)
open Primary (Key)

def portWord (side : Bool) (ports : List (Bool × Nat)) : List Nat :=
  (ports.filter (fun entry => decide (entry.1 = side))).map Prod.snd

@[simp] theorem blockLeaves_mirror (block : Block Nat) :
    blockLeaves (block.map Source.mirror) = (blockLeaves block).reverse := by
  cases block <;> simp [blockLeaves,Source.mirror_leaves]

private theorem upperKeys_append (inside outside : Spine Nat) :
    (inside ++ outside).upperKeys = inside.upperKeys ++ outside.upperKeys := by
  induction inside with
  | nil => simp [Spine.upperKeys]
  | cons entry rest ih =>
      obtain ⟨side,key⟩ := entry
      cases side <;> simp [Spine.upperKeys,ih,List.append_assoc]

/-- These signatures belong to the actual indexed path, not an arbitrary
same-domain rearrangement of its ancestor keys. -/
theorem IndexedPath.prefix_ports {lo hi bottom top : Nat} {state : State}
    {reference : BST lo hi} {address : Key} {spine : Spine Nat} {focus : BST bottom top}
    (path : IndexedPath state reference address spine focus) :
    portWord true ((signature (routing state reference)).take address.length) = spine.lowerKeys ∧
      top :: (portWord false ((signature (routing state reference)).take address.length)).reverse =
        spine.upperKeys ++ [hi] := by
  induction path with
  | here state reference => simp [portWord,Spine.lowerKeys,Spine.upperKeys]
  | @left lo key hi bottom top state left right address spine focus agrees rest ih =>
      have sig : signature (routing state (.node left right)) =
          (false,hi) :: signature (routing (EndpointEncoding.below state false) left) := by
        simp [routing,agrees,signature,exits,ComparatorPrimary.lastGap_routing]
      rw [sig]
      simp only [List.length_cons,List.take_succ_cons,portWord,List.filter_cons,List.map_cons,
        Bool.false_eq_true,decide_false,if_false,decide_true,if_true,List.reverse_cons]
      constructor
      · simpa only [portWord,Spine.lowerKeys_append,Spine.lowerKeys,List.nil_append] using ih.1
      · simpa only [portWord,upperKeys_append,Spine.upperKeys,List.append_assoc,List.cons_append] using
          congrArg (fun word => word ++ [hi]) ih.2
  | @right lo key hi bottom top state left right address spine focus agrees rest ih =>
      have sig : signature (routing state (.node left right)) =
          (true,key) :: signature (routing (EndpointEncoding.below state true) right) := by
        simp [routing,agrees,signature,exits,ComparatorPrimary.lastGap_routing]
      rw [sig]
      simp only [List.length_cons,List.take_succ_cons,portWord,List.filter_cons,List.map_cons,
        Bool.true_eq_false,Bool.false_eq_true,decide_false,if_false,decide_true,if_true,List.reverse_cons]
      constructor
      · simpa only [portWord,Spine.lowerKeys_append,Spine.lowerKeys,List.cons_append,List.nil_append] using
          congrArg (List.cons key) ih.1
      · simpa only [portWord,upperKeys_append,Spine.upperKeys,List.append_nil] using ih.2

theorem IndexedPath.front_ports {lo hi bottom top : Nat} {state : State}
    {reference : BST lo hi} {address : Key} {spine : Spine Nat} {focus : BST bottom top}
    (path : IndexedPath state reference address spine focus)
    (front tail : List (Bool × Nat)) (length : front.length = address.length)
    (ports : signature (routing state reference) = front ++ tail) :
    portWord true front = spine.lowerKeys ∧
      top :: (portWord false front).reverse = spine.upperKeys ++ [hi] := by
  have taken : (signature (routing state reference)).take address.length = front := by
    rw [ports,← length,List.take_left]
  simpa only [taken] using path.prefix_ports

private theorem lowerKeys_injective : Function.Injective (Boundary.lowerKeys (α := Nat)) := by
  intro first second equal
  cases first with
  | absent => cases second <;> simp_all [Boundary.lowerKeys]
  | guard outside key =>
      cases second with
      | absent => simp [Boundary.lowerKeys] at equal
      | guard other next =>
          obtain ⟨same,keys⟩ := List.append_inj' equal (by rfl)
          have keyEq : key = next := by simpa using keys
          subst other
          subst next
          rfl

private theorem upperKeys_injective : Function.Injective (Boundary.upperKeys (α := Nat)) := by
  intro first second equal
  cases first <;> cases second <;> simp_all [Boundary.upperKeys]

@[simp] theorem lowerBoundary_keys (block : Block Nat) :
    (lowerBoundary block).lowerKeys = blockLeaves block := by
  cases block with
  | none => rfl
  | some tree =>
      simpa only [lowerBoundary,Boundary.lowerKeys,blockLeaves,Option.toList,List.flatMap_cons,
        List.flatMap_nil,List.append_nil] using GapBST.gaps_word tree

@[simp] theorem upperBoundary_keys (upper : Nat) (block : Block Nat) :
    (upperBoundary upper block).upperKeys = (upper :: blockLeaves block).dropLast := by
  cases block with
  | none => rfl
  | some tree =>
      simp only [upperBoundary,Boundary.upperKeys,blockLeaves,Option.toList,List.flatMap_cons,
        List.flatMap_nil,List.append_nil,← GapBST.gaps_word]
      rw [← List.cons_append,List.dropLast_append_cons]
      simp only [List.dropLast_singleton,List.append_nil]

/-- Any two literal blocks with the projected prefix words have exactly the
nearest lower and upper reference ancestor boundaries required by `word`.
Empty blocks give absent guards, also when the focused subtree is empty. -/
theorem IndexedPath.boundaries {lo hi bottom top : Nat} {state : State}
    {reference : BST lo hi} {address : Key} {spine : Spine Nat} {focus : BST bottom top}
    (path : IndexedPath state reference address spine focus)
    (front tail : List (Bool × Nat)) (length : front.length = address.length)
    (ports : signature (routing state reference) = front ++ tail)
    (left right : Block Nat)
    (leftWord : blockLeaves left = portWord true front)
    (rightWord : blockLeaves right = (portWord false front).reverse) :
    lowerBoundary left = spine.lower ∧ upperBoundary top right = spine.upper := by
  obtain ⟨lower,upper⟩ := path.front_ports front tail length ports
  constructor
  · apply lowerKeys_injective
    rw [lowerBoundary_keys,leftWord,lower,Spine.lower_domain]
  · apply upperKeys_injective
    rw [upperBoundary_keys,rightWord,upper,Spine.upper_domain,List.dropLast_append_cons]
    simp only [List.dropLast_singleton,List.append_nil]

/-- The actual retained depth prefix supplies the required guards directly.
Its length is the relative focus depth, while `start` is the global depth
of this component; these offsets are never identified. -/
theorem IndexedPath.prefixWing_boundaries {lo hi bottom top : Nat} {state : State}
    {reference : BST lo hi} {address : Key} {spine : Spine Nat} {focus : BST bottom top}
    (path : IndexedPath state reference address spine focus) (start : Nat)
    (kept : Option (Source Nat Unit))
    (keys : kept.toList.flatMap (fun tree => tree.shape.leaves) = List.range' start address.length) :
    lowerBoundary (prefixWing start (routing state reference) true kept) = spine.lower ∧
      upperBoundary top ((prefixWing start (routing state reference) false kept).map Source.mirror) =
        spine.upper := by
  obtain ⟨front,length,ports,_,_,_⟩ := path.signatures
  apply path.boundaries front _ length ports
  · exact prefixWing_word start (routing state reference) front _ kept true ports (by simpa only [length] using keys)
  · rw [blockLeaves_mirror]
    exact congrArg List.reverse
      (prefixWing_word start (routing state reference) front _ kept false ports (by simpa only [length] using keys))

end MultiSplay.ComparatorGuard
