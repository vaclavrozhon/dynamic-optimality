import MultiSplay.StackShift

/-!
# Transporting complete persistent representations

A change of ordinal origin retains every recursive heavy and rib stack and
preserves the total potential exactly. The source and represented tree both
undergo the same shape-preserving shift from `OrdinalShift.tree`.
-/

namespace MultiSplay.OrdinalShift

open Splay.Tree (BST)
open Splay.Accounting.OfflineConnectedSupport
  (HeavyRepresentation RibRepresentation RibSpineMap SupportFrontier leafSplit)
open Splay.Accounting.OfflineConnectedSupport.FrontierFolding (Context)

mutual

noncomputable def heavy (offset : Nat) {capacity lower upper : Nat}
    {source actual : BST lower upper} (representation : HeavyRepresentation capacity source actual) :
    {shifted : HeavyRepresentation capacity (tree offset source) (tree offset actual) //
      shifted.potential = representation.potential} :=
  match representation with
  | .empty boundary => ⟨.empty (offset + boundary), rfl⟩
  | @HeavyRepresentation.path _ _ root _ original replacement payloads long left right => by
      obtain ⟨mapped, preserved⟩ := heavyPayload offset payloads
      rw [← context_plug, tree_leafSplit]
      refine ⟨.path mapped ?_ (minimumTo offset left (expose_left_frontier offset replacement))
        (maximumTo offset right (expose_right_frontier offset replacement)), ?_⟩
      · simpa only [tree_leafSplit] using context_long offset original (leafSplit root).tree long
      · change left.potential + right.potential + mapped.heavyPotential =
          left.potential + right.potential + payloads.heavyPotential
        rw [preserved]
termination_by sizeOf representation
decreasing_by all_goals simp_wf <;> omega

noncomputable def heavyPayload (offset : Nat) {capacity lower innerLower innerUpper upper : Nat}
    {original replacement : Context lower innerLower innerUpper upper}
    (mapped : Context.PayloadMap (@HeavyRepresentation capacity) original replacement) :
    {shifted : Context.PayloadMap (@HeavyRepresentation capacity)
        (context offset original) (context offset replacement) //
      shifted.heavyPotential = mapped.heavyPotential} :=
  match mapped with
  | .hole lower upper => ⟨.hole (offset + lower) (offset + upper), rfl⟩
  | .low payload tail => by
      obtain ⟨child, childEq⟩ := heavy offset payload
      obtain ⟨rest, restEq⟩ := heavyPayload offset tail
      exact ⟨.low child rest, by simp only [Context.PayloadMap.heavyPotential, childEq, restEq]⟩
  | .high initial payload => by
      obtain ⟨rest, restEq⟩ := heavyPayload offset initial
      obtain ⟨child, childEq⟩ := heavy offset payload
      exact ⟨.high rest child, by simp only [Context.PayloadMap.heavyPotential, childEq, restEq]⟩
termination_by sizeOf mapped
decreasing_by all_goals simp_wf <;> omega

end

mutual

noncomputable def rib (offset : Nat) {capacity lower upper : Nat} {side : Bool}
    {source actual : BST lower upper} (representation : RibRepresentation capacity side source actual) :
    {shifted : RibRepresentation capacity side (tree offset source) (tree offset actual) //
      shifted.potential = representation.potential} :=
  match representation with
  | .minimum payloads stack => by
      obtain ⟨mapped, preserved⟩ := ribPayload offset payloads
      exact ⟨.minimum mapped (foldedMinimumTo offset stack rfl), by
        simpa only [RibRepresentation.potential, foldedMinimumTo_potential] using
          congrArg (fun value => stack.potential + value) preserved⟩
  | .maximum payloads stack => by
      obtain ⟨mapped, preserved⟩ := ribPayload offset payloads
      exact ⟨.maximum mapped (foldedMaximumTo offset stack rfl), by
        simpa only [RibRepresentation.potential, foldedMaximumTo_potential] using
          congrArg (fun value => stack.potential + value) preserved⟩
termination_by sizeOf representation
decreasing_by all_goals simp_wf <;> omega

noncomputable def ribPayload (offset : Nat) {capacity lower upper : Nat} {side : Bool}
    {source : BST lower upper} {portion : SupportFrontier lower upper}
    (mapped : RibSpineMap (@RibRepresentation capacity) side source portion) :
    {shifted : RibSpineMap (@RibRepresentation capacity) side
        (tree offset source) (frontier offset portion) //
      shifted.ribPotential = mapped.ribPotential} :=
  match mapped with
  | .empty side boundary => ⟨.empty side (offset + boundary), rfl⟩
  | .right payload rest => by
      obtain ⟨child, childEq⟩ := rib offset payload
      obtain ⟨tail, tailEq⟩ := ribPayload offset rest
      exact ⟨.right child tail, by simp only [RibSpineMap.ribPotential, childEq, tailEq]⟩
  | .left initial payload => by
      obtain ⟨head, headEq⟩ := ribPayload offset initial
      obtain ⟨child, childEq⟩ := rib offset payload
      rw [frontier_append]
      exact ⟨.left head child, by simp only [RibSpineMap.ribPotential, headEq, childEq]⟩
termination_by sizeOf mapped
decreasing_by all_goals simp_wf <;> omega

end

end MultiSplay.OrdinalShift
