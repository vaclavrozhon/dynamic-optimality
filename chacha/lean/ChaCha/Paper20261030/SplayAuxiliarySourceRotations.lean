import ChaCha.Paper20261030.SplayAuxiliaryPayload
import ChaCha.Paper20261030.Restriction
import ChaCha.Paper20261030.GapBSTRepresentation

/-!
# Exact ordinary separator rotations with opaque leaf payloads

A source rotation preserves every original leaf label and record. It is
an ordinary BST rotation of separator vertices, at any location, with
no pointer-navigation charge. This is the shared search-plus-rotations
model chosen for the final algorithm.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open DynamicOptimality.SearchRotation
open ColoredStorage

variable {α κ : Type*}

inductive SourceRotation : Source α κ → Source α κ → Prop
  | right (a b c : Source α κ) (x y : κ) :
      SourceRotation (.fork y (.fork x a b) c) (.fork x a (.fork y b c))
  | left (a b c : Source α κ) (x y : κ) :
      SourceRotation (.fork x a (.fork y b c)) (.fork y (.fork x a b) c)
  | inLeft {a b : Source α κ} (step : SourceRotation a b) (key : κ) (r : Source α κ) :
      SourceRotation (.fork key a r) (.fork key b r)
  | inRight (l : Source α κ) (key : κ) {a b : Source α κ} (step : SourceRotation a b) :
      SourceRotation (.fork key l a) (.fork key l b)

inductive SourceRotations : Source α κ → Source α κ → Nat → Prop
  | refl (source : Source α κ) : SourceRotations source source 0
  | step {a b c : Source α κ} {cost : Nat}
      (first : SourceRotation a b) (rest : SourceRotations b c cost) :
      SourceRotations a c (cost+1)

theorem SourceRotation.payloads {a b : Source α κ} (step : SourceRotation a b) :
    leafPayloads a = leafPayloads b := by
  induction step <;> simp_all [leafPayloads,List.append_assoc]

theorem SourceRotation.raw {a b : Source α κ} (step : SourceRotation a b) :
    Rotation (referenceCuts id a) (referenceCuts id b) := by
  induction step with
  | right a b c x y => exact .rootRight _ _ _ _ _
  | left a b c x y => exact .rootLeft _ _ _ _ _
  | inLeft step key r ih => exact .leftContext ih key _
  | inRight l key step ih => exact .rightContext _ key ih

theorem SourceRotation.router {a b : Source α κ} (step : SourceRotation a b) :
    Router.Rotation a.shape b.shape := by
  induction step with
  | right => exact .root _ _ _
  | left => exact .rootRev _ _ _
  | inLeft step key r ih => exact .left _ ih
  | inRight l key step ih => exact .right _ ih

theorem SourceRotation.lastKey {a b : Source α κ} (step : SourceRotation a b) :
    GapBST.lastKey a = GapBST.lastKey b := by
  induction step <;> simp_all [GapBST.lastKey]

/-- Separator rotations also induce exactly one rotation on the original
leaf-key gap encoding. No extra physical keys are introduced. -/
theorem SourceRotation.gaps {a b : Source α κ} (step : SourceRotation a b) :
    Rotation (GapBST.gaps a) (GapBST.gaps b) := by
  induction step with
  | right a b c x y => exact .rootRight _ _ _ _ _
  | left a b c x y => exact .rootLeft _ _ _ _ _
  | inLeft step key r ih =>
      simpa only [GapBST.gaps,step.lastKey] using Rotation.leftContext ih (GapBST.lastKey _) (GapBST.gaps r)
  | inRight l key step ih => exact .rightContext _ _ ih

theorem SourceRotation.encoded {a b : Source α κ} (step : SourceRotation a b) :
    Rotation (GapBST.encode a) (GapBST.encode b) := by
  simpa only [GapBST.encode,step.lastKey] using Rotation.leftContext step.gaps (GapBST.lastKey b) .empty

theorem SourceRotations.encoded {a b : Source α κ} {cost : Nat}
    (run : SourceRotations a b cost) : Rotations (GapBST.encode a) (GapBST.encode b) cost := by
  induction run with
  | refl => exact .refl _
  | step first rest ih => exact .step first.encoded ih

theorem SourceRotations.payloads {a b : Source α κ} {cost : Nat}
    (run : SourceRotations a b cost) : leafPayloads a = leafPayloads b := by
  induction run with
  | refl => rfl
  | step first rest ih => exact first.payloads.trans ih

theorem SourceRotations.raw {a b : Source α κ} {cost : Nat}
    (run : SourceRotations a b cost) :
    Rotations (referenceCuts id a) (referenceCuts id b) cost := by
  induction run with
  | refl => exact .refl _
  | step first rest ih => exact .step first.raw ih

theorem SourceRotations.append {a b c : Source α κ} {firstCost secondCost : Nat}
    (first : SourceRotations a b firstCost) (second : SourceRotations b c secondCost) :
    SourceRotations a c (firstCost+secondCost) := by
  induction first with
  | refl => simpa only [Nat.zero_add] using second
  | step first rest ih =>
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using SourceRotations.step first (ih second)

/-- Every actual raw rotation lifts with exactly one source rotation. -/
theorem source_rotation_lift {before after : RawTree κ} (step : Rotation before after)
    (source : Source α κ) (physical : referenceCuts id source = before) :
    ∃ target : Source α κ, SourceRotation source target ∧ referenceCuts id target = after := by
  induction step generalizing source with
  | rootRight a x b y c =>
      cases source with
      | leaf => cases physical
      | fork key left right =>
          cases left with
          | leaf => cases physical
          | fork value first second =>
              simp only [referenceCuts,id_eq,MTR.Tree.node.injEq] at physical
              rcases physical with ⟨⟨rfl,rfl,rfl⟩,rfl,rfl⟩
              exact ⟨_,.right first second right _ _,rfl⟩
  | rootLeft a x b y c =>
      cases source with
      | leaf => cases physical
      | fork key left right =>
          cases right with
          | leaf => cases physical
          | fork value first second =>
              simp only [referenceCuts,id_eq,MTR.Tree.node.injEq] at physical
              rcases physical with ⟨rfl,rfl,⟨rfl,rfl,rfl⟩⟩
              exact ⟨_,.left left first second _ _,rfl⟩
  | leftContext step key right ih =>
      cases source with
      | leaf => cases physical
      | fork value left rightSource =>
          simp only [referenceCuts,id_eq,MTR.Tree.node.injEq] at physical
          rcases physical with ⟨leftEq,rfl,rightEq⟩
          obtain ⟨next,move,same⟩ := ih left leftEq
          refine ⟨_,.inLeft move _ rightSource,?_⟩
          simp only [referenceCuts,id_eq,same,rightEq]
  | rightContext left key step ih =>
      cases source with
      | leaf => cases physical
      | fork value leftSource right =>
          simp only [referenceCuts,id_eq,MTR.Tree.node.injEq] at physical
          rcases physical with ⟨leftEq,rfl,rightEq⟩
          obtain ⟨next,move,same⟩ := ih right rightEq
          refine ⟨_,.inRight leftSource _ move,?_⟩
          simp only [referenceCuts,id_eq,same,leftEq]

theorem source_rotations_lift {before after : RawTree κ} {cost : Nat}
    (run : Rotations before after cost) (source : Source α κ)
    (physical : referenceCuts id source = before) :
    ∃ target : Source α κ, SourceRotations source target cost ∧ referenceCuts id target = after := by
  induction run generalizing source with
  | refl tree => exact ⟨source,.refl _,physical⟩
  | step first rest ih =>
      obtain ⟨middle,move,same⟩ := source_rotation_lift first source physical
      obtain ⟨target,remaining,endpoint⟩ := ih middle same
      exact ⟨target,.step move remaining,endpoint⟩

/-- The endpoint source is fixed by its physical raw tree and preserved
payloads; the lift cannot silently select a different attachment tree. -/
theorem source_rotations_of_raw {before after : Source α κ} {cost : Nat}
    (run : Rotations (referenceCuts id before) (referenceCuts id after) cost)
    (payloads : leafPayloads before = leafPayloads after) : SourceRotations before after cost := by
  obtain ⟨target,actual,physical⟩ := source_rotations_lift run before rfl
  have same : target = after := source_ext physical (actual.payloads.symm.trans payloads)
  simpa only [same] using actual

end ChaCha.Paper20261030.SplayAuxiliary
