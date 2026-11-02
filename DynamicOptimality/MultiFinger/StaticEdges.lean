import DynamicOptimality.MultiFinger.SimulationBound

/-! A same-tree pointer step is literally an edge move.
The static benchmark cannot hide any rotations: a rotation under a fixed
zipper context would strictly change one of the root-child subtree sizes.
-/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR

variable {α : Type*}

theorem plug_injective (frames : List (Pointer.Frame α)) :
    Function.Injective (fun focus : RawTree α => Pointer.plug focus frames) := by
  induction frames with
  | nil => exact fun _ _ same => same
  | cons frame frames ih =>
    intro first last same
    cases frame with
    | left key right => exact (ChaCha.MTR.Tree.node.inj (ih same)).1
    | right left key => exact (ChaCha.MTR.Tree.node.inj (ih same)).2.2

inductive Edge : Pointer.Cursor α → Pointer.Cursor α → Prop
  | left (a b c : RawTree α) (x y : α) (frames : List (Pointer.Frame α)) :
      Edge ⟨.node (.node a x b) y c,frames⟩ ⟨.node a x b,.left y c::frames⟩
  | right (a b c : RawTree α) (x y : α) (frames : List (Pointer.Frame α)) :
      Edge ⟨.node a x (.node b y c),frames⟩ ⟨.node b y c,.right a x::frames⟩
  | upLeft (a b : RawTree α) (key : α) (frames : List (Pointer.Frame α)) :
      Edge ⟨a,.left key b::frames⟩ ⟨.node a key b,frames⟩
  | upRight (a b : RawTree α) (key : α) (frames : List (Pointer.Frame α)) :
      Edge ⟨b,.right a key::frames⟩ ⟨.node a key b,frames⟩

theorem edge_of_same_tree {before after : Pointer.Cursor α}
    (step : Pointer.Step before after) (same : before.tree = after.tree) : Edge before after := by
  cases step with
  | left a b c x y frames => exact .left a b c x y frames
  | right a b c x y frames => exact .right a b c x y frames
  | upLeft a b key frames => exact .upLeft a b key frames
  | upRight a b key frames => exact .upRight a b key frames
  | rotateRight a b c x y frames =>
    have focus := plug_injective frames same
    have child := congrArg ChaCha.MTR.Tree.size (ChaCha.MTR.Tree.node.inj focus).1
    simp only [Tree.size] at child
    omega
  | rotateLeft a b c x y frames =>
    have focus := plug_injective frames same
    have child := congrArg ChaCha.MTR.Tree.size (ChaCha.MTR.Tree.node.inj focus).1
    simp only [Tree.size] at child
    omega

end DynamicOptimality.MultiFinger
