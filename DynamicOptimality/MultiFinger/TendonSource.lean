import DynamicOptimality.MultiFinger.Hand
import DynamicOptimality.ModelOnline

/-! The two ordered sides of an exact source tendon.
A tendon is the original zipper path between two retained hand vertices.
Right turns contribute the keys below the inner vertex; left turns
contribute the keys above it. The order of the original turns is retained
as ghost state even when the physical BST groups these two sides. -/

namespace DynamicOptimality.MultiFinger.TendonSource

open ChaCha.MTR SearchRotation

variable {α : Type*}

abbrev LowCell (α : Type*) := RawTree α × α
abbrev HighCell (α : Type*) := α × RawTree α

def low : List (Pointer.Frame α) → List (LowCell α)
  | [] => []
  | .left _ _::frames => low frames
  | .right left key::frames => low frames++[(left,key)]

def high : List (Pointer.Frame α) → List (HighCell α)
  | [] => []
  | .left key right::frames => (key,right)::high frames
  | .right _ _::frames => high frames

def lowWord : List (LowCell α) → List α
  | [] => []
  | (left,key)::cells => left.inorder++[key]++lowWord cells

def highWord : List (HighCell α) → List α
  | [] => []
  | (key,right)::cells => [key]++right.inorder++highWord cells

theorem lowWord_append (first last : List (LowCell α)) :
    lowWord (first++last) = lowWord first++lowWord last := by
  induction first with
  | nil => rfl
  | cons cell cells ih => cases cell; simp only [List.cons_append,lowWord,ih,List.append_assoc]

theorem split_word (frames : List (Pointer.Frame α)) (inside : RawTree α) :
    (Pointer.plug inside frames).inorder = lowWord (low frames)++inside.inorder++highWord (high frames) := by
  induction frames generalizing inside with
  | nil => simp [Pointer.plug,low,high,lowWord,highWord]
  | cons frame frames ih =>
    cases frame with
    | left key right =>
      simpa only [Pointer.plug,low,high,highWord,Tree.inorder,List.append_assoc] using
        ih (ChaCha.MTR.Tree.node inside key right)
    | right left key =>
      simpa only [Pointer.plug,low,high,lowWord_append,lowWord,List.append_nil,
        Tree.inorder,List.append_assoc] using ih (ChaCha.MTR.Tree.node left key inside)

def lowTree : List (LowCell α) → RawTree α → RawTree α
  | [], inside => inside
  | (left,key)::cells, inside => .node left key (lowTree cells inside)

def highTree : List (HighCell α) → RawTree α → RawTree α
  | [], inside => inside
  | (key,right)::cells, inside => highTree cells (.node inside key right)

theorem lowTree_word (cells : List (LowCell α)) (inside : RawTree α) :
    (lowTree cells inside).inorder = lowWord cells++inside.inorder := by
  induction cells with
  | nil => rfl
  | cons cell cells ih => cases cell; simp only [lowTree,Tree.inorder,ih,lowWord,List.append_assoc]

theorem highTree_word (cells : List (HighCell α)) (inside : RawTree α) :
    (highTree cells inside).inorder = inside.inorder++highWord cells := by
  induction cells generalizing inside with
  | nil => simp [highTree,highWord]
  | cons cell cells ih => cases cell; simp only [highTree,ih,Tree.inorder,highWord,List.append_assoc]

def canonical (frames : List (Pointer.Frame α)) (inside : RawTree α) : RawTree α :=
  lowTree (low frames) (highTree (high frames) inside)

theorem canonical_word (frames : List (Pointer.Frame α)) (inside : RawTree α) :
    (canonical frames inside).inorder = (Pointer.plug inside frames).inorder := by
  simp only [canonical,lowTree_word,highTree_word,split_word,List.append_assoc]

theorem side_count (frames : List (Pointer.Frame α)) :
    (low frames).length+(high frames).length = frames.length := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
    cases frame <;> simp only [low,high,List.length_append,List.length_cons,List.length_nil] <;> omega

private theorem restricted_to_rotations {before after : RawTree α} {count : Nat}
    (steps : Tree.RestrictedSteps count before after) : Rotations before after count := by
  induction steps with
  | refl => exact .refl _
  | @cons before middle after count head _ ih =>
    have step : Rotation before middle := by
      cases head with
      | rootRight a b c x y => exact .rootRight a b c x y
      | rootLeft a b c x y => exact .rootLeft a b c x y
      | rightRight a b c d x y z => exact .rightContext a x (.rootRight b c d y z)
      | rightLeft a b c d x y z => exact .rightContext a x (.rootLeft b c d y z)
      | leftRight a b c d x y z => exact .leftContext (.rootRight a b c x y) z d
      | leftLeft a b c d x y z => exact .leftContext (.rootLeft a b c x y) z d
    exact .step step ih

/-- This is an initialization fact only. Later endpoint operations must
use the deque potential; a fresh linear reshaping at every move would not
prove the logarithmic multifinger simulation. -/
theorem canonical_initialization (frames : List (Pointer.Frame α)) (inside : RawTree α) :
    ∃ count, count ≤ 6*(Pointer.plug inside frames).size ∧
      Rotations (Pointer.plug inside frames) (canonical frames inside) count := by
  obtain ⟨count,paid,steps⟩ := ChaCha.MTR.Tree.restricted_rotation_linear
    (Pointer.plug inside frames) (canonical frames inside) (canonical_word frames inside).symm
  have sameSize : (canonical frames inside).size = (Pointer.plug inside frames).size := by
    rw [← Tree.length_inorder,← Tree.length_inorder,canonical_word]
  exact ⟨count,by rw [sameSize] at paid; omega,restricted_to_rotations steps⟩

end DynamicOptimality.MultiFinger.TendonSource
