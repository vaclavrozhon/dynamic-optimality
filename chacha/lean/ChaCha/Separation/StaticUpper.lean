import ChaCha.Separation.SparseKeys
import ChaCha.Paper20261030.GapBSTRepresentation
import ChaCha.Paper20261030.BSTRectangleBound
import ChaCha.Paper20261030.RobustBSTLowerBound

/-!
# Matching upper bound from a static balanced BST on the active ranks

Strictly increasing embeddings preserve the robust rectangle bound.
It therefore suffices to serve the dense rank word in a fixed perfect
reference's gap-key BST. The proof below constructs actual pointer traces;
no comparison algorithm or geometric completion is assumed.
-/

namespace ChaCha.Separation

open Paper20261030 Paper20261030.Rectangles Paper20261030.Dyadic
open ColoredStorage PreferredProjection MTR MTR.Tree MTR.Pointer

def rawHeight {α : Type*} : MTR.Tree α → Nat
  | .empty => 0
  | .node left _ right => max (rawHeight left) (rawHeight right)+1

theorem static_trace {α : Type*} (tree : MTR.Tree α) (key : α) (member : key ∈ tree.inorder)
    (outside : List (Frame α)) :
    ∃ cost final, Trace ⟨tree,outside⟩ [key] final cost ∧
      final.tree = plug tree outside ∧ cost ≤ rawHeight tree := by
  induction tree generalizing outside with
  | empty => simp [inorder] at member
  | node left root right ihl ihr =>
      simp only [inorder,List.mem_append,List.mem_singleton] at member
      rcases member with (leftMember | same) | rightMember
      · obtain ⟨cost,final,trace,sameTree,bound⟩ := ihl leftMember (.left root right::outside)
        cases left with
        | empty => simp [inorder] at leftMember
        | node a pivot b =>
            exact ⟨cost+1,final,.step (.left a b right pivot root outside) trace,
              sameTree,by simp only [rawHeight] at bound ⊢; omega⟩
      · subst key
        exact ⟨1,⟨.node left root right,outside⟩,.serve rfl (.nil _),rfl,
          by simp only [rawHeight]; omega⟩
      · obtain ⟨cost,final,trace,sameTree,bound⟩ := ihr rightMember (.right left root::outside)
        cases right with
        | empty => simp [inorder] at rightMember
        | node a pivot b =>
            exact ⟨cost+1,final,.step (.right left a b root pivot outside) trace,
              sameTree,by simp only [rawHeight] at bound ⊢; omega⟩

theorem static_execution {α : Type*} (tree : MTR.Tree α) (requests : List α)
    (members : ∀ key ∈ requests, key ∈ tree.inorder) :
    ∃ cost, MTR.Pointer.Execution tree requests tree cost ∧ cost ≤ rawHeight tree*requests.length := by
  induction requests with
  | nil => exact ⟨0,.nil _,by simp⟩
  | cons key requests ih =>
      obtain ⟨first,final,trace,same,bound⟩ := static_trace tree key (members key (by simp)) []
      obtain ⟨rest,execution,restBound⟩ := ih (fun key present => members key (by simp [present]))
      refine ⟨first+rest,.cons ⟨final,same,trace⟩ execution,?_⟩
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
      omega

def staticSource : Nat → Int → Source Int Unit
  | 0, owner => .leaf owner ()
  | height+1, owner => .fork () (staticSource height (2*owner)) (staticSource height (2*owner+1))

theorem staticSource_leaves (height : Nat) (owner : Int) :
    (staticSource height owner).shape.leaves = (canonical height owner).leaves := by
  induction height generalizing owner with
  | zero => rfl
  | succ height ih => simp only [staticSource,Source.shape,RouterProjection.Router.leaves,
      canonical,PrefRouter.leaves,ih]

theorem staticSource_height (height : Nat) (owner : Int) :
    rawHeight (GapBST.gaps (staticSource height owner)) = height := by
  induction height generalizing owner with
  | zero => rfl
  | succ height ih => simp only [staticSource,GapBST.gaps,rawHeight,ih,Nat.max_self]

theorem dense_robust_upper (height : Nat) (requests : List Int)
    (keys : ∀ key ∈ requests, ValidKey height key) :
    robustBound (accessPoints requests) ≤ 2*(height+1)*requests.length := by
  let tree := GapBST.encode (staticSource height 0)
  have word : tree.inorder = (canonical height 0).leaves :=
    (GapBST.encode_word _).trans (staticSource_leaves _ _)
  have ordered : tree.Ordered := by rw [Ordered,word]; exact canonical_ordered _ _
  have members : ∀ key ∈ requests, key ∈ tree.inorder := by
    intro key member
    rw [word]
    exact (canonical_zero_mem _ _).mpr (keys key member)
  obtain ⟨cost,execution,bound⟩ := static_execution tree requests members
  have heightEq : rawHeight tree = height+1 := by
    simp only [tree,GapBST.encode,rawHeight,staticSource_height,Nat.max_zero]
  have upper := robustBound_le_pointer_cost execution ordered
  rw [heightEq] at bound
  calc
    _ ≤ 2*cost := upper
    _ ≤ 2*((height+1)*requests.length) := Nat.mul_le_mul_left _ bound
    _ = _ := (Nat.mul_assoc _ _ _).symm

theorem sparseRequests_robust_upper (height copies : Nat) :
    robustBound (accessPoints (sparseRequests height copies)) ≤
      2*(height+1)*(copies*2^height) := by
  have same := robust_increasing_embedding_eq sparseKey sparseKey_increasing (2^height)
    (rankRequests height copies) (rankRequests_valid height copies)
  rw [rankRequests_cast] at same
  change robustBound (accessPoints (sparseRequests height copies)) = _ at same
  rw [same]
  have bound := dense_robust_upper height (numericRepeatedWord height copies)
    (numericRepeatedWord_valid height copies)
  simpa only [numericRepeatedWord_length] using bound

end ChaCha.Separation
