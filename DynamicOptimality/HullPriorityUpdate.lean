import DynamicOptimality.Basic
import ChaCha.PriorityHull

/-! Raising the last-touch times of a rooted hull preserves the existing
max-heap invariant. The gaps are actual untouched BST subtrees; their
disjointness from the touched keys follows from BST ordering. -/

namespace DynamicOptimality

open ChaCha ChaCha.MTR.Tree ChaCha.MTR.Tree.PriorityHull

variable {α : Type*} [LinearOrder α]

theorem ordered_node_parts {left right : RawTree α} {key : α}
    (ordered : Ordered (.node left key right)) :
    Ordered left ∧ Ordered right ∧ (∀ x ∈ left.inorder, x < key) ∧ (∀ x ∈ right.inorder, key < x) := by
  have outer := List.pairwise_append.mp ordered
  have inner := List.pairwise_append.mp outer.1
  refine ⟨inner.1,outer.2.1,?_,?_⟩
  · intro x member
    exact inner.2.2 x member key (by simp)
  · intro x member
    exact outer.2.2 key (by simp) x member

theorem gap_keys_subset (source : RawTree α) (gaps : Nat → RawTree α) (start index : Nat)
    (valid : index ≤ source.size) :
    ∀ key ∈ (gaps (start+index)).inorder, key ∈ (graft source gaps start).inorder := by
  induction source generalizing start index with
  | empty =>
    have zero : index = 0 := by simpa [size] using valid
    subst index
    simpa [graft]
  | node left key right ihl ihr =>
    intro x member
    by_cases inLeft : index ≤ left.size
    · have inTree := ihl start index inLeft x member
      simp only [graft,inorder,List.mem_append,List.mem_singleton]
      exact .inl (.inl inTree)
    · have inRight : index-left.size-1 ≤ right.size := by simp only [size] at valid; omega
      have offset : start+left.size+1+(index-left.size-1) = start+index := by omega
      have inTree := ihr (start+left.size+1) (index-left.size-1) inRight x (by simpa only [offset] using member)
      simp only [graft,inorder,List.mem_append,List.mem_singleton]
      exact .inr inTree

theorem gap_avoids_skeleton (source : RawTree α) (gaps : Nat → RawTree α) (start index : Nat)
    (valid : index ≤ source.size) (ordered : Ordered (graft source gaps start)) :
    ∀ key ∈ (gaps (start+index)).inorder, key ∉ source.inorder := by
  induction source generalizing start index with
  | empty => simp [inorder]
  | node left key right ihl ihr =>
    obtain ⟨orderedLeft,orderedRight,leftLt,rightLt⟩ := ordered_node_parts ordered
    intro x member selected
    simp only [inorder,List.mem_append,List.mem_singleton] at selected
    by_cases inLeft : index ≤ left.size
    · have inTree := gap_keys_subset left gaps start index inLeft x member
      have less := leftLt x inTree
      obtain (inSkeleton | equal) | inSkeleton := selected
      · exact ihl start index inLeft orderedLeft x member inSkeleton
      · subst x; exact lt_irrefl _ less
      · exact lt_asymm less (rightLt x ((inorder_sublist_graft right gaps _).subset inSkeleton))
    · have inRight : index-left.size-1 ≤ right.size := by simp only [size] at valid; omega
      have offset : start+left.size+1+(index-left.size-1) = start+index := by omega
      have memberRight : x ∈ (gaps (start+left.size+1+(index-left.size-1))).inorder := by
        simpa only [offset] using member
      have inTree := gap_keys_subset right gaps (start+left.size+1) (index-left.size-1) inRight x memberRight
      have greater := rightLt x inTree
      obtain (inSkeleton | equal) | inSkeleton := selected
      · exact lt_asymm greater (leftLt x ((inorder_sublist_graft left gaps _).subset inSkeleton))
      · subst x; exact lt_irrefl _ greater
      · exact ihr (start+left.size+1) (index-left.size-1) inRight orderedRight x memberRight inSkeleton

theorem heap_congr {old fresh : α → Int} (tree : RawTree α)
    (agree : ∀ key ∈ tree.inorder, old key = fresh key) (heap : Heap old tree) : Heap fresh tree := by
  induction tree with
  | empty => trivial
  | node left key right ihl ihr =>
    have rootEq := agree key (by simp [inorder])
    have leftEq : ∀ x ∈ left.inorder, old x = fresh x := fun x member => agree x (by simp [inorder,member])
    have rightEq : ∀ x ∈ right.inorder, old x = fresh x := fun x member => agree x (by simp [inorder,member])
    refine ⟨ihl leftEq heap.1,ihr rightEq heap.2.1,?_,?_⟩
    · intro x member
      rw [← leftEq x member,← rootEq]
      exact heap.2.2.1 x member
    · intro x member
      rw [← rightEq x member,← rootEq]
      exact heap.2.2.2 x member

theorem heap_uniform (tree : RawTree α) (priority : α → Int) (time : Int)
    (uniform : ∀ key ∈ tree.inorder, priority key = time) : Heap priority tree := by
  induction tree with
  | empty => trivial
  | node left key right ihl ihr =>
    have rootTime := uniform key (by simp [inorder])
    have leftTime : ∀ x ∈ left.inorder, priority x = time := fun x member => uniform x (by simp [inorder,member])
    have rightTime : ∀ x ∈ right.inorder, priority x = time := fun x member => uniform x (by simp [inorder,member])
    exact ⟨ihl leftTime,ihr rightTime,
      fun x member => by rw [leftTime x member,rootTime],
      fun x member => by rw [rightTime x member,rootTime]⟩

theorem gapCondition_reweight (old fresh : α → Int) (gaps : Nat → RawTree α)
    (selected : List α) (start : Nat) (condition : GapCondition old gaps selected start)
    (raised : ∀ key ∈ selected, old key ≤ fresh key)
    (unchanged : ∀ index ≤ selected.length, ∀ key ∈ (gaps (start+index)).inorder, fresh key = old key) :
    GapCondition fresh gaps selected start := by
  induction selected generalizing start with
  | nil =>
    exact heap_congr _ (fun key member => (unchanged 0 le_rfl key (by simpa using member)).symm) condition
  | cons key rest ih =>
    have agreeFirst : ∀ x ∈ (gaps start).inorder, old x = fresh x :=
      fun x member => (unchanged 0 (by simp) x (by simpa using member)).symm
    have agreeNext : ∀ x ∈ (gaps (start+1)).inorder, old x = fresh x :=
      fun x member => (unchanged 1 (by simp) x member).symm
    have increase := raised key (by simp)
    refine ⟨heap_congr _ agreeFirst condition.1,?_,?_,?_⟩
    · intro x member
      rw [← agreeFirst x member]
      exact (condition.2.1 x member).trans increase
    · intro x member
      rw [← agreeNext x member]
      exact (condition.2.2.1 x member).trans increase
    · apply ih (start+1) condition.2.2.2 (fun x member => raised x (by simp [member]))
      intro index bound x member
      have shifted := unchanged (index+1) (by simp only [List.length_cons]; omega) x
      exact shifted (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using member)

def touchTime (selected : List α) (time : Int) (old : α → Int) (key : α) : Int :=
  if key ∈ selected then time else old key

theorem hull_touch_heap {before after : RawTree α} {request : α}
    (access : MTR.HullAccess request before after) (ordered : Ordered before)
    (old : α → Int) (time : Int) (heap : Heap old before)
    (past : ∀ key ∈ before.inorder, old key ≤ time) :
    Heap (touchTime access.source.inorder time old) after := by
  let fresh := touchTime access.source.inorder time old
  have sourceHeap : Heap old (graft access.source access.gaps 0) := by rw [access.source_tree]; exact heap
  have sourceOrdered : Ordered (graft access.source access.gaps 0) := by rw [access.source_tree]; exact ordered
  have raised : ∀ key ∈ access.source.inorder, old key ≤ fresh key := by
    intro key member
    have inTree := (inorder_sublist_graft access.source access.gaps 0).subset member
    rw [access.source_tree] at inTree
    simpa only [fresh,touchTime,if_pos member] using past key inTree
  have unchanged : ∀ index ≤ access.source.inorder.length,
      ∀ key ∈ (access.gaps (0+index)).inorder, fresh key = old key := by
    intro index bound key member
    rw [length_inorder] at bound
    have absent := gap_avoids_skeleton access.source access.gaps 0 index bound sourceOrdered key member
    exact if_neg absent
  have condition := gapCondition_reweight old fresh access.gaps access.source.inorder 0
    (gapCondition_of_heap_graft old access.source access.gaps 0 sourceHeap) raised unchanged
  rw [access.same_keys] at condition
  have targetHeap : Heap fresh access.target := by
    apply heap_uniform _ _ time
    intro key member
    rw [← access.same_keys] at member
    exact if_pos member
  have result := heap_graft_of_gapCondition access.target access.gaps 0 targetHeap condition
  simpa only [access.target_tree] using result

end DynamicOptimality
