import DynamicOptimality.SearchRotationModel

set_option autoImplicit false

/-! Restriction of an ordinary BST to an initial interval of keys.
The restriction contracts every discarded search vertex. Each original
rotation becomes either one ordinary rotation or no change, so both the
successful initial search depth and the number of rotations can only
decrease. The endpoint is the restriction of the actual output tree. -/

namespace DynamicOptimality.SearchRotation.Prefix

open TangoSquared.MTR

def prune (n : Nat) : RawTree Nat → RawTree Nat
  | .empty => .empty
  | .node left key right =>
      if key < n then .node (prune n left) key (prune n right) else prune n left

private theorem node_parts {left right : RawTree Nat} {key : Nat}
    (ordered : Tree.Ordered (.node left key right)) :
    Tree.Ordered left ∧ Tree.Ordered right ∧
      (∀ x ∈ left.inorder, x < key) ∧ (∀ x ∈ right.inorder, key < x) := by
  have outer := List.pairwise_append.mp ordered
  have inner := List.pairwise_append.mp outer.1
  refine ⟨inner.1,outer.2.1,?_,?_⟩
  · intro x member
    exact inner.2.2 x member key (by simp)
  · intro x member
    exact outer.2.2 key (by simp) x member

theorem inorder (n : Nat) {tree : RawTree Nat} (ordered : Tree.Ordered tree) :
    (prune n tree).inorder = tree.inorder.filter (fun key => decide (key < n)) := by
  induction tree with
  | empty => rfl
  | node left key right ihl ihr =>
    obtain ⟨leftOrdered,rightOrdered,_,rightKeys⟩ := node_parts ordered
    by_cases kept : key < n
    · simp only [prune,if_pos kept,Tree.inorder,ihl leftOrdered,ihr rightOrdered,List.filter_append,
        List.filter_cons,decide_eq_true kept,if_true,List.filter_nil]
    · have rightEmpty : right.inorder.filter (fun value => decide (value < n)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro value member
        have larger := rightKeys value member
        have outside : ¬ value < n := by omega
        simp [outside]
      simp only [prune,if_neg kept,Tree.inorder,ihl leftOrdered,List.filter_append,
        List.filter_cons,decide_eq_false kept,Bool.false_eq_true,if_false,List.filter_nil,rightEmpty,List.append_nil]

theorem ordered (n : Nat) {tree : RawTree Nat} (sourceOrdered : Tree.Ordered tree) :
    Tree.Ordered (prune n tree) := by
  unfold Tree.Ordered
  rw [inorder n sourceOrdered]
  exact sourceOrdered.filter _

theorem prune_eq_self (n : Nat) {tree : RawTree Nat}
    (keys : ∀ key ∈ tree.inorder, key < n) : prune n tree = tree := by
  induction tree with
  | empty => rfl
  | node left key right ihl ihr =>
    have kept : key < n := keys key (by simp [Tree.inorder])
    have leftKeys : ∀ value ∈ left.inorder, value < n := by
      intro value member
      exact keys value (by simp [Tree.inorder,member])
    have rightKeys : ∀ value ∈ right.inorder, value < n := by
      intro value member
      exact keys value (by simp [Tree.inorder,member])
    simp only [prune,if_pos kept,ihl leftKeys,ihr rightKeys]

theorem rotation_inorder {before after : RawTree Nat} (move : Rotation before after) :
    after.inorder = before.inorder := by
  induction move with
  | rootRight | rootLeft => simp only [Tree.inorder,List.append_assoc]
  | leftContext move key right ih => simp only [Tree.inorder,ih]
  | rightContext left key move ih => simp only [Tree.inorder,ih]

theorem rotation_ordered {before after : RawTree Nat} (sourceOrdered : Tree.Ordered before)
    (move : Rotation before after) : Tree.Ordered after := by
  unfold Tree.Ordered
  rw [rotation_inorder move]
  exact sourceOrdered

/-- One rotation restricts to at most one rotation, with exact endpoints. -/
theorem rotation (n : Nat) {before after : RawTree Nat} (sourceOrdered : Tree.Ordered before)
    (move : Rotation before after) :
    ∃ count, Rotations (prune n before) (prune n after) count ∧ count ≤ 1 := by
  induction move with
  | rootRight a b c x y =>
    have smaller : x < y := (node_parts sourceOrdered).2.2.1 x (by simp [Tree.inorder])
    by_cases keepY : y < n
    · have keepX : x < n := by omega
      refine ⟨1,?_,le_rfl⟩
      simpa only [prune,if_pos keepY,if_pos keepX] using
        Rotations.singleton (Rotation.rootRight (prune n a) (prune n b) (prune n c) x y)
    · by_cases keepX : x < n
      · refine ⟨0,?_,by decide⟩
        simp only [prune,if_neg keepY,if_pos keepX]
        exact .refl _
      · refine ⟨0,?_,by decide⟩
        simp only [prune,if_neg keepY,if_neg keepX]
        exact .refl _
  | rootLeft a b c x y =>
    have smaller : x < y := (node_parts sourceOrdered).2.2.2 y (by simp [Tree.inorder])
    by_cases keepY : y < n
    · have keepX : x < n := by omega
      refine ⟨1,?_,le_rfl⟩
      simpa only [prune,if_pos keepY,if_pos keepX] using
        Rotations.singleton (Rotation.rootLeft (prune n a) (prune n b) (prune n c) x y)
    · by_cases keepX : x < n
      · refine ⟨0,?_,by decide⟩
        simp only [prune,if_neg keepY,if_pos keepX]
        exact .refl _
      · refine ⟨0,?_,by decide⟩
        simp only [prune,if_neg keepY,if_neg keepX]
        exact .refl _
  | leftContext move key right ih =>
    obtain ⟨count,trace,bound⟩ := ih (node_parts sourceOrdered).1
    refine ⟨count,?_,bound⟩
    by_cases kept : key < n
    · simpa only [prune,if_pos kept,Pointer.plug] using
        trace.plug [Pointer.Frame.left key (prune n right)]
    · simpa only [prune,if_neg kept] using trace
  | rightContext left key move ih =>
    by_cases kept : key < n
    · obtain ⟨count,trace,bound⟩ := ih (node_parts sourceOrdered).2.1
      refine ⟨count,?_,bound⟩
      simpa only [prune,if_pos kept,Pointer.plug] using
        trace.plug [Pointer.Frame.right (prune n left) key]
    · refine ⟨0,?_,by decide⟩
      simp only [prune,if_neg kept]
      exact .refl _

theorem rotations (n : Nat) {before after : RawTree Nat} {count : Nat}
    (sourceOrdered : Tree.Ordered before) (trace : Rotations before after count) :
    ∃ actualCount, Rotations (prune n before) (prune n after) actualCount ∧ actualCount ≤ count := by
  induction trace with
  | refl tree => exact ⟨0,.refl _,le_rfl⟩
  | step first rest ih =>
    obtain ⟨front,frontTrace,frontBound⟩ := rotation n sourceOrdered first
    obtain ⟨back,backTrace,backBound⟩ := ih (rotation_ordered sourceOrdered first)
    exact ⟨front+back,frontTrace.append backTrace,by omega⟩

/-- Pruning contracts vertices on the successful initial search path.
This depth comparison itself does not require source-tree ordering. -/
theorem search_depth (n : Nat) {tree : RawTree Nat} {key depth : Nat}
    (kept : key < n) (found : Tree.searchDepth key tree = some depth) :
    ∃ actualDepth, Tree.searchDepth key (prune n tree) = some actualDepth ∧ actualDepth ≤ depth := by
  induction tree generalizing depth with
  | empty => simp only [Tree.searchDepth,reduceCtorEq] at found
  | node left root right ihl ihr =>
    by_cases rootKept : root < n
    · by_cases onLeft : key < root
      · simp only [Tree.searchDepth,onLeft,if_true] at found
        cases searched : Tree.searchDepth key left with
        | none => simp only [searched,Option.map_none,reduceCtorEq] at found
        | some childDepth =>
          have equal : childDepth+1 = depth := by
            simpa only [searched,Option.map_some,Option.some.injEq] using found
          obtain ⟨actualDepth,actual,bound⟩ := ihl searched
          refine ⟨actualDepth+1,?_,by omega⟩
          simp only [prune,if_pos rootKept,Tree.searchDepth,if_pos onLeft,actual,Option.map_some]
      · by_cases onRight : root < key
        · simp only [Tree.searchDepth,onLeft,if_false,onRight,if_true] at found
          cases searched : Tree.searchDepth key right with
          | none => simp only [searched,Option.map_none,reduceCtorEq] at found
          | some childDepth =>
            have equal : childDepth+1 = depth := by
              simpa only [searched,Option.map_some,Option.some.injEq] using found
            obtain ⟨actualDepth,actual,bound⟩ := ihr searched
            refine ⟨actualDepth+1,?_,by omega⟩
            simp only [prune,if_pos rootKept,Tree.searchDepth,if_neg onLeft,if_pos onRight,actual,Option.map_some]
        · refine ⟨0,?_,Nat.zero_le _⟩
          simp only [prune,if_pos rootKept,Tree.searchDepth,if_neg onLeft,if_neg onRight]
    · have onLeft : key < root := by omega
      simp only [Tree.searchDepth,onLeft,if_true] at found
      cases searched : Tree.searchDepth key left with
      | none => simp only [searched,Option.map_none,reduceCtorEq] at found
      | some childDepth =>
        have equal : childDepth+1 = depth := by
          simpa only [searched,Option.map_some,Option.some.injEq] using found
        obtain ⟨actualDepth,actual,bound⟩ := ihl searched
        refine ⟨actualDepth,?_,by omega⟩
        simpa only [prune,if_neg rootKept] using actual

/-- Exact restricted endpoints, with no increase in the paid initial
search path or the actual number of ordinary rotations. -/
theorem access (n : Nat) {before after : RawTree Nat} {key cost : Nat}
    (sourceOrdered : Tree.Ordered before) (kept : key < n)
    (sourceAccess : Access key before after cost) :
    ∃ actualCost, Access key (prune n before) (prune n after) actualCost ∧ actualCost ≤ cost := by
  obtain ⟨depth,count,found,trace,costEq⟩ := sourceAccess
  obtain ⟨actualDepth,actualFound,depthBound⟩ := search_depth n kept found
  obtain ⟨actualCount,actualTrace,countBound⟩ := rotations n sourceOrdered trace
  exact ⟨actualDepth+1+actualCount,⟨actualDepth,actualCount,actualFound,actualTrace,rfl⟩,by omega⟩

end DynamicOptimality.SearchRotation.Prefix
