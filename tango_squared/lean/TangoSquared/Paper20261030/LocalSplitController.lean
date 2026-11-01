import TangoSquared.Paper20261030.LocalSplitProgram

/-! Correctness and the telescoping logarithmic bound for the concrete
split controller. Its output is the existing `splitAt`: the requested
vertex is the root and both remaining sides are balanced. All control
decisions use records read by the program. -/

namespace TangoSquared.Paper20261030.Auxiliary.SplitController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open MTR DynamicOptimality DynamicOptimality.LocalProgram

variable {α ρ : Type*} [Ord α] [LawfulEqOrd α]

theorem split_prefix (request : α) (tree : Impl α (fun _ => ρ))
    (balanced : tree.Balanced) (found : searchResult request tree = true) (depth : Nat) (outside) :
    ∃ reads cost, Steps (program request) (.search depth) ⟨recordTree tree,outside⟩ (.returning depth)
      ⟨recordTree (splitAt request tree balanced found).impl,outside⟩ reads cost ∧
      cost ≤ 990*(Nat.clog 2 ((splitAt request tree balanced found).left.size+1)+
        Nat.clog 2 ((splitAt request tree balanced found).right.size+1))+1250*height tree := by
  induction tree generalizing depth outside with
  | leaf => simp [searchResult] at found
  | inner size key value left right ihl ihr =>
    have binEq : bin key value left right = .inner size key value left right := by
      have sizes := balanced.eq
      simp only [bin,sizes]
    have read := read_search request key depth size value left right outside
    cases comparison : compare request key with
    | eq =>
      have target : (splitAt request (.inner size key value left right) balanced found).impl =
          .inner size key value left right := by
        have equal := compare_eq_iff_eq.mp comparison
        subst request
        rw [splitAt]
        split <;> rename_i impossible <;> simp at impossible
        simpa only [SplitResult.impl,cast_eq] using binEq
      simp only [comparison] at read
      rw [target]
      exact ⟨_,1,read.prefix,by simp only [height]; omega⟩
    | lt =>
      have childFound : searchResult request left = true := by simpa [searchResult,comparison] using found
      let child := splitAt request left balanced.left childFound
      let joined := link key value child.right right child.right_balanced balanced.right
      have childSize : child.left.size+1+child.right.size = left.size := splitAt_size request left balanced.left childFound
      have order := split_join_order left.size right.size child.right.size balanced.at_root (by omega)
      have target : splitAt request (.inner size key value left right) balanced found =
          ⟨child.value,child.left,joined.impl,child.left_balanced,joined.balanced_impl⟩ := by
        rw [splitAt]
        split <;> rename_i branch <;> simp [comparison] at branch
        rfl
      have totalSize : size = child.left.size+1+joined.impl.size := by
        have joinedSize := joined.size_impl
        have oldSize := balanced.eq
        omega
      have treeEq : recordTree (.inner size request child.value child.left joined.impl) =
          recordTree (splitAt request (.inner size key value left right) balanced found).impl := by
        rw [target]
        change recordTree (.inner size request child.value child.left joined.impl) =
          recordTree (bin request child.value child.left joined.impl)
        simp only [bin,← totalSize]
      obtain ⟨childReads,childCost,childRun,childBound⟩ := ihl balanced.left childFound (depth+1)
        (.left (size,⟨key,value⟩) (recordTree right)::outside)
      have down : Step (program request) (.descend depth true) ⟨recordTree (.inner size key value left right),outside⟩
          (.search (depth+1)) ⟨recordTree left,.left (size,⟨key,value⟩) (recordTree right)::outside⟩ none := by
        cases left with
        | leaf => simp [searchResult] at childFound
        | inner => exact .nav rfl rfl
      have up : Step (program request) (.returning (depth+1))
          ⟨recordTree child.impl,.left (size,⟨key,value⟩) (recordTree right)::outside⟩
          (.parent depth) ⟨recordTree (.inner size key value child.impl right),outside⟩ none := .nav rfl rfl
      have parentRead := read_parent request key depth size value child.impl right outside
      simp only [comparison] at read parentRead
      let exposed : NodeRecord α (fun _ => ρ) := (child.left.size+1+child.right.size,⟨request,child.value⟩)
      have turned := turn_left request depth size (recordTree child.left) (recordTree child.right) (recordTree right)
        exposed (size,⟨key,value⟩) outside
      obtain ⟨joinReads,joinCost,joinRun,joinBound⟩ := JoinController.link_prefix_right_rank
        size key value child.right right child.right_balanced balanced.right order 0
        (.right (recordTree child.left) exposed::outside)
      have compiled := join_prefix request depth size joinRun
      have finished := finish_right request depth size exposed.1 request child.value
        (recordTree child.left) (recordTree joined.impl) outside
      change Steps (program request) _ _ _ ⟨recordTree (.inner size request child.value child.left joined.impl),outside⟩ _ _ at finished
      rw [treeEq] at finished
      have whole := ((((((read.prefix.append down.prefix).append childRun).append up.prefix).append parentRead.prefix).append turned).append compiled).append finished
      refine ⟨_,_,whole,?_⟩
      have joinBudget : joinCost ≤ 990*Nat.clog 2 (child.right.size+right.size+2)+76-990*Nat.log 2 (child.right.size+1) := by omega
      have telescope := Metadata.charged_rank_telescope (child.right.size+1) (child.right.size+right.size+2) (by omega)
      have joinedSize : joined.impl.size+1 = child.right.size+right.size+2 := by have := joined.size_impl; omega
      have heightBound := Nat.mul_le_mul_left 1250 (Nat.le_max_left (height left) (height right))
      rw [target]
      change _ ≤ 990*(Nat.clog 2 (child.left.size+1)+Nat.clog 2 (joined.impl.size+1))+1250*height (.inner size key value left right)
      simp only [joinedSize,height,Nat.mul_add,Nat.mul_one]
      change childCost ≤ 990*(Nat.clog 2 (child.left.size+1)+Nat.clog 2 (child.right.size+1))+1250*height left at childBound
      omega
    | gt =>
      have childFound : searchResult request right = true := by simpa [searchResult,comparison] using found
      let child := splitAt request right balanced.right childFound
      let joined := link key value left child.left balanced.left child.left_balanced
      have childSize : child.left.size+1+child.right.size = right.size := splitAt_size request right balanced.right childFound
      have order := split_join_order right.size left.size child.left.size balanced.at_root.symm (by omega)
      have target : splitAt request (.inner size key value left right) balanced found =
          ⟨child.value,joined.impl,child.right,joined.balanced_impl,child.right_balanced⟩ := by
        rw [splitAt]
        split <;> rename_i branch <;> simp [comparison] at branch
        rfl
      have totalSize : size = joined.impl.size+1+child.right.size := by
        have joinedSize := joined.size_impl
        have oldSize := balanced.eq
        omega
      have treeEq : recordTree (.inner size request child.value joined.impl child.right) =
          recordTree (splitAt request (.inner size key value left right) balanced found).impl := by
        rw [target]
        change recordTree (.inner size request child.value joined.impl child.right) =
          recordTree (bin request child.value joined.impl child.right)
        simp only [bin,← totalSize]
      obtain ⟨childReads,childCost,childRun,childBound⟩ := ihr balanced.right childFound (depth+1)
        (.right (recordTree left) (size,⟨key,value⟩)::outside)
      have down : Step (program request) (.descend depth false) ⟨recordTree (.inner size key value left right),outside⟩
          (.search (depth+1)) ⟨recordTree right,.right (recordTree left) (size,⟨key,value⟩)::outside⟩ none := by
        cases right with
        | leaf => simp [searchResult] at childFound
        | inner => exact .nav rfl rfl
      have up : Step (program request) (.returning (depth+1))
          ⟨recordTree child.impl,.right (recordTree left) (size,⟨key,value⟩)::outside⟩
          (.parent depth) ⟨recordTree (.inner size key value left child.impl),outside⟩ none := .nav rfl rfl
      have parentRead := read_parent request key depth size value left child.impl outside
      simp only [comparison] at read parentRead
      let exposed : NodeRecord α (fun _ => ρ) := (child.left.size+1+child.right.size,⟨request,child.value⟩)
      have turned := turn_right request depth size (recordTree left) (recordTree child.left) (recordTree child.right)
        (size,⟨key,value⟩) exposed outside
      obtain ⟨joinReads,joinCost,joinRun,joinBound⟩ := JoinController.link_prefix_left_rank
        size key value left child.left balanced.left child.left_balanced order 0
        (.left exposed (recordTree child.right)::outside)
      have compiled := join_prefix request depth size joinRun
      have finished := finish_left request depth size exposed.1 request child.value
        (recordTree joined.impl) (recordTree child.right) outside
      change Steps (program request) _ _ _ ⟨recordTree (.inner size request child.value joined.impl child.right),outside⟩ _ _ at finished
      rw [treeEq] at finished
      have whole := ((((((read.prefix.append down.prefix).append childRun).append up.prefix).append parentRead.prefix).append turned).append compiled).append finished
      refine ⟨_,_,whole,?_⟩
      have joinBudget : joinCost ≤ 990*Nat.clog 2 (left.size+child.left.size+2)+76-990*Nat.log 2 (child.left.size+1) := by omega
      have telescope := Metadata.charged_rank_telescope (child.left.size+1) (left.size+child.left.size+2) (by omega)
      have joinedSize : joined.impl.size+1 = left.size+child.left.size+2 := by have := joined.size_impl; omega
      have heightBound := Nat.mul_le_mul_left 1250 (Nat.le_max_right (height left) (height right))
      rw [target]
      change _ ≤ 990*(Nat.clog 2 (joined.impl.size+1)+Nat.clog 2 (child.right.size+1))+1250*height (.inner size key value left right)
      simp only [joinedSize,height,Nat.mul_add,Nat.mul_one]
      change childCost ≤ 990*(Nat.clog 2 (child.left.size+1)+Nat.clog 2 (child.right.size+1))+1250*height right at childBound
      omega

theorem split_run (request : α) (tree : Impl α (fun _ => ρ))
    (balanced : tree.Balanced) (found : searchResult request tree = true) (outside) :
    ∃ reads cost, Run (program request) (.search 0) ⟨recordTree tree,outside⟩ (.returning 0)
      ⟨recordTree (splitAt request tree balanced found).impl,outside⟩ reads cost ∧
      cost ≤ 5730*Nat.clog 2 (tree.size+1) := by
  obtain ⟨reads,cost,run,bound⟩ := split_prefix request tree balanced found 0 outside
  have size := splitAt_size request tree balanced found
  have treeHeight := balanced_height_log balanced
  have leftRank := Nat.clog_monotone 2
    (show (splitAt request tree balanced found).left.size+1 ≤ tree.size+1 by omega)
  have rightRank := Nat.clog_monotone 2
    (show (splitAt request tree balanced found).right.size+1 ≤ tree.size+1 by omega)
  exact ⟨reads,cost,run.run rfl,by omega⟩

end TangoSquared.Paper20261030.Auxiliary.SplitController
