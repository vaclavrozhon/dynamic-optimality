import DynamicOptimality.GeometricOnlineSimulation.ClassTree
import ChaCha.Paper20261030.SearchRotationDepth

/-! # Searching a class skeleton inside its physical tree -/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR

/-- A search ending at a skeleton key never enters a literal hole. -/
theorem ClassFrame.searchDepth {system : SplitTreeSystem} {skeleton : RawTree Nat}
    (frame : ClassFrame system skeleton) {key depth : Nat}
    (found : Tree.searchDepth key skeleton = some depth) :
    Tree.searchDepth key frame.tree = some depth := by
  induction skeleton generalizing depth with
  | empty => simp only [Tree.searchDepth, reduceCtorEq] at found
  | node left root right ihl ihr =>
      cases frame with
      | node front _ back =>
          by_cases before : key < root
          · simp only [Tree.searchDepth, if_pos before] at found
            cases searched : Tree.searchDepth key left with
            | none => simp only [searched, Option.map_none, reduceCtorEq] at found
            | some childDepth =>
                have equal : childDepth+1 = depth := by simpa only
                  [searched, Option.map_some, Option.some.injEq] using found
                simp only [ClassFrame.tree, Tree.searchDepth, if_pos before,
                  ihl front searched, Option.map_some, Nat.succ_eq_add_one, equal]
          · by_cases after : root < key
            · simp only [Tree.searchDepth, if_neg before, if_pos after] at found
              cases searched : Tree.searchDepth key right with
              | none => simp only [searched, Option.map_none, reduceCtorEq] at found
              | some childDepth =>
                  have equal : childDepth+1 = depth := by simpa only
                    [searched, Option.map_some, Option.some.injEq] using found
                  simp only [ClassFrame.tree, Tree.searchDepth, if_neg before, if_pos after,
                    ihr back searched, Option.map_some, Nat.succ_eq_add_one, equal]
            · simpa only [ClassFrame.tree, Tree.searchDepth, if_neg before, if_neg after] using found

end DynamicOptimality.GeometricOnlineSimulation
