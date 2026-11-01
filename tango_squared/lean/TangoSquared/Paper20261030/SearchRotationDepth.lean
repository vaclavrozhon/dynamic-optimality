import DynamicOptimality.MetadataExecution

set_option autoImplicit false

/-! A root-starting adjacent-pointer access already pays the initial
search path. The existing tracked execution constructs an actual connected
prefix containing the requested key, with at most one prefix vertex per
charged pointer operation. Filling its untouched gaps does not change the
successful search depth of any key in the prefix.
-/

namespace TangoSquared.Paper20261030.SearchRotationBridge

open MTR MTR.Tree

variable {α : Type*} [LinearOrder α]

theorem searchDepth_lt_size {tree : MTR.Tree α} {key : α} {depth : Nat}
    (found : searchDepth key tree = some depth) : depth + 1 ≤ tree.size := by
  induction tree generalizing depth with
  | empty => simp only [searchDepth,reduceCtorEq] at found
  | node left root right ihl ihr =>
    by_cases onLeft : key < root
    · simp only [searchDepth,onLeft,if_true] at found
      cases searched : searchDepth key left with
      | none => simp only [searched,Option.map_none,reduceCtorEq] at found
      | some childDepth =>
        have equal : childDepth + 1 = depth := by simpa only [searched,Option.map_some,Option.some.injEq] using found
        have bound := ihl searched
        simp only [size]
        omega
    · by_cases onRight : root < key
      · simp only [searchDepth,onLeft,if_false,onRight,if_true] at found
        cases searched : searchDepth key right with
        | none => simp only [searched,Option.map_none,reduceCtorEq] at found
        | some childDepth =>
          have equal : childDepth + 1 = depth := by simpa only [searched,Option.map_some,Option.some.injEq] using found
          have bound := ihr searched
          simp only [size]
          omega
      · have equal : 0 = depth := by simpa only [searchDepth,onLeft,if_false,onRight,Option.some.injEq] using found
        simp only [size]
        omega

/-- A successful search never enters one of the skeleton's empty gaps. -/
theorem searchDepth_graft {tree : MTR.Tree α} {key : α} {depth : Nat}
    (found : searchDepth key tree = some depth) (gaps : Nat → MTR.Tree α) (start : Nat) :
    searchDepth key (graft tree gaps start) = some depth := by
  induction tree generalizing depth start with
  | empty => simp only [searchDepth,reduceCtorEq] at found
  | node left root right ihl ihr =>
    by_cases onLeft : key < root
    · simp only [searchDepth,onLeft,if_true] at found
      cases searched : searchDepth key left with
      | none => simp only [searched,Option.map_none,reduceCtorEq] at found
      | some childDepth =>
        have equal : childDepth + 1 = depth := by simpa only [searched,Option.map_some,Option.some.injEq] using found
        simp only [graft,searchDepth,onLeft,if_true,ihl searched start,Option.map_some,Nat.succ_eq_add_one,equal]
    · by_cases onRight : root < key
      · simp only [searchDepth,onLeft,if_false,onRight,if_true] at found
        cases searched : searchDepth key right with
        | none => simp only [searched,Option.map_none,reduceCtorEq] at found
        | some childDepth =>
          have equal : childDepth + 1 = depth := by simpa only [searched,Option.map_some,Option.some.injEq] using found
          simp only [graft,searchDepth,onLeft,if_false,onRight,if_true,ihr searched _,Option.map_some,Nat.succ_eq_add_one,equal]
      · simpa only [graft,searchDepth,onLeft,if_false,onRight] using found

/-- The initial search cost is bounded by the original pointer trace cost,
including when rotations precede the instruction serving the request. -/
theorem pointer_access_initial_depth {before after : MTR.Tree α} {key : α} {cost : Nat}
    (ordered : Ordered before) (access : Pointer.Access key before after cost) :
    ∃ depth, searchDepth key before = some depth ∧ depth + 1 ≤ cost := by
  obtain ⟨hull,bound⟩ := access.toHullAccess
  have sourceOrdered : Ordered hull.source := ordered_of_graft (hull.source_tree.symm ▸ ordered)
  obtain ⟨depth,found⟩ := searchDepth_exists_of_mem sourceOrdered hull.requested
  refine ⟨depth,?_,(searchDepth_lt_size found).trans bound⟩
  rw [← hull.source_tree]
  exact searchDepth_graft found hull.gaps 0

/-- Erasing the existing decorated access preserves the real key set and
provides the same initial search-depth bound. -/
theorem metadata_access_initial_depth {β : α → Type*}
    {before after : MTR.Tree (Auxiliary.NodeRecord α β)} {key : α} {cost : Nat}
    (ordered : Ordered (Auxiliary.Metadata.forgetTree before))
    (access : Auxiliary.Metadata.Access key before after cost) :
    ∃ depth, searchDepth key (Auxiliary.Metadata.forgetTree before) = some depth ∧ depth + 1 ≤ cost := by
  obtain ⟨pointerCost,bound,pointer⟩ := access.pointer
  obtain ⟨depth,found,depthBound⟩ := pointer_access_initial_depth ordered pointer
  exact ⟨depth,found,depthBound.trans bound⟩

end TangoSquared.Paper20261030.SearchRotationBridge
