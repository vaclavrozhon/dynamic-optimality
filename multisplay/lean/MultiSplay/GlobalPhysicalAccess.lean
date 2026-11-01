import MultiSplay.GlobalSplay
import DynamicOptimality.SearchRotationIndexed

/-!
# Paying the initial global search by rotations to the requested root

One ordinary rotation reduces a key's depth by at most one. Consequently,
when the final classical switch puts the requested key at the global root,
the preceding exact physical rotation sequence already pays its initial
search depth. This avoids charging any free navigation or bookkeeping.
Root-component membership is a separate structural invariant; it is not
silently assumed to follow from a list of forest component domains.
-/

namespace MultiSplay.Global

open DynamicOptimality DynamicOptimality.SearchRotation
open TangoSquared.MTR

theorem indexed_hasRoot {lower upper key : Nat} (tree : BST lower upper)
    (root : tree.toRaw.rootKey = some key) : tree.HasRoot key := by
  cases tree with
  | empty => contradiction
  | node left right =>
    have same := Option.some.inj root
    subst key
    exact ⟨left, right, rfl⟩

/-- The actual initial key depth is bounded by the number of rotations
of any trace that ends at that key's root. -/
theorem initial_depth_le_rotations {n count : Nat} (before : BST 0 n) (key : Fin n)
    {after : RawTree Nat} (rotations : Rotations before.toRaw after count)
    (root : after.rootKey = some key.val) : before.depth key.val ≤ count := by
  obtain ⟨last, lifted, same⟩ := rotations_lift rotations before rfl
  have lastRoot := indexed_hasRoot last (same.symm ▸ root)
  have lastDepth := Splay.Tree.BST.depth_eq_zero_of_hasRoot lastRoot
  have bound := rotations_depth_le lifted key.val
  omega

/-- This constructs the exact search-and-rotation access, retaining the
supplied initial tree, actual final tree, and full rotation transcript. -/
theorem rooted_access {n count : Nat} (before : BST 0 n) (key : Fin n)
    {after : RawTree Nat} (rotations : Rotations before.toRaw after count)
    (root : after.rootKey = some key.val) :
    Access key.val before.toRaw after (before.depth key.val + 1 + count) ∧
      before.depth key.val + 1 + count ≤ 2 * count + 1 := by
  refine ⟨⟨before.depth key.val, count, toRaw_searchDepth before (Nat.zero_le _) key.isLt,
    rotations, rfl⟩, ?_⟩
  have bound := initial_depth_le_rotations before key rotations root
  omega

/-- Once the ancestor switches place the query in the root auxiliary,
its mandatory final splay certifies the global root without an additional
root-service hypothesis. The prefix contains the exact earlier rotations. -/
theorem final_splay_access {n prefixCount finalCount : Nat}
    (before : BST 0 n) (key : Fin n) {source target : RawTree Nat}
    (gaps : Nat → RawTree Nat) (start : Nat)
    (earlier : Rotations before.toRaw (Tree.graft source gaps start) prefixCount)
    (finalSplay : Auxiliary.Splay key.val source target finalCount) :
    Access key.val before.toRaw (Tree.graft target gaps start)
      (before.depth key.val + 1 + (prefixCount + finalCount)) ∧
      before.depth key.val + 1 + (prefixCount + finalCount) ≤
        2 * (prefixCount + finalCount) + 1 := by
  exact rooted_access before key
    (earlier.append (rotations_graft (splay_rotations finalSplay) gaps start))
    (Tree.graft_rootKey target gaps start finalSplay.root_after)

end MultiSplay.Global
