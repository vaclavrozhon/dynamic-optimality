import Splay.Rank.Basic
import Splay.Tree.ExternalDepthMin

namespace Splay.Rank

/--
Value- and null-node depths in a comparison BST produce a valid static rank
snapshot.

The comparison tree itself has `n` value nodes. Its empty children are the
`n + 1` null nodes, producing `2 * n + 1` external inorder positions.
-/
def Snapshot.ofTree {n : ℕ}
    (tree : Tree.BST 0 n) : Snapshot n where
  rank node := tree.externalDepth node.val
  maxRank := tree.height
  rank_le_max node := tree.externalDepth_le_height node.val
  uniqueIntervalMin := by
    intro lower upper hNonempty
    obtain ⟨key, hKeyMin, hKeyUnique⟩ :=
      tree.existsUnique_intervalExternalDepthMin
        (intervalLower := lower.val)
        (intervalUpper := upper.val)
        (Nat.zero_le lower.val)
        hNonempty
        (by omega)
    let keyNode : External n :=
      ⟨key, lt_of_le_of_lt hKeyMin.2.1 upper.isLt⟩
    refine ⟨keyNode, ?_, ?_⟩
    · exact ⟨hKeyMin.1, hKeyMin.2.1, fun node hLower hUpper =>
        hKeyMin.2.2 node.val hLower hUpper⟩
    · intro other hOther
      apply Fin.ext
      apply hKeyUnique other.val
      refine ⟨hOther.1, hOther.2.1, ?_⟩
      intro candidate hCandidateLower hCandidateUpper
      let candidateNode : External n :=
        ⟨candidate, lt_of_le_of_lt hCandidateUpper upper.isLt⟩
      exact hOther.2.2 candidateNode hCandidateLower hCandidateUpper
  hasZero := by
    obtain ⟨position, _, hPositionUpper, hDepth⟩ :=
      tree.exists_externalDepth_eq_zero
    exact ⟨⟨position, by omega⟩, hDepth⟩

end Splay.Rank
