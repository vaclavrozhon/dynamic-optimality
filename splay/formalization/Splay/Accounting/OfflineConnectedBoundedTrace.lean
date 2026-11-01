import Splay.Accounting.OfflineRestrictedMacros

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree OfflineNormalForm

/-- The connected-support normalization yields shallow actual rotations
before any height balancing is attempted. Its charge is linear in support. -/
theorem ConnectedExecution.exists_boundedTrace {n rotations support : ℕ}
    {accesses : List (Fin n)} {before after : BST 0 n}
    (execution : ConnectedExecution accesses before after rotations support) :
    ∃ count, BoundedTrace n 1 accesses before after count ∧ count ≤ 4 * support := by
  induction execution with
  | done tree =>
      exact ⟨0, .done tree (by have := tree.height_le_size; simpa using this), by omega⟩
  | @next access accesses before served after a b prefixRotations tailRotations tailSupport
      supported positive root tail ih =>
      obtain ⟨restCount, rest, restCost⟩ := ih
      have beforeHeight : before.height ≤ n := by simpa using before.height_le_size
      have afterHeight : served.height ≤ n := by simpa using served.height_le_size
      obtain ⟨path, cost, depths, heights, _, visits⟩ :=
        exists_restrictedPath_of_sameFrontier a b supported.frontier_eq positive
          (ribs_of_height beforeHeight) (ribs_of_height afterHeight)
      have selected : access.val ∈ a.keys := by
        rw [supported.keys_eq]
        exact b.mem_keys_of_hasRoot (by have := supported.card_eq; omega) root
      have prefixTrace := path.toBoundedTraceSingleton
        (heights.imp (fun tree _ => by simpa using tree.height_le_size)) depths access (visits _ selected)
      exact ⟨path.length + restCount, by simpa using prefixTrace.append rest, by omega⟩

end Splay.Accounting.OfflineConnectedSupport
