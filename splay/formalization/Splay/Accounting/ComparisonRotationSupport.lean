import Splay.Accounting.ComparisonRotationJunctionBound
import Splay.Accounting.JunctionOwnerSupport
import Splay.Accounting.JunctionEdgeCorrespondence
import Splay.Rank.TemporaryBoundarySnapshot

namespace Splay.Accounting.ComparisonRotationJunctionBound

open Splay.Rank Splay.Tree.BST Splay.Lazy.Canonical JunctionBendReduction

/-- The two-position minimum-change support survives the fixed rank
doubling used throughout the completed request realizations. -/
theorem RotationAt.exists_doubledMinimumChangeSupport {n depth : ℕ} {before after : BST 0 n}
    (rotation : RotationAt depth before after) :
    ∃ selected : Finset (External n), selected.card ≤ 2 ∧
      (Snapshot.ofTree before).withTruePriority.MinimumChangesFrom (Snapshot.ofTree after).withTruePriority selected := by
  obtain ⟨selected, cardinal, changes⟩ := RotationAt.exists_minimumChangeSupport rotation
  refine ⟨selected, cardinal, ?_⟩
  intro lower upper nonempty outside
  rw [intervalMin_withTruePriority_eq] at outside
  rw [intervalMin_withTruePriority_eq, intervalMin_withTruePriority_eq]
  exact changes lower upper nonempty outside

theorem junctionCount_doubled_eq {n : ℕ} (before after : Snapshot n) (tree : BST 0 n) :
    junctionCount before.withTruePriority after.withTruePriority tree = junctionCount before after tree := by
  calc
    junctionCount before.withTruePriority after.withTruePriority tree = junctionCount before.withTruePriority after tree :=
      (junctionCountFrom_eq_of_heavyBranch_eq _ _ _
        (fun node => heavyBranch_withTruePriority_eq _ _ _ _ _) tree (Nat.le_refl n))
    _ = junctionCount after before.withTruePriority tree := junctionCountFrom_comm _ _ tree (Nat.le_refl n)
    _ = junctionCount after before tree :=
      (junctionCountFrom_eq_of_heavyBranch_eq _ _ _
        (fun node => heavyBranch_withTruePriority_eq _ _ _ _ _) tree (Nat.le_refl n))
    _ = junctionCount before after tree := junctionCountFrom_comm _ _ tree (Nat.le_refl n)

theorem RotationAt.doubled_junctionCount_le_one {n depth : ℕ} {before after splay : BST 0 n}
    (rotation : RotationAt depth before after) :
    junctionCount (Snapshot.ofTree before).withTruePriority (Snapshot.ofTree after).withTruePriority splay ≤ 1 := by
  rw [junctionCount_doubled_eq]
  exact RotationAt.junctionCount_le_one rotation

/-- At most five owner slots can change child order under a comparison
rotation, independently of its depth. Additional rank-sector preparation
uses the separate low-rank border-owner support. -/
theorem RotationAt.doubled_affectedOwners_card_le {n depth : ℕ} {before after splay : BST 0 n}
    (rotation : RotationAt depth before after) {selected : Finset (External n)} (cardinal : selected.card ≤ 2) :
    (affectedOwnerSupport (Snapshot.ofTree before).withTruePriority (Snapshot.ofTree after).withTruePriority selected splay).card ≤ 5 := by
  have bound := affectedOwnerSupport_card_le (Snapshot.ofTree before).withTruePriority (Snapshot.ofTree after).withTruePriority selected splay
  have junctions := RotationAt.doubled_junctionCount_le_one rotation (splay := splay)
  omega

end Splay.Accounting.ComparisonRotationJunctionBound
