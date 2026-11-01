import TaggedTransfer
import OrderedPortRestoration

/-! Paid restoration changes the global state-defined labels only on the
actual inserted port keys. Receiving-grower conversion and positional
splitting preserve every other entry/base pair exactly. -/

namespace GreedyMerge.StateLabels

open OrderedBlocks Primitives BlockCoverage
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

theorem tagged_installPaid (owner : ℕ) (side : Bool)
    (splitStart paidId paidFamily base ownerRank : ℕ) (entry : Entry)
    (state : SideState) (item : Entry × ℕ) :
    item ∈ tagged ownerRank (installPaid owner side splitStart paidId paidFamily base entry state) ↔
      item = (entry, base) ∨ item ∈ tagged ownerRank state := by
  have partition := separateOuter_tagged_cover side entry.key splitStart state item
  simp only [frozenTagged] at partition
  simp only [installPaid, tagged_eq, frozenTagged, List.flatMap_append, List.flatMap_cons,
    OrderedBlocks.singleton, List.map_cons, List.map_nil, List.flatMap_nil, List.append_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem tagged_paidInsertion (owner : ℕ) (side : Bool)
    (family id splitStart paidId paidFamily ownerRank : ℕ) (entry : Entry)
    (state : SideState) (item : Entry × ℕ) :
    item ∈ tagged ownerRank (paidInsertion owner side family id splitStart paidId paidFamily ownerRank entry state) ↔
      item = (entry, ownerRank) ∨ item ∈ tagged ownerRank state := by
  unfold paidInsertion
  rw [tagged_installPaid, tagged_convert]

theorem restorePort_hasBase {n : ℕ} (before tree : BST 0 n)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n)
    (states : States n) (entryKey : ∀ owner, (makeEntry owner).key = record.val)
    (key base : ℕ) (outside : key ≠ record.val) :
    HasBase before.externalDepth (restorePort (Snapshot.ofTree before) tree names makeEntry record states).1 key base ↔
      HasBase before.externalDepth states key base := by
  cases parent : canonicalParent (Snapshot.ofTree before) tree record with
  | none => simp [restorePort, parent]
  | some actualOwner =>
      have point (owner : External n) (side : Bool) (entry : Entry) (equal : entry.key = key) :
          (entry, base) ∈ tagged (before.externalDepth owner.val)
            ((restorePort (Snapshot.ofTree before) tree names makeEntry record states).1 owner side) ↔
          (entry, base) ∈ tagged (before.externalDepth owner.val) (states owner side) := by
        simp only [restorePort, parent, replaceSide]
        split_ifs with location
        · obtain ⟨rfl, rfl⟩ := location
          change (entry, base) ∈ tagged (before.externalDepth owner.val)
            (paidInsertion owner.val _ _ _ _ _ _ (before.externalDepth owner.val) _ _) ↔ _
          rw [tagged_paidInsertion]
          have different : (entry, base) ≠ (makeEntry owner, before.externalDepth owner.val) := by
            intro same
            have entries := congrArg Prod.fst same
            exact outside (equal.symm.trans ((congrArg Entry.key entries).trans (entryKey owner)))
          simp only [different, false_or]
        · rfl
      constructor
      · rintro ⟨owner, side, entry, member, equal⟩
        exact ⟨owner, side, entry, (point owner side entry equal).mp member, equal⟩
      · rintro ⟨owner, side, entry, member, equal⟩
        exact ⟨owner, side, entry, (point owner side entry equal).mpr member, equal⟩

theorem restorePort_label {n : ℕ} (before tree : BST 0 n) (K : ℤ)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n)
    (states : States n) (entryKey : ∀ owner, (makeEntry owner).key = record.val)
    (key : ℕ) (outside : key ≠ record.val) :
    label before.externalDepth K (restorePort (Snapshot.ofTree before) tree names makeEntry record states).1 key =
      label before.externalDepth K states key := by
  apply label_congr
  intro base
  exact restorePort_hasBase before tree names makeEntry record states entryKey key base outside

theorem restorePorts_label {n : ℕ} (before tree : BST 0 n) (K : ℤ)
    (names : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (entryKey : ∀ stage record owner, (makeEntry stage record owner).key = record.val)
    (ports : List (External n)) (stage : ℕ) (states : States n)
    (key : ℕ) (outside : key ∉ ports.map Fin.val) :
    label before.externalDepth K
      (restorePorts (Snapshot.ofTree before) tree names makeEntry ports stage states).1 key =
      label before.externalDepth K states key := by
  induction ports generalizing stage states with
  | nil => rfl
  | cons record rest ih =>
      have excluded : key ≠ record.val ∧ key ∉ rest.map Fin.val := by
        simpa only [List.map_cons, List.mem_cons, not_or] using outside
      have different := excluded.1
      have restOutside := excluded.2
      change label _ K (restorePorts (Snapshot.ofTree before) tree names makeEntry rest (stage+1)
        (restorePort (Snapshot.ofTree before) tree (names stage) (makeEntry stage record) record states).1).1 key = _
      rw [ih (stage+1) _ restOutside]
      exact restorePort_label before tree K (names stage) (makeEntry stage record) record states
        (entryKey stage record) key different

end GreedyMerge.StateLabels

#print axioms GreedyMerge.StateLabels.restorePorts_label
