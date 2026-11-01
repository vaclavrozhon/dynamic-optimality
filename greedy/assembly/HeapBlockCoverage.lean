import OrderedPortDeletion
import OrderedPaidInsertion

/-!
Coverage of the actual canonical heap by concrete side-block states.
ParentSound gives the correct owner of every represented key; CompleteExcept
additionally requires every nonroot outside an explicit detached-port set.
These lemmas separate global coverage from local ordering and parent soundness.
-/

namespace GreedyMerge.BlockCoverage

open OrderedBlocks Primitives
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

abbrev States (n : ℕ) := External n → Bool → SideState

def Represented {n : ℕ} (states : States n) (key : ℕ) : Prop :=
  ∃ owner side entry, entry ∈ entries (states owner side) ∧ entry.key = key

def Sound {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (states : States n) : Prop :=
  ∀ owner side, ParentSound snapshot tree owner (states owner side)

def CompleteExcept {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (states : States n) (missing : Finset ℕ) : Prop :=
  ∀ record owner, canonicalParent snapshot tree record = some owner → record.val ∉ missing →
    ∃ side entry, entry ∈ entries (states owner side) ∧ entry.key = record.val

abbrev Complete {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (states : States n) : Prop :=
  CompleteExcept snapshot tree states ∅

theorem represented_has_owner {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (states : States n) (sound : Sound snapshot tree states)
    (record owner : External n) (parent : canonicalParent snapshot tree record = some owner)
    (present : Represented states record.val) :
    ∃ side entry, entry ∈ entries (states owner side) ∧ entry.key = record.val := by
  obtain ⟨actualOwner, side, entry, member, key⟩ := present
  obtain ⟨actualRecord, actualKey, actualParent⟩ := sound actualOwner side entry member
  have recordEqual : actualRecord = record := Fin.ext (actualKey.trans key)
  rw [recordEqual, parent] at actualParent
  have ownerEqual := Option.some.inj actualParent
  exact ⟨side, entry, by simpa only [ownerEqual] using member, key⟩

theorem represented_filter {n : ℕ} (before after : States n) (key record : ℕ)
    (exactEntries : ∀ owner side, entries (after owner side) =
      (entries (before owner side)).filter (fun entry => entry.key != key)) :
    Represented after record ↔ Represented before record ∧ record ≠ key := by
  constructor
  · rintro ⟨owner, side, entry, member, equal⟩
    rw [exactEntries] at member
    have data := List.mem_filter.mp member
    refine ⟨⟨owner, side, entry, data.1, equal⟩, ?_⟩
    simpa only [equal, bne_iff_ne] using data.2
  · rintro ⟨⟨owner, side, entry, member, equal⟩, different⟩
    refine ⟨owner, side, entry, ?_, equal⟩
    rw [exactEntries]
    exact List.mem_filter.mpr ⟨member, by simpa only [equal, bne_iff_ne] using different⟩

theorem completeExcept_detach {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (before after : States n) (missing : Finset ℕ) (key : ℕ)
    (complete : CompleteExcept snapshot tree before missing)
    (exactEntries : ∀ owner side, entries (after owner side) =
      (entries (before owner side)).filter (fun entry => entry.key != key)) :
    CompleteExcept snapshot tree after (insert key missing) := by
  intro record owner parent outside
  have absent : record.val ≠ key ∧ record.val ∉ missing := by simpa using outside
  obtain ⟨side, entry, member, equal⟩ := complete record owner parent absent.2
  refine ⟨side, entry, ?_, equal⟩
  rw [exactEntries]
  exact List.mem_filter.mpr ⟨member, by simpa only [equal, bne_iff_ne] using absent.1⟩

/-- Whole-block moves may change every member's owner, but preserve
coverage. If all changed global roots were detached as ports, the new
heap has exactly the same coverage obligation outside those ports. -/
theorem completeExcept_reparent {n : ℕ}
    (oldSnapshot newSnapshot : Snapshot n) (oldTree newTree : BST 0 n)
    (before after : States n) (missing : Finset ℕ)
    (complete : CompleteExcept oldSnapshot oldTree before missing)
    (sound : Sound newSnapshot newTree after)
    (rootCase : canonicalRoot oldSnapshot oldTree = canonicalRoot newSnapshot newTree ∨
      (canonicalRoot oldSnapshot oldTree).val ∈ missing)
    (preserved : ∀ key, key ∉ missing → Represented before key → Represented after key) :
    CompleteExcept newSnapshot newTree after missing := by
  intro record owner parent outside
  have notOldRoot : record ≠ canonicalRoot oldSnapshot oldTree := by
    intro equal
    rcases rootCase with sameRoot | detached
    · have none := (canonicalParent_eq_none_iff newSnapshot newTree record).2 (equal.trans sameRoot)
      rw [parent] at none
      contradiction
    · exact outside (by simpa only [equal] using detached)
  cases oldParent : canonicalParent oldSnapshot oldTree record with
  | none =>
      exact False.elim (notOldRoot ((canonicalParent_eq_none_iff oldSnapshot oldTree record).1 oldParent))
  | some oldOwner =>
      obtain ⟨side, entry, member, equal⟩ := complete record oldOwner oldParent outside
      exact represented_has_owner newSnapshot newTree after sound record owner parent
        (preserved record.val outside ⟨oldOwner, side, entry, member, equal⟩)

theorem completeExcept_restore {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (before after : States n) (missing : Finset ℕ) (key : ℕ)
    (complete : CompleteExcept snapshot tree before missing)
    (sound : Sound snapshot tree after)
    (preserved : ∀ record, Represented before record → Represented after record)
    (installed : Represented after key) :
    CompleteExcept snapshot tree after (missing.erase key) := by
  intro record owner parent outside
  apply represented_has_owner snapshot tree after sound record owner parent
  by_cases selected : record.val = key
  · simpa only [selected] using installed
  · have oldOutside : record.val ∉ missing := by
      intro member
      exact outside (Finset.mem_erase.mpr ⟨selected, member⟩)
    obtain ⟨side, entry, member, equal⟩ := complete record owner parent oldOutside
    exact preserved _ ⟨owner, side, entry, member, equal⟩

theorem completeExcept_root_complete {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (states : States n) (missing : Finset ℕ)
    (complete : CompleteExcept snapshot tree states missing)
    (onlyRoot : ∀ key ∈ missing, key = (canonicalRoot snapshot tree).val) :
    Complete snapshot tree states := by
  intro record owner parent _
  apply complete record owner parent
  intro missingRecord
  have root : record = canonicalRoot snapshot tree := Fin.ext (onlyRoot record.val missingRecord)
  have none := (canonicalParent_eq_none_iff snapshot tree record).2 root
  rw [parent] at none
  contradiction

end GreedyMerge.BlockCoverage

#print axioms GreedyMerge.BlockCoverage.completeExcept_reparent
#print axioms GreedyMerge.BlockCoverage.completeExcept_restore
#print axioms GreedyMerge.BlockCoverage.completeExcept_root_complete
