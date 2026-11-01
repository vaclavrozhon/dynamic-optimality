import OrderedGrowerPreparation
import OrderedPortDeletion

/-!
Construct the preparation half of one comparator macro: select and seal
rank-mismatched growers, detach the finite paid port set, seal the bulk
source/receiver sides, and split actual blocks at all rank cuts. Every
budget below is derived from the executed operations and old heap geometry.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

abbrev HeapSides (n : ℕ) := External n → Bool → SideState
abbrev NameSupply (n : ℕ) := ℕ → External n → Bool → ℕ

def prepareAllGrowers {n : ℕ} (before after : BST 0 n)
    (family id : External n → Bool → ℕ) (states : HeapSides n) : HeapSides n :=
  fun owner side => prepareGrower before after owner (family owner side) (id owner side) (states owner side)

theorem prepareAllGrowers_valid {n : ℕ} (before after : BST 0 n)
    (family id : External n → Bool → ℕ) (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side)) :
    ∀ owner side, Valid owner.val side (prepareAllGrowers before after family id states owner side) := by
  intro owner side
  exact prepareGrower_valid before after owner _ _ side _ (valid owner side)

theorem prepareAllGrowers_sound {n : ℕ} (before after tree : BST 0 n)
    (family id : External n → Bool → ℕ) (states : HeapSides n)
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner (states owner side)) :
    ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner
      (prepareAllGrowers before after family id states owner side) := by
  intro owner side
  simpa only [prepareAllGrowers, ParentSound, prepareGrower_entries] using sound owner side

noncomputable def detachAll {n : ℕ} (before : BST 0 n) (key : ℕ)
    (family id : External n → Bool → ℕ) (states : HeapSides n) : HeapSides n :=
  fun owner side => detachPort owner.val (family owner side) (id owner side)
    (before.externalDepth owner.val) key (states owner side)

theorem detachAll_valid {n : ℕ} (before : BST 0 n) (key : ℕ)
    (family id : External n → Bool → ℕ) (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side)) :
    ∀ owner side, Valid owner.val side (detachAll before key family id states owner side) := by
  intro owner side
  exact detachPort_valid owner.val _ _ _ key side _ (valid owner side)

theorem detachAll_sound {n : ℕ} (before tree : BST 0 n) (key : ℕ)
    (family id : External n → Bool → ℕ) (states : HeapSides n)
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner (states owner side)) :
    ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner
      (detachAll before key family id states owner side) := by
  intro owner side
  exact detachPort_sound (Snapshot.ofTree before) tree owner _ _ _ key _ (sound owner side)

noncomputable def detachPorts {n : ℕ} (before : BST 0 n) (families ids : NameSupply n) :
    List ℕ → ℕ → HeapSides n → HeapSides n × ℕ
  | [], _, states => (states, 0)
  | key :: rest, stage, states =>
      let next := detachAll before key (families stage) (ids stage) states
      let tail := detachPorts before families ids rest (stage+1) next
      (tail.1, (portSources key states).card + tail.2)

theorem detachPorts_valid {n : ℕ} (before : BST 0 n) (families ids : NameSupply n)
    (ports : List ℕ) (stage : ℕ) (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side)) :
    ∀ owner side, Valid owner.val side ((detachPorts before families ids ports stage states).1 owner side) := by
  induction ports generalizing stage states with
  | nil => exact valid
  | cons key rest ih =>
      exact ih (stage+1) _ (detachAll_valid before key _ _ states valid)

theorem detachPorts_sound {n : ℕ} (before tree : BST 0 n) (families ids : NameSupply n)
    (ports : List ℕ) (stage : ℕ) (states : HeapSides n)
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner (states owner side)) :
    ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner
      ((detachPorts before families ids ports stage states).1 owner side) := by
  induction ports generalizing stage states with
  | nil => exact sound
  | cons key rest ih =>
      exact ih (stage+1) _ (detachAll_sound before tree key _ _ states sound)

theorem detachPorts_births_le {n : ℕ} (before tree : BST 0 n) (families ids : NameSupply n)
    (ports : List ℕ) (stage : ℕ) (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner (states owner side)) :
    (detachPorts before families ids ports stage states).2 ≤ ports.length := by
  induction ports generalizing stage states with
  | nil => simp [detachPorts]
  | cons key rest ih =>
      have head := portSources_card_le_one (Snapshot.ofTree before) tree key states valid sound
      have tail := ih (stage+1) (detachAll before key (families stage) (ids stage) states)
        (detachAll_valid before key _ _ states valid) (detachAll_sound before tree key _ _ states sound)
      change (portSources key states).card +
        (detachPorts before families ids rest (stage+1)
          (detachAll before key (families stage) (ids stage) states)).2 ≤ _
      simp only [List.length_cons]
      omega

def sealOwners {n : ℕ} (before : BST 0 n) (owners : Finset (External n))
    (families ids : External n → Bool → ℕ) (states : HeapSides n) : HeapSides n :=
  fun owner side => if owner ∈ owners then
    convert owner.val (families owner side) (ids owner side) (before.externalDepth owner.val) (states owner side)
    else states owner side

noncomputable def sealOwnersBirths {n : ℕ} (owners : Finset (External n)) (states : HeapSides n) : ℕ :=
  ∑ owner ∈ owners, (conversionBirths (states owner false) + conversionBirths (states owner true))

theorem sealOwners_entries {n : ℕ} (before : BST 0 n) (owners : Finset (External n))
    (families ids : External n → Bool → ℕ) (states : HeapSides n) (owner : External n) (side : Bool) :
    entries (sealOwners before owners families ids states owner side) = entries (states owner side) := by
  unfold sealOwners
  split_ifs <;> simp

theorem sealOwners_valid {n : ℕ} (before : BST 0 n) (owners : Finset (External n))
    (families ids : External n → Bool → ℕ) (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side)) :
    ∀ owner side, Valid owner.val side (sealOwners before owners families ids states owner side) := by
  intro owner side
  unfold sealOwners
  split_ifs
  · exact conversion_valid owner.val _ _ _ side _ (valid owner side)
  · exact valid owner side

theorem sealOwners_sound {n : ℕ} (before tree : BST 0 n) (owners : Finset (External n))
    (families ids : External n → Bool → ℕ) (states : HeapSides n)
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner (states owner side)) :
    ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner
      (sealOwners before owners families ids states owner side) := by
  intro owner side
  simpa only [ParentSound, sealOwners_entries] using sound owner side

theorem sealOwners_empty {n : ℕ} (before : BST 0 n) (owners : Finset (External n))
    (families ids : External n → Bool → ℕ) (states : HeapSides n)
    (owner : External n) (member : owner ∈ owners) (side : Bool) :
    growerEntries (sealOwners before owners families ids states owner side).grower = [] := by
  simpa only [sealOwners, if_pos member] using
    converted_grower_empty owner.val (families owner side) (ids owner side)
      (before.externalDepth owner.val) (states owner side)

theorem sealOwnersBirths_le {n : ℕ} (owners : Finset (External n)) (states : HeapSides n) :
    sealOwnersBirths owners states ≤ 2 * owners.card := by
  classical
  calc
    sealOwnersBirths owners states ≤ ∑ _owner ∈ owners, 2 := by
      apply Finset.sum_le_sum
      intro owner member
      have left := conversionBirths_le_one (states owner false)
      have right := conversionBirths_le_one (states owner true)
      omega
    _ = 2 * owners.card := by simp [Nat.mul_comm]

noncomputable def prepareComparator {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth)
    (families ids : NameSupply n) (ports : List ℕ) (bulkOwners : Finset (External n))
    (states : HeapSides n) : HeapSides n × ℕ :=
  let growing := prepareAllGrowers before after (families 0) (ids 0) states
  let detached := detachPorts before families ids ports 1 growing
  let sealed := sealOwners before bulkOwners (families (ports.length+1)) (ids (ports.length+1)) detached.1
  let cuts := prepareCuts ids profile.entries (ports.length+2) sealed
  (cuts.1, allGrowerPreparationBirths before after states + detached.2 +
    sealOwnersBirths bulkOwners detached.1 + cuts.2)

theorem prepareComparator_valid {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth)
    (families ids : NameSupply n) (ports : List ℕ) (bulkOwners : Finset (External n))
    (states : HeapSides n) (valid : ∀ owner side, Valid owner.val side (states owner side)) :
    ∀ owner side, Valid owner.val side
      ((prepareComparator profile families ids ports bulkOwners states).1 owner side) := by
  apply prepareCuts_valid
  apply sealOwners_valid
  apply detachPorts_valid
  exact prepareAllGrowers_valid before after _ _ states valid

theorem prepareComparator_sound {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (families ids : NameSupply n) (ports : List ℕ) (bulkOwners : Finset (External n))
    (states : HeapSides n)
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner (states owner side)) :
    ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner
      ((prepareComparator profile families ids ports bulkOwners states).1 owner side) := by
  apply prepareCuts_sound
  apply sealOwners_sound
  apply detachPorts_sound
  exact prepareAllGrowers_sound before after tree _ _ states sound

/-- The actual composed preparation program has a derived administration
budget: rank conversions 2B, port-source conversions |D|, bulk seals 2|U|,
and rank-cut split births 2B, where B=(depth+2)^2. -/
theorem prepareComparator_births_le {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (families ids : NameSupply n) (ports : List ℕ) (bulkOwners : Finset (External n))
    (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner (states owner side)) :
    (prepareComparator profile families ids ports bulkOwners states).2 ≤
      4*(depth+2)^2 + ports.length + 2*bulkOwners.card := by
  let growing := prepareAllGrowers before after (families 0) (ids 0) states
  let detached := detachPorts before families ids ports 1 growing
  let sealed := sealOwners before bulkOwners (families (ports.length+1)) (ids (ports.length+1)) detached.1
  have growingValid := prepareAllGrowers_valid before after (families 0) (ids 0) states valid
  have growingSound := prepareAllGrowers_sound before after tree (families 0) (ids 0) states sound
  have detachedValid := detachPorts_valid before families ids ports 1 growing growingValid
  have detachedSound := detachPorts_sound before tree families ids ports 1 growing growingSound
  have sealedValid := sealOwners_valid before bulkOwners (families (ports.length+1)) (ids (ports.length+1)) detached.1 detachedValid
  have sealedSound := sealOwners_sound before tree bulkOwners (families (ports.length+1)) (ids (ports.length+1)) detached.1 detachedSound
  have first := allGrowerPreparationBirths_le profile tree states sound
  have second := detachPorts_births_le before tree families ids ports 1 growing growingValid growingSound
  change detached.2 ≤ ports.length at second
  have third := sealOwnersBirths_le bulkOwners detached.1
  have fourth := prepareProfile_births_le profile tree ids (ports.length+2) sealed sealedValid sealedSound
  change allGrowerPreparationBirths before after states + detached.2 +
    sealOwnersBirths bulkOwners detached.1 + (prepareCuts ids profile.entries (ports.length+2) sealed).2 ≤ _
  omega

theorem detachPorts_membership {n : ℕ} (before : BST 0 n) (families ids : NameSupply n)
    (ports : List ℕ) (stage : ℕ) (states : HeapSides n) (owner : External n) (side : Bool)
    (entry : Entry) :
    entry ∈ entries ((detachPorts before families ids ports stage states).1 owner side) ↔
      entry ∈ entries (states owner side) ∧ entry.key ∉ ports := by
  induction ports generalizing stage states with
  | nil => simp [detachPorts]
  | cons key rest ih =>
      change entry ∈ entries ((detachPorts before families ids rest (stage+1)
        (detachAll before key (families stage) (ids stage) states)).1 owner side) ↔ _
      rw [ih]
      simp only [detachAll, detachPort_entries, List.mem_filter, bne_iff_ne, List.mem_cons,
        not_or]
      tauto

theorem prepareComparator_membership {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (families ids : NameSupply n)
    (ports : List ℕ) (bulkOwners : Finset (External n)) (states : HeapSides n)
    (owner : External n) (side : Bool) (entry : Entry) :
    entry ∈ entries ((prepareComparator profile families ids ports bulkOwners states).1 owner side) ↔
      entry ∈ entries (states owner side) ∧ entry.key ∉ ports := by
  change entry ∈ entries ((prepareCuts ids profile.entries (ports.length+2)
    (sealOwners before bulkOwners (families (ports.length+1)) (ids (ports.length+1))
      (detachPorts before families ids ports 1
        (prepareAllGrowers before after (families 0) (ids 0) states)).1)).1 owner side) ↔ _
  rw [prepareCuts_entries, sealOwners_entries, detachPorts_membership]
  simp only [prepareAllGrowers, prepareGrower_entries]

#print axioms prepareComparator_valid
#print axioms prepareComparator_sound
#print axioms prepareComparator_births_le
#print axioms prepareComparator_membership

end GreedyMerge.OrderedBlocks
