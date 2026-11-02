import ChaCha.Paper20261030.DecompositionInventory
import ChaCha.Paper20261030.PackedRecordDecoding

/-!
# Existing reference intervals are unique immutable record identifiers

Each secondary record already stores its original `(lo,cut,hi)` interval.
A terminal has `(d,d,d)`; an internal reference vertex has `cut < hi`.
These triples are distinct over the entire reference, and remain distinct
after suffix restriction and any maintained balanced decomposition.
No allocated addresses or uncharged identifier-to-pointer lookup is used:
an identifier selects a record only from the bounded list actually read.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open ColoredStorage AuxiliaryComponent BoundaryObservations PathDecomposition

def recordId (record : Cached) : DepthSplit := record.2.2.1.1

theorem source_id_bounds {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    {id : DepthSplit} (member : id ∈ (source reference p).inventory recordId) :
    a ≤ id.lo ∧ id.lo ≤ id.cut ∧ id.cut ≤ id.hi ∧ id.hi ≤ b := by
  induction reference with
  | leaf a =>
    have same : id = ⟨a,a,a⟩ := by simpa only [source,Source.inventory_leaf,recordId,Multiset.mem_singleton] using member
    subst id
    exact ⟨le_rfl,le_rfl,le_rfl,le_rfl⟩
  | @node a b cut lower upper l r ihl ihr =>
    simp only [source,Source.inventory_fork,recordId,Multiset.mem_add,Multiset.mem_singleton] at member
    rcases member with (rfl | left) | right
    · exact ⟨le_rfl,lower,Nat.le_of_lt upper,le_rfl⟩
    · obtain ⟨h₁,h₂,h₃,h₄⟩ := ihl left
      exact ⟨h₁,h₂,h₃,by omega⟩
    · obtain ⟨h₁,h₂,h₃,h₄⟩ := ihr right
      exact ⟨by omega,h₂,h₃,h₄⟩

theorem source_ids_nodup {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool) :
    ((source reference p).inventory recordId).Nodup := by
  induction reference with
  | leaf a => simp [source]
  | @node a b cut lower upper l r ihl ihr =>
    have rootLeft : Disjoint ({DepthSplit.mk a cut b} : Multiset DepthSplit) ((source l p).inventory recordId) := by
      apply Multiset.disjoint_left.mpr
      intro id root member
      have same := Multiset.mem_singleton.mp root
      subst id
      have bounds := source_id_bounds l p member
      simp only at bounds
      omega
    have rootRight : Disjoint ({DepthSplit.mk a cut b} : Multiset DepthSplit) ((source r p).inventory recordId) := by
      apply Multiset.disjoint_left.mpr
      intro id root member
      have same := Multiset.mem_singleton.mp root
      subst id
      have bounds := source_id_bounds r p member
      simp only at bounds
      omega
    have separated : Disjoint ((source l p).inventory recordId) ((source r p).inventory recordId) := by
      apply Multiset.disjoint_left.mpr
      intro id left right
      have lb := source_id_bounds l p left
      have rb := source_id_bounds r p right
      omega
    simp only [source,Source.inventory_fork,recordId]
    exact Multiset.nodup_add.mpr ⟨Multiset.nodup_add.mpr ⟨by simp,ihl,rootLeft⟩,
      ihr,Multiset.disjoint_add_left.mpr ⟨rootRight,separated⟩⟩

theorem suffix_ids_le {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) :
    (suffixSource reference p d valid).inventory recordId ≤ (source reference p).inventory recordId := by
  induction reference with
  | leaf a =>
    have equal : d = a := by omega
    subst d
    exact le_rfl
  | @node a b cut lower upper l r ihl ihr =>
    unfold suffixSource
    split
    · simpa only [source,Source.inventory_fork] using
        add_le_add (add_le_add le_rfl (ihl _)) le_rfl
    · exact (ihr _).trans (by
        simp only [source,Source.inventory_fork]
        exact le_add_of_nonneg_left zero_le)

theorem represented_ids_nodup {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    ((closed c).inventory recordId).Nodup := by
  have inventory := represented.closed_inventory (fun entry => entry.2.1)
  change (closed c).inventory recordId = (source reference p).inventory recordId at inventory
  rw [inventory]
  exact source_ids_nodup reference p

theorem represented_suffix_ids_nodup {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference p d valid) c) :
    ((closed c).inventory recordId).Nodup := by
  have inventory := represented.closed_inventory (fun entry => entry.2.1)
  change (closed c).inventory recordId = (suffixSource reference p d valid).inventory recordId at inventory
  rw [inventory]
  exact Multiset.nodup_of_le (suffix_ids_le reference p d valid) (source_ids_nodup reference p)

theorem represented_ids_distinguish {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    Distinguishes recordId (closed c) :=
  Multiset.inj_on_of_nodup_map (represented_ids_nodup reference p c represented)

theorem represented_suffix_ids_distinguish {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference p d valid) c) :
    Distinguishes recordId (closed c) :=
  Multiset.inj_on_of_nodup_map (represented_suffix_ids_nodup reference p d valid c represented)

end ChaCha.Paper20261030.SecondaryDecomposition
