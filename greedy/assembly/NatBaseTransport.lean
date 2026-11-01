import Splay.Analysis.ContractedGap

/-!
Integral absolute-base transport for actual frozen source blocks.
If every member's rank changes by `shift`, transport its old absolute
base by that shift, clipping at the new owner's rank. This is exactly
the paper's lower-bound-offset update in natural-number coordinates.
-/

namespace GreedyMerge.BaseTransport

open Splay.Analysis

def transport (oldBase newOwner : ℕ) (shift : ℤ) : ℕ :=
  max newOwner ((oldBase : ℤ) + shift).toNat

theorem transport_spec (oldBase oldRank newOwner newRank : ℕ) (shift : ℤ)
    (oldValid : oldBase ≤ oldRank) (newParent : newOwner ≤ newRank)
    (uniform : (newRank : ℤ) - oldRank = shift) :
    newOwner ≤ transport oldBase newOwner shift ∧
    transport oldBase newOwner shift ≤ newRank ∧
    newRank - transport oldBase newOwner shift ≤ oldRank - oldBase := by
  unfold transport
  omega

theorem transported_label_le (oldBase oldRank newOwner newRank : ℕ) (shift : ℤ)
    (oldValid : oldBase ≤ oldRank) (newParent : newOwner ≤ newRank)
    (uniform : (newRank : ℤ) - oldRank = shift) :
    (contractedGap (newRank - transport oldBase newOwner shift) : ℤ) ≤
      contractedGap (oldRank - oldBase) := by
  have point := (transport_spec oldBase oldRank newOwner newRank shift
    oldValid newParent uniform).2.2
  exact_mod_cast contractedGap_mono point

/-- The absolute-base formula agrees with clipping the old lower-bound
offset after the net true-gap shift, including an owner change. -/
theorem transport_eq_offset_rebase (oldOwner oldBase newOwner : ℕ) (shift : ℤ)
    (validOffset : oldOwner ≤ oldBase) :
    transport oldBase newOwner shift =
      newOwner + ((oldBase - oldOwner : ℕ) + shift + oldOwner - newOwner).toNat := by
  unfold transport
  omega

/-- Pointwise transport is shared by an arbitrary number of records.
No individual entry or paid label update is required for these members. -/
theorem block_transport {Record : Type*} (members : Set Record)
    (oldRank newRank : Record → ℕ) (oldBase newOwner : ℕ) (shift : ℤ)
    (oldValid : ∀ record ∈ members, oldBase ≤ oldRank record)
    (newParent : ∀ record ∈ members, newOwner ≤ newRank record)
    (uniform : ∀ record ∈ members, (newRank record : ℤ) - oldRank record = shift) :
    ∀ record ∈ members,
      newOwner ≤ transport oldBase newOwner shift ∧
      transport oldBase newOwner shift ≤ newRank record ∧
      newRank record - transport oldBase newOwner shift ≤ oldRank record - oldBase := by
  intro record member
  exact transport_spec _ _ _ _ shift (oldValid record member)
    (newParent record member) (uniform record member)

end GreedyMerge.BaseTransport

#print axioms GreedyMerge.BaseTransport.block_transport
#print axioms GreedyMerge.BaseTransport.transported_label_le
#print axioms GreedyMerge.BaseTransport.transport_eq_offset_rebase
