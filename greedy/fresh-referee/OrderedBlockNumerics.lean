import OrderedBlockPrimitives

/-!
Integral absolute-base transport for concrete frozen blocks. All bases and
comparator ranks are natural numbers; only signed depth shifts are integers.
This discharges the integrality interface to the natural phase bucket model.
-/
namespace GreedyMerge.OrderedBlocks

/-- Absolute-base form of δ' = max(0,δ+c), with the owner/rank change
performed as one transaction. -/
def transportedBase (oldBase newOwnerRank : ℕ) (memberShift : ℤ) : ℕ :=
  max newOwnerRank ((oldBase : ℤ) + memberShift).toNat

theorem transportedBase_valid (oldRank newRank oldBase newOwnerRank : ℕ)
    (memberShift : ℤ) (oldValid : oldBase ≤ oldRank)
    (newHeap : newOwnerRank ≤ newRank)
    (shift : (newRank : ℤ) = (oldRank : ℤ) + memberShift) :
    newOwnerRank ≤ transportedBase oldBase newOwnerRank memberShift ∧
    transportedBase oldBase newOwnerRank memberShift ≤ newRank ∧
    newRank - transportedBase oldBase newOwnerRank memberShift ≤ oldRank - oldBase := by
  unfold transportedBase
  constructor
  · exact le_max_left _ _
  constructor
  · apply max_le
    · exact newHeap
    · omega
  · rcases le_total newOwnerRank ((oldBase : ℤ) + memberShift).toNat with h | h
    · rw [max_eq_right h]
      omega
    · rw [max_eq_left h]
      omega

/-- Block validity uses the absolute base, rather than silently coercing
a real-valued offset to the natural gap function used in the accounting. -/
def BaseValid (rank : ℕ → ℕ) (owner : ℕ) (block : Frozen) : Prop :=
  rank owner ≤ block.base ∧ ∀ entry ∈ block.members, block.base ≤ rank entry.key

/-- The whole-block rebase keeps exactly the old immutable Entry records,
creator and family, and makes every actual natural gap weakly decrease. -/
theorem rebase_uniform_block (beforeRank afterRank : ℕ → ℕ)
    (oldOwner newOwner : ℕ) (block : Frozen) (shift : ℤ)
    (oldValid : BaseValid beforeRank oldOwner block)
    (newHeap : ∀ entry ∈ block.members, afterRank newOwner ≤ afterRank entry.key)
    (uniform : ∀ entry ∈ block.members,
      (afterRank entry.key : ℤ) = (beforeRank entry.key : ℤ) + shift) :
    let updated := rebase (transportedBase block.base (afterRank newOwner) shift) block
    BaseValid afterRank newOwner updated ∧ Descends updated block ∧
      ∀ entry ∈ block.members, afterRank entry.key - updated.base ≤ beforeRank entry.key - block.base := by
  dsimp
  constructor
  · constructor
    · exact le_max_left _ _
    · intro entry member
      exact (transportedBase_valid (beforeRank entry.key) (afterRank entry.key)
        block.base (afterRank newOwner) shift (oldValid.2 entry member)
        (newHeap entry member) (uniform entry member)).2.1
  constructor
  · exact rebase_descends block _
  · intro entry member
    exact (transportedBase_valid (beforeRank entry.key) (afterRank entry.key)
      block.base (afterRank newOwner) shift (oldValid.2 entry member)
      (newHeap entry member) (uniform entry member)).2.2

#print axioms transportedBase_valid
#print axioms rebase_uniform_block

end GreedyMerge.OrderedBlocks
