import DynamicOptimality.SingleFinger.BoundedScan
import ChaCha.Paper20261030.SourceCursorPositions

/-! Completeness of bounded scanning for a physically reached marked
vertex. Addresses occur only in this theorem's ghost hypothesis; the scanner
receives the fixed depth and the record predicate, never the address.
-/

namespace DynamicOptimality.SingleFinger.BoundedScan

open ChaCha.Paper20261030 ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ : Type*}

theorem contains_root (test : ρ → Bool) (depth : Nat) (tree : Source α ρ)
    (hit : test tree.rootRecord = true) : contains test depth tree = true := by
  cases depth <;> cases tree <;> simp_all [contains,Source.rootRecord]

theorem contains_descend (test : ρ → Bool) {before after : Cursor α ρ}
    {position : List Bool} {depth : Nat}
    (reached : SourcePositions.descend before position = some after)
    (short : position.length ≤ depth) (hit : test after.focus.rootRecord = true) :
    contains test depth before.focus = true := by
  induction position generalizing before depth with
  | nil =>
    have same := Option.some.inj reached
    subst after
    exact contains_root test depth before.focus hit
  | cons right tail ih =>
    cases depth with
    | zero => simp at short
    | succ depth =>
      rcases before with ⟨tree,outside⟩
      cases tree with
      | leaf => cases right <;> simp [SourcePositions.descend,navigate] at reached
      | fork record left rightTree =>
        have tailShort : tail.length ≤ depth := by simpa using short
        cases right
        · have found := ih (before := ⟨left,.left record rightTree::outside⟩) reached tailShort
          simp only [contains,found,Bool.or_true,Bool.true_or]
        · have found := ih (before := ⟨rightTree,.right left record::outside⟩) reached tailShort
          simp only [contains,found,Bool.or_true]

/-- A bounded physical mark guarantees that the executable scan succeeds,
with exact observed record and leaf bit, without changing the tree. -/
theorem find (test : ρ → Bool) (depth : Nat) (tree : Source α ρ)
    {position : List Bool} {marked : Cursor α ρ}
    (reached : SourcePositions.locate tree position = some marked)
    (short : position.length ≤ depth) (hit : test marked.focus.rootRecord = true) :
    ∃ (after : Cursor α ρ) (reads : List ρ) (cost : Nat),
      Steps (code test) (.running [.inspect depth]) ⟨tree,[]⟩
        (.found after.focus.rootRecord (isLeaf after.focus)) after reads cost ∧
      cost ≤ budget depth ∧ test after.focus.rootRecord = true ∧
      after.tree = tree ∧ after.ancestors.length ≤ depth := by
  have existsHit := contains_descend test reached short hit
  obtain ⟨state,after,reads,cost,run,bound,result⟩ := execute test depth tree [] []
  rcases result with ⟨none,_,_⟩ | ⟨_,found,testAfter,sameTree,shallow⟩
  · exact False.elim (Bool.noConfusion (none.symm.trans existsHit))
  · subst state
    exact ⟨after,reads,cost,run,bound,testAfter,sameTree,by simpa using shallow⟩

end DynamicOptimality.SingleFinger.BoundedScan
