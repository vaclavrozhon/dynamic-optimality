import Splay.Lazy.CanonicalHeapView

namespace Splay.Lazy.Canonical

open Splay.Rank

/--
The initial interface value induced by the canonical heap view.

The canonical root's raw gap is zero, so this uniform formula gives it value
one. Every other canonical heap child belongs to a growing interval with
interval gap zero.
-/
noncomputable def canonicalValue {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) (element : Element n) : ℕ :=
  Analysis.transientContractedGap
    ((canonicalHeapView snapshot tree).rawGap element) 0

/-- The canonical root has the distinguished value one. -/
@[simp]
theorem canonicalValue_canonicalRoot {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    canonicalValue snapshot tree (canonicalRoot snapshot tree) = 1 := by
  have rawGapEq :
      (canonicalHeapView snapshot tree).rawGap
          (canonicalRoot snapshot tree) = 0 := by
    simp
      [HeapView.rawGap, canonicalHeapView,
        canonicalParent_canonicalRoot]
  rw [canonicalValue, rawGapEq]
  exact Analysis.transientContractedGap_self 0

/-- Away from the root, the canonical value is the contracted raw heap gap. -/
theorem canonicalValue_of_ne_root {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    {element : Element n}
    (_notRoot : element ≠ canonicalRoot snapshot tree) :
    canonicalValue snapshot tree element =
      Analysis.transientContractedGap
        ((canonicalHeapView snapshot tree).rawGap element) 0 := by
  rfl

/-- Every canonical value is positive. -/
theorem canonicalValue_pos {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (element : Element n) :
    0 < canonicalValue snapshot tree element := by
  simp only
    [canonicalValue, Analysis.transientContractedGap,
      Analysis.contractedGap]
  omega

/--
The uncontracted point gap of every canonical heap vertex is bounded by the
snapshot's maximum rank.
-/
theorem canonicalTransientPointGap_le_maxRank {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (element : Element n) :
    Analysis.transientPointGap
        ((canonicalHeapView snapshot tree).rawGap element) 0 ≤
      snapshot.maxRank := by
  let view := canonicalHeapView snapshot tree
  change
    Analysis.transientPointGap (view.rawGap element) 0 ≤
      snapshot.maxRank
  by_cases isRoot : element = view.root
  · subst element
    simp [HeapView.rawGap, Analysis.transientPointGap, view.root_parent]
  · have parentNe : view.parent element ≠ none :=
      view.parent_ne_none_of_ne_root isRoot
    cases parentEq : view.parent element with
    | none =>
        exact False.elim (parentNe parentEq)
    | some owner =>
        have rankLt : view.rank owner < view.rank element :=
          canonicalHeapView_heapOrdered snapshot tree parentEq
        have rankBound : view.rank element ≤ snapshot.maxRank := by
          simpa only [view, canonicalHeapView] using
            snapshot.rank_le_max element
        simp only
          [Analysis.transientPointGap, HeapView.rawGap, parentEq,
            Int.sub_zero]
        rw [Int.toNat_le]
        omega

/-- Canonical values never exceed the contraction of the maximum rank. -/
theorem canonicalValue_le_contractedGap_maxRank {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (element : Element n) :
    canonicalValue snapshot tree element ≤
      Analysis.contractedGap snapshot.maxRank := by
  exact
    Analysis.contractedGap_mono
      (canonicalTransientPointGap_le_maxRank snapshot tree element)

end Splay.Lazy.Canonical
