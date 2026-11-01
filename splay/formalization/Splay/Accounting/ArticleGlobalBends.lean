import Splay.Accounting.ArticleUniformExecution
import Splay.Accounting.WholeSplayTemporaryGeometry

namespace Splay.Accounting

open Splay.Tree.BST Splay.Assumptions.NormalForm

def articleBendConstants (slack : ℕ) : BendConstants where
  initial := 1
  splay := 2 + 6 * (slack + 1)
  comparisonRotation := 3

/-- The existing complete-splay and comparison-rotation bend constructions
give a global bound without an input schedule or local certificate provider. -/
theorem article_global_zigZag_bound {n : ℕ} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses} {bounds : StructuralBounds}
    (normal : IsStructurallyNormal bounds comparison) (tree : BST 0 n) :
    (concreteSplayTranscript tree accesses).zigZag ≤
      (concreteSplayTranscript tree accesses).zigZig +
        (articleBendConstants bounds.neighborDepthSlack).coefficient * (n + comparison.cost) := by
  obtain ⟨groups, final, schedule, requests, _, _, _⟩ := comparison.exists_normalFormSchedule tree
  exact WholeSplayTemporaryGeometry.canonical_concrete_zigZag_bends
    (constants := articleBendConstants bounds.neighborDepthSlack) (normal := normal) schedule
    le_rfl le_rfl requests le_rfl le_rfl le_rfl

namespace ConstructedPolylogNormalForm

theorem articleRun_zigZags {n : ℕ} (tree : BST 0 n) (accesses : List (Fin n)) :
    (concreteSplayTranscript tree accesses).zigZag ≤
      (concreteSplayTranscript tree accesses).zigZig + 132 * (n + (trace accesses).cost) :=
  article_global_zigZag_bound (structurallyNormal accesses) tree

end ConstructedPolylogNormalForm
end Splay.Accounting
