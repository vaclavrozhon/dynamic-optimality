import Splay.Accounting.ArticleFiniteIsolation
import Splay.Accounting.ArticleFiniteGrowingPreparation
import Splay.Accounting.ArticleOwnerCuts

namespace Splay.Accounting

open Splay.Lazy

/-- The complete finite preparation used before whole-block relocation:
selected elements are singleton exceptions, affected growing slots are empty,
and all affected blocks lie in one cell of the chosen numerical cuts. -/
structure ArticleRelocationPreparation {n : ℕ} (params : Interface.Parameters) (initial : Lazy.State n)
    (selected owners : Finset (Element n)) (cuts : Finset ℕ) where
  events : List (Event n)
  final : Lazy.State n
  trace : Trace params initial events final
  stable : final.Stable params
  view_eq : final.view = initial.view
  births : final.blocks.length ≤ initial.blocks.length + 5 * selected.card +
    2 * owners.card + 4 * owners.card * cuts.card
  noInserts : Interface.totalInserts (eraseOperations events) = 0
  noIncreases : Interface.totalIncreases (eraseOperations events) = 0
  singletons : final.ShrinkingSingletons selected
  passRefines : initial.PassRefinement final
  empty : ∀ block ∈ final.blocks, block.mode = .growing → block.owner ∈ owners → block.elements = []
  cells : ∀ block ∈ final.blocks, block.owner ∈ owners →
    ∀ first ∈ block.elements, ∀ second ∈ block.elements, JunctionBendReduction.SameCutCell cuts first second

namespace ArticleRelocationPreparation

/-- This is an actual finite rich trace, using only existing conversion,
isolation, split and downward value-adjustment primitives. -/
theorem exists_preparation {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    (stable : initial.Stable params) (selected owners : Finset (Element n)) (cuts : Finset ℕ) :
    Nonempty (ArticleRelocationPreparation params initial selected owners cuts) := by
  obtain ⟨isolation⟩ := ArticleFiniteIsolation.exists_finite stable selected.toList
  obtain ⟨growings⟩ := ArticleFiniteGrowingPreparation.exists_finite isolation.stable (articleOwnerSlots owners)
  obtain ⟨splits⟩ := ArticleCutPreparation.exists_ownerCuts growings.stable owners cuts growings.ownerSlots_empty
  have isolated : isolation.final.ShrinkingSingletons selected := by simpa using isolation.singletons
  have growingSingletons := growings.singletons isolation.stable.2.1 isolated
  refine ⟨{
    events := (isolation.events ++ growings.events) ++ splits.events
    final := splits.final
    trace := (isolation.trace.append growings.trace).append splits.trace
    stable := splits.stable
    view_eq := splits.view_eq.trans (growings.view_eq.trans isolation.view_eq)
    births := ?_
    noInserts := by simp only [eraseOperations_append, Interface.totalInserts_append,
      isolation.noInserts, growings.noInserts, splits.noInserts, zero_add]
    noIncreases := by simp only [eraseOperations_append, Interface.totalIncreases_append,
      isolation.noIncreases, growings.noIncreases, splits.noIncreases, zero_add]
    singletons := growingSingletons.refine splits.refines splits.growing_preserved
    passRefines := (isolation.passRefines.trans growings.passRefines).trans splits.passRefines
    empty := fun block member growing marked =>
      growings.ownerSlots_empty block (splits.growing_preserved block member growing) growing marked
    cells := fun _ member marked _ firstIn _ secondIn => splits.ownerCuts_sameCell member marked firstIn secondIn
  }⟩
  have isolationBound := isolation.births
  have growingBound := growings.births
  have splitBound := splits.ownerCuts_births
  rw [Finset.length_toList] at isolationBound
  rw [articleOwnerSlots_length] at growingBound
  omega

/-- Any rank-change set included in both finite preparations is ready for
the final silent numerical-rank restoration. -/
theorem isolatedRanks {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    {selected owners : Finset (Element n)} {cuts : Finset ℕ}
    (execution : ArticleRelocationPreparation params initial selected owners cuts)
    {changed : Finset (Element n)} (selectedSubset : changed ⊆ selected) (ownersSubset : changed ⊆ owners) :
    execution.final.IsolatedRanks changed :=
  ⟨fun block member growing marked => execution.empty block member growing (ownersSubset marked),
    fun element marked => execution.singletons element (selectedSubset marked)⟩

end ArticleRelocationPreparation
end Splay.Accounting
