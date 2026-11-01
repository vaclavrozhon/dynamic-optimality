import Splay.Accounting.ArticleCutPreparation

namespace Splay.Accounting

open Splay.Lazy

/-- Every requested numerical cut on both sides of every affected owner. -/
noncomputable def articleOwnerCuts {n : ℕ} (owners : Finset (Element n)) (cuts : Finset ℕ) : List (ArticleCutRequest n) :=
  owners.toList.flatMap fun owner =>
    cuts.toList.map (fun cut => ⟨owner, .left, cut⟩) ++ cuts.toList.map (fun cut => ⟨owner, .right, cut⟩)

theorem articleOwnerCuts_length {n : ℕ} (owners : Finset (Element n)) (cuts : Finset ℕ) :
    (articleOwnerCuts owners cuts).length = 2 * owners.card * cuts.card := by
  have lengthFor : ∀ (list : List (Element n)),
      (list.flatMap fun owner => cuts.toList.map (fun cut => (⟨owner, .left, cut⟩ : ArticleCutRequest n)) ++
        cuts.toList.map (fun cut => (⟨owner, .right, cut⟩ : ArticleCutRequest n))).length = 2 * list.length * cuts.card := by
    intro list
    induction list with
    | nil => simp
    | cons head tail ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_map, Finset.length_toList, ih, List.length_cons]
        ring
  simpa only [articleOwnerCuts, Finset.length_toList] using lengthFor owners.toList

theorem mem_articleOwnerCuts {n : ℕ} (owners : Finset (Element n)) (cuts : Finset ℕ)
    (request : ArticleCutRequest n) :
    request ∈ articleOwnerCuts owners cuts ↔ request.owner ∈ owners ∧ request.cut ∈ cuts := by
  classical
  rcases request with ⟨owner, side, cut⟩
  cases side <;> simp [articleOwnerCuts]

namespace ArticleCutPreparation

/-- Construct all owner-side cuts from empty growing slots. -/
theorem exists_ownerCuts {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    (stable : initial.Stable params) (owners : Finset (Element n)) (cuts : Finset ℕ)
    (emptyGrowings : ∀ block ∈ initial.blocks, block.mode = .growing → block.owner ∈ owners → block.elements = []) :
    Nonempty (ArticleCutPreparation params initial (articleOwnerCuts owners cuts)) := by
  apply exists_of_emptyGrowings stable
  intro request member block blockMember growing ownerEq
  have marked := (mem_articleOwnerCuts owners cuts request).mp member
  exact emptyGrowings block blockMember growing (ownerEq.symm ▸ marked.1)

theorem ownerCuts_births {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    {owners : Finset (Element n)} {cuts : Finset ℕ}
    (execution : ArticleCutPreparation params initial (articleOwnerCuts owners cuts)) :
    execution.final.blocks.length ≤ initial.blocks.length + 4 * owners.card * cuts.card := by
  have bound := execution.births
  rw [articleOwnerCuts_length] at bound
  convert bound using 1 <;> ring

/-- Every resulting block at an affected owner lies in one numerical cut
cell. This is precisely the hypothesis of canonical junction relocation. -/
theorem ownerCuts_sameCell {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    {owners : Finset (Element n)} {cuts : Finset ℕ}
    (execution : ArticleCutPreparation params initial (articleOwnerCuts owners cuts))
    {block : Block n} (member : block ∈ execution.final.blocks) (marked : block.owner ∈ owners)
    {first second : Element n} (firstIn : first ∈ block.elements) (secondIn : second ∈ block.elements) :
    JunctionBendReduction.SameCutCell cuts first second := by
  intro cut cutMember
  let request : ArticleCutRequest n := ⟨block.owner, block.side, cut⟩
  have requested : request ∈ articleOwnerCuts owners cuts := (mem_articleOwnerCuts owners cuts request).mpr ⟨marked, cutMember⟩
  have clear := execution.cleared request requested block member rfl rfl
  change ¬ block.CrossesCut cut at clear
  constructor
  · intro firstLow
    by_contra secondNotLow
    exact clear ⟨first, firstIn, second, secondIn, firstLow, by omega⟩
  · intro secondLow
    by_contra firstNotLow
    exact clear ⟨second, secondIn, first, firstIn, secondLow, by omega⟩

end ArticleCutPreparation
end Splay.Accounting
