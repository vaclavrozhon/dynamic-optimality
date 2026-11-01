import Splay.Accounting.ArticleCutSplit

namespace Splay.Accounting

open Splay.Lazy

/-- One owner-side slot and one numerical cut to clear. -/
structure ArticleCutRequest (n : ℕ) where
  owner : Element n
  side : Side
  cut : ℕ

def ArticleCutRequest.Clear {n : ℕ} (request : ArticleCutRequest n) (state : Lazy.State n) : Prop :=
  ∀ block ∈ state.blocks, block.owner = request.owner → block.side = request.side → ¬ block.CrossesCut request.cut

/-- An actual sequence clearing a finite cut worklist. It only refines old
blocks and preserves every surviving growing block literally. -/
structure ArticleCutPreparation {n : ℕ} (params : Interface.Parameters) (initial : Lazy.State n)
    (requests : List (ArticleCutRequest n)) where
  events : List (Event n)
  final : Lazy.State n
  trace : Trace params initial events final
  stable : final.Stable params
  view_eq : final.view = initial.view
  births : final.blocks.length ≤ initial.blocks.length + 2 * requests.length
  noInserts : Interface.totalInserts (eraseOperations events) = 0
  noIncreases : Interface.totalIncreases (eraseOperations events) = 0
  refines : initial.BlockRefinement final
  passRefines : initial.PassRefinement final
  growing_preserved : ∀ block ∈ final.blocks, block.mode = .growing → block ∈ initial.blocks
  cleared : ∀ request ∈ requests, request.Clear final

namespace ArticleCutPreparation

theorem exists_one {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    (stable : initial.Stable params) (request : ArticleCutRequest n)
    (emptyGrowings : ∀ block ∈ initial.blocks, block.mode = .growing →
      block.owner = request.owner → block.elements = []) :
    Nonempty (ArticleCutPreparation params initial [request]) := by
  classical
  by_cases crossing : ∃ source ∈ initial.blocks,
      source.owner = request.owner ∧ source.side = request.side ∧ source.CrossesCut request.cut
  · obtain ⟨source, member, ownerEq, sideEq, crosses⟩ := crossing
    obtain ⟨sourceId, found⟩ := List.mem_iff_getElem?.mp member
    have shrinking : source.mode = .shrinking := by
      cases mode : source.mode with
      | shrinking => rfl
      | growing =>
          have empty := emptyGrowings source member mode ownerEq
          obtain ⟨low, lowIn, _, _, _, _⟩ := crosses
          simp [empty] at lowIn
    obtain ⟨execution⟩ := ArticleCutSplit.exists_of_crossing stable found shrinking request.cut crosses
    refine ⟨{
      events := execution.events
      final := execution.final
      trace := execution.trace
      stable := execution.stable
      view_eq := execution.view_eq
      births := by rw [execution.births]; simp
      noInserts := execution.noInserts
      noIncreases := execution.noIncreases
      refines := execution.refines found
      passRefines := execution.passRefines found
      growing_preserved := execution.growing_preserved found shrinking
      cleared := ?_
    }⟩
    intro queried inside
    have equal : queried = request := List.mem_singleton.mp inside
    subst queried
    intro block blockMember blockOwner blockSide
    exact execution.cleared block blockMember (blockOwner.trans ownerEq.symm) (blockSide.trans sideEq.symm)
  · refine ⟨{
      events := []
      final := initial
      trace := Trace.nil stable.1
      stable := stable
      view_eq := rfl
      births := by simp
      noInserts := rfl
      noIncreases := rfl
      refines := State.BlockRefinement.refl initial
      passRefines := State.PassRefinement.refl initial
      growing_preserved := fun _ member _ => member
      cleared := ?_
    }⟩
    intro queried inside
    have equal : queried = request := List.mem_singleton.mp inside
    subst queried
    intro block member ownerEq sideEq crosses
    exact crossing ⟨block, member, ownerEq, sideEq, crosses⟩

/-- All cuts are realized with at most one actual shrinking split per
worklist entry. Earlier cuts remain clear by sublist refinement. -/
theorem exists_of_emptyGrowings {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    (stable : initial.Stable params) (requests : List (ArticleCutRequest n))
    (emptyGrowings : ∀ request ∈ requests, ∀ block ∈ initial.blocks, block.mode = .growing →
      block.owner = request.owner → block.elements = []) :
    Nonempty (ArticleCutPreparation params initial requests) := by
  induction requests generalizing initial with
  | nil =>
      exact ⟨{
        events := []
        final := initial
        trace := Trace.nil stable.1
        stable := stable
        view_eq := rfl
        births := by simp
        noInserts := rfl
        noIncreases := rfl
        refines := State.BlockRefinement.refl initial
        passRefines := State.PassRefinement.refl initial
        growing_preserved := fun _ member _ => member
        cleared := by simp
      }⟩
  | cons request requests ih =>
      obtain ⟨head⟩ := exists_one stable request (emptyGrowings request (by simp))
      have remainingEmpty : ∀ next ∈ requests, ∀ block ∈ head.final.blocks, block.mode = .growing →
          block.owner = next.owner → block.elements = [] := by
        intro next member block blockMember growing ownerEq
        exact emptyGrowings next (by simp [member]) block (head.growing_preserved block blockMember growing) growing ownerEq
      obtain ⟨tail⟩ := ih head.stable remainingEmpty
      refine ⟨{
        events := head.events ++ tail.events
        final := tail.final
        trace := head.trace.append tail.trace
        stable := tail.stable
        view_eq := tail.view_eq.trans head.view_eq
        births := ?_
        noInserts := by rw [eraseOperations_append, Interface.totalInserts_append, head.noInserts, tail.noInserts]
        noIncreases := by rw [eraseOperations_append, Interface.totalIncreases_append, head.noIncreases, tail.noIncreases]
        refines := head.refines.trans tail.refines
        passRefines := head.passRefines.trans tail.passRefines
        growing_preserved := fun block member growing => head.growing_preserved block (tail.growing_preserved block member growing) growing
        cleared := ?_
      }⟩
      · have headBound := head.births
        have tailBound := tail.births
        simp only [List.length_cons, List.length_nil] at headBound ⊢
        omega
      · intro next member
        rcases List.mem_cons.mp member with equal | inTail
        · subst next
          exact tail.refines.preserves_clearCut request.owner request.side request.cut (head.cleared request (by simp))
        · exact tail.cleared next inTail

end ArticleCutPreparation
end Splay.Accounting
