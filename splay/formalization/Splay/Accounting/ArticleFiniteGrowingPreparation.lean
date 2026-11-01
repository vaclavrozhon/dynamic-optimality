import Splay.Accounting.ArticleInternalPairingExecution
import Splay.Lazy.ShrinkingSingletons
import Splay.Interface.OperationCounts

namespace Splay.Accounting

open Splay.Lazy

/-- Actual growing-slot preparation with a literal frame for every old
shrinking block. This frame is stronger than a zero-insert count. -/
structure ArticleFiniteGrowingPreparation {n : ℕ} (params : Interface.Parameters) (initial : Lazy.State n)
    (slots : List (Element n × Side)) where
  events : List (Event n)
  final : Lazy.State n
  trace : Trace params initial events final
  stable : final.Stable params
  view_eq : final.view = initial.view
  births : final.blocks.length ≤ initial.blocks.length + slots.length
  noInserts : Interface.totalInserts (eraseOperations events) = 0
  noIncreases : Interface.totalIncreases (eraseOperations events) = 0
  passRefines : initial.PassRefinement final
  empty : ∀ slot ∈ slots, ArticleGrowingEmptyAt final slot.1 slot.2
  preservesEmpty : ∀ owner side, ArticleGrowingEmptyAt initial owner side → ArticleGrowingEmptyAt final owner side
  shrinkingFrame : ∀ (id : Interface.BlockId) (block : Block n), initial.blocks[id]? = some block →
    block.mode = .shrinking → final.blocks[id]? = some block

namespace ArticleFiniteGrowingPreparation

theorem exists_one {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    (stable : initial.Stable params) (slot : Element n × Side) :
    Nonempty (ArticleFiniteGrowingPreparation params initial [slot]) := by
  obtain ⟨events, final, trace, births, noInserts, noIncreases, finalStable,
    viewEq, empty, preserves, frame, passRefines⟩ := exists_articleEmptyGrowingAtFramedRefinedTrace stable slot.1 slot.2
  refine ⟨{
    events := events
    final := final
    trace := trace
    stable := finalStable
    view_eq := viewEq
    births := by simpa using births
    noInserts := noInserts
    noIncreases := noIncreases
    passRefines := passRefines
    empty := ?_
    preservesEmpty := ?_
    shrinkingFrame := frame
  }⟩
  · intro queried member
    have equal := List.mem_singleton.mp member
    subst queried
    exact empty
  · intro owner side alreadyEmpty
    by_cases ownerEq : owner = slot.1
    · by_cases sideEq : side = slot.2
      · simpa [ownerEq, sideEq] using empty
      · exact preserves owner side (Or.inr sideEq) alreadyEmpty
    · exact preserves owner side (Or.inl ownerEq) alreadyEmpty

theorem exists_finite {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    (stable : initial.Stable params) (slots : List (Element n × Side)) :
    Nonempty (ArticleFiniteGrowingPreparation params initial slots) := by
  induction slots generalizing initial with
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
        passRefines := State.PassRefinement.refl initial
        empty := by simp
        preservesEmpty := fun _ _ empty => empty
        shrinkingFrame := fun _ _ found _ => found
      }⟩
  | cons slot slots ih =>
      obtain ⟨head⟩ := exists_one stable slot
      obtain ⟨tail⟩ := ih head.stable
      refine ⟨{
        events := head.events ++ tail.events
        final := tail.final
        trace := head.trace.append tail.trace
        stable := tail.stable
        view_eq := tail.view_eq.trans head.view_eq
        births := ?_
        noInserts := by rw [eraseOperations_append, Interface.totalInserts_append, head.noInserts, tail.noInserts]
        noIncreases := by rw [eraseOperations_append, Interface.totalIncreases_append, head.noIncreases, tail.noIncreases]
        passRefines := head.passRefines.trans tail.passRefines
        empty := ?_
        preservesEmpty := fun owner side empty => tail.preservesEmpty owner side (head.preservesEmpty owner side empty)
        shrinkingFrame := fun id block found shrinking =>
          tail.shrinkingFrame id block (head.shrinkingFrame id block found shrinking) shrinking
      }⟩
      · have headBound := head.births
        have tailBound := tail.births
        simp only [List.length_cons, List.length_nil] at headBound ⊢
        omega
      · intro queried member
        rcases List.mem_cons.mp member with equal | inTail
        · subst queried
          exact tail.preservesEmpty _ _ (head.empty slot (by simp))
        · exact tail.empty queried inTail

theorem singletons {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    {slots : List (Element n × Side)} (execution : ArticleFiniteGrowingPreparation params initial slots)
    (complete : initial.Complete) {selected : Finset (Element n)} (prepared : initial.ShrinkingSingletons selected) :
    execution.final.ShrinkingSingletons selected :=
  prepared.of_shrinking_frame complete execution.stable.1 execution.view_eq execution.shrinkingFrame

end ArticleFiniteGrowingPreparation

noncomputable def articleOwnerSlots {n : ℕ} (owners : Finset (Element n)) : List (Element n × Side) :=
  owners.toList.flatMap fun owner => [(owner, .left), (owner, .right)]

theorem articleOwnerSlots_length {n : ℕ} (owners : Finset (Element n)) :
    (articleOwnerSlots owners).length = 2 * owners.card := by
  have lengthFor : ∀ list : List (Element n),
      (list.flatMap fun owner => [(owner, Side.left), (owner, Side.right)]).length = 2 * list.length := by
    intro list
    induction list with
    | nil => simp
    | cons head tail ih => simp [ih]; omega
  simpa [articleOwnerSlots] using lengthFor owners.toList

theorem mem_articleOwnerSlots {n : ℕ} (owners : Finset (Element n)) (owner : Element n) (side : Side) :
    (owner, side) ∈ articleOwnerSlots owners ↔ owner ∈ owners := by
  classical
  cases side <;> simp [articleOwnerSlots]

theorem ArticleFiniteGrowingPreparation.ownerSlots_empty {n : ℕ} {params : Interface.Parameters}
    {initial : Lazy.State n} {owners : Finset (Element n)}
    (execution : ArticleFiniteGrowingPreparation params initial (articleOwnerSlots owners)) :
    ∀ block ∈ execution.final.blocks, block.mode = .growing → block.owner ∈ owners → block.elements = [] := by
  intro block member growing marked
  have empty := execution.empty (block.owner, block.side) ((mem_articleOwnerSlots owners block.owner block.side).mpr marked)
  obtain ⟨id, found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨lt, getEq⟩ := List.getElem?_eq_some_iff.mp found
  have result := empty ⟨id, lt⟩
  dsimp only at result
  rw [show execution.final.blocks.get ⟨id, lt⟩ = block from getEq] at result
  exact result growing rfl rfl

end Splay.Accounting
