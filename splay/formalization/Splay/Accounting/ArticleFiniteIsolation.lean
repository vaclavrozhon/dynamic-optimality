import Splay.Accounting.ArticleInternalPairingExecution
import Splay.Lazy.ShrinkingSingletons
import Splay.Interface.OperationCounts

namespace Splay.Accounting

open Splay.Lazy

/-- Isolate a finite list using actual convert/split preparations. Existing
shrinking singleton elements stay isolated throughout the composition. -/
structure ArticleFiniteIsolation {n : ℕ} (params : Interface.Parameters) (initial : Lazy.State n)
    (selected : List (Element n)) where
  events : List (Event n)
  final : Lazy.State n
  trace : Trace params initial events final
  stable : final.Stable params
  view_eq : final.view = initial.view
  births : final.blocks.length ≤ initial.blocks.length + 5 * selected.length
  noInserts : Interface.totalInserts (eraseOperations events) = 0
  noIncreases : Interface.totalIncreases (eraseOperations events) = 0
  singletons : final.ShrinkingSingletons selected.toFinset
  passRefines : initial.PassRefinement final
  preserves : ∀ oldSelected, initial.ShrinkingSingletons oldSelected → final.ShrinkingSingletons oldSelected

namespace ArticleFiniteIsolation

theorem exists_one {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    (stable : initial.Stable params) (element : Element n) :
    Nonempty (ArticleFiniteIsolation params initial [element]) := by
  classical
  by_cases assigned : element ∈ initial.allElements
  · obtain ⟨source, member, inside⟩ := State.mem_allElements_iff.mp assigned
    obtain ⟨sourceId, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨before, after, decomposition⟩ := List.mem_iff_append.mp inside
    obtain ⟨events, final, singletonId, singletonBlock, trace, births, noInserts,
      noIncreases, finalStable, viewEq, singletonFound, mode, elements, _gap, _value, frame, passRefines⟩ :=
      exists_articlePrepareElementRefinedTrace stable found decomposition
    have prepared : final.ShrinkingSingletons [element].toFinset := by
      apply State.ShrinkingSingletons.of_residences finalStable.1
      intro queried marked _
      have equal : queried = element := by simpa using marked
      subst queried
      exact ⟨singletonId, singletonBlock, singletonFound, mode, elements⟩
    refine ⟨{
      events := events
      final := final
      trace := trace
      stable := finalStable
      view_eq := viewEq
      births := by simpa using births
      noInserts := noInserts
      noIncreases := noIncreases
      singletons := prepared
      passRefines := passRefines
      preserves := ?_
    }⟩
    intro oldSelected oldPrepared
    apply State.ShrinkingSingletons.of_residences finalStable.1
    intro queried marked queriedAssigned
    by_cases equal : queried = element
    · subst queried
      exact ⟨singletonId, singletonBlock, singletonFound, mode, elements⟩
    · have oldAssigned : queried ∈ initial.allElements := by
        apply (stable.2.1 queried).mpr
        rw [← viewEq]
        exact (finalStable.2.1 queried).mp queriedAssigned
      obtain ⟨oldBlock, oldMember, oldInside⟩ := State.mem_allElements_iff.mp oldAssigned
      obtain ⟨oldId, oldFound⟩ := List.mem_iff_getElem?.mp oldMember
      obtain ⟨oldMode, oldElements⟩ := oldPrepared queried marked oldBlock oldMember oldInside
      have different : oldId ≠ sourceId := by
        intro idsEqual
        subst oldId
        rw [found] at oldFound
        have blockEq := Option.some.inj oldFound
        have elementEquals : element = queried := by simpa [blockEq, oldElements] using inside
        exact equal elementEquals.symm
      exact ⟨oldId, oldBlock, frame oldId oldBlock oldFound different, oldMode, oldElements⟩
  · refine ⟨{
      events := []
      final := initial
      trace := Trace.nil stable.1
      stable := stable
      view_eq := rfl
      births := by simp
      noInserts := rfl
      noIncreases := rfl
      passRefines := State.PassRefinement.refl initial
      singletons := ?_
      preserves := fun _ prepared => prepared
    }⟩
    intro queried marked block member inside
    have equal : queried = element := by simpa using marked
    subst queried
    exact (assigned (State.mem_allElements_iff.mpr ⟨block, member, inside⟩)).elim

/-- Five block births per selected element suffice, even with repeated
elements or the actual heap root in the worklist. -/
theorem exists_finite {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    (stable : initial.Stable params) (selected : List (Element n)) :
    Nonempty (ArticleFiniteIsolation params initial selected) := by
  classical
  induction selected generalizing initial with
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
        singletons := by simp [State.ShrinkingSingletons]
        passRefines := State.PassRefinement.refl initial
        preserves := fun _ prepared => prepared
      }⟩
  | cons element selected ih =>
      obtain ⟨head⟩ := exists_one stable element
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
        singletons := ?_
        passRefines := head.passRefines.trans tail.passRefines
        preserves := fun oldSelected prepared => tail.preserves oldSelected (head.preserves oldSelected prepared)
      }⟩
      · have headBound := head.births
        have tailBound := tail.births
        simp only [List.length_cons, List.length_nil] at headBound ⊢
        omega
      · intro queried marked
        have cases : queried = element ∨ queried ∈ selected.toFinset := by simpa using marked
        rcases cases with equal | inTail
        · subst queried
          exact tail.preserves _ head.singletons element (by simp)
        · exact tail.singletons queried inTail

end ArticleFiniteIsolation
end Splay.Accounting
