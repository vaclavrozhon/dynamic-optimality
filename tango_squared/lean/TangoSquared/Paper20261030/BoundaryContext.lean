import TangoSquared.Paper20261030.IntervalContext
import TangoSquared.Paper20261030.BoundaryReplacement

/-! Matching the one-boundary physical splits to the preferred context.
An empty outside record word also has an empty outside port word. -/

namespace TangoSquared.Paper20261030.PathDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations

variable {α : Type*} {β : Nat → Type*} {right : Record (β := β) → Bool}

theorem prefix_context (c sub : AuxiliaryComponent α Nat (Tagged β))
    (frames : List (ContextFrame right)) (same : Equivalent c (PreferredContext.wrap sub frames))
    (ordered : c.core.Ordered) (after : List (Sigma (Tagged β))) (hi : Sigma (Tagged β))
    (hb : PreferredContext.before frames = []) (ha : PreferredContext.after frames = hi :: after) :
    ∃ found : searchResult hi.1 c.core = true,
      Equivalent (cutLeft c hi.1 found) sub ∧
        ∀ fresh : AuxiliaryComponent α Nat (Tagged β),
          Equivalent (replacePrefix c hi.1 found fresh) (PreferredContext.wrap fresh frames) := by
  have emptyPorts : PreferredContext.beforePorts frames = [] := by
    apply List.length_eq_zero_iff.mp
    rw [PreferredContext.beforePorts_length,hb]
    rfl
  have word : c.core.toListModel = sub.core.toListModel ++ hi :: after := by
    rw [same.word,PreferredContext.word,hb,ha,List.nil_append]
  have ports : c.portWord = sub.portWord ++ PreferredContext.afterPorts frames := by
    rw [same.portWord,PreferredContext.portWord,emptyPorts,List.nil_append]
  let found := word_pivot_found c.core ordered sub.core.toListModel after hi word
  have pLength : sub.portWord.length = sub.core.toListModel.length + 1 := by
    rw [portWord_length,size_eq_length _ sub.balanced]
  obtain ⟨hl,hv,hr,hpl,hpr⟩ := split_slices c ordered sub.core.toListModel after hi
    sub.portWord (PreferredContext.afterPorts frames) word ports pLength found
  refine ⟨found,equivalent_of_words hl hpl,?_⟩
  intro fresh
  apply PreferredContext.equivalent_of_context_words
  · simp only [replacePrefix,join_word,hv,hr,hb,ha,List.nil_append]
  · simp only [replacePrefix,join_portWord,hpr,emptyPorts,List.nil_append]

theorem suffix_context (c sub : AuxiliaryComponent α Nat (Tagged β))
    (frames : List (ContextFrame right)) (same : Equivalent c (PreferredContext.wrap sub frames))
    (ordered : c.core.Ordered) (before : List (Sigma (Tagged β))) (lo : Sigma (Tagged β))
    (hb : PreferredContext.before frames = before ++ [lo]) (ha : PreferredContext.after frames = []) :
    ∃ found : searchResult lo.1 c.core = true,
      Equivalent (cutRight c lo.1 found) sub ∧
        ∀ fresh : AuxiliaryComponent α Nat (Tagged β),
          Equivalent (replaceSuffix c lo.1 found fresh) (PreferredContext.wrap fresh frames) := by
  have emptyPorts : PreferredContext.afterPorts frames = [] := by
    apply List.length_eq_zero_iff.mp
    rw [PreferredContext.afterPorts_length,ha]
    rfl
  have word : c.core.toListModel = before ++ lo :: sub.core.toListModel := by
    rw [same.word,PreferredContext.word,hb,ha]
    simp only [List.append_nil,List.append_assoc,List.singleton_append]
  have ports : c.portWord = PreferredContext.beforePorts frames ++ sub.portWord := by
    rw [same.portWord,PreferredContext.portWord,emptyPorts,List.append_nil]
  have pLength : (PreferredContext.beforePorts frames).length = before.length + 1 := by
    rw [PreferredContext.beforePorts_length,hb,List.length_append,List.length_singleton]
  let found := word_pivot_found c.core ordered before sub.core.toListModel lo word
  obtain ⟨hl,hv,hr,hpl,hpr⟩ := split_slices c ordered before sub.core.toListModel lo
    (PreferredContext.beforePorts frames) sub.portWord word ports pLength found
  refine ⟨found,equivalent_of_words hr hpr,?_⟩
  intro fresh
  apply PreferredContext.equivalent_of_context_words
  · simp only [replaceSuffix,join_word,hl,hv,hb,ha,List.append_nil,List.append_assoc,List.singleton_append]
  · simp only [replaceSuffix,join_portWord,hpl,emptyPorts,List.append_nil]

theorem empty_context (sub : AuxiliaryComponent α Nat (Tagged β))
    (frames : List (ContextFrame right))
    (hb : PreferredContext.before frames = []) (ha : PreferredContext.after frames = []) :
    Equivalent sub (PreferredContext.wrap sub frames) := by
  have bp : PreferredContext.beforePorts frames = [] := by
    apply List.length_eq_zero_iff.mp
    rw [PreferredContext.beforePorts_length,hb]
    rfl
  have ap : PreferredContext.afterPorts frames = [] := by
    apply List.length_eq_zero_iff.mp
    rw [PreferredContext.afterPorts_length,ha]
    rfl
  apply PreferredContext.equivalent_of_context_words
  · simp only [hb,ha,List.nil_append,List.append_nil]
  · simp only [bp,ap,List.nil_append,List.append_nil]

end TangoSquared.Paper20261030.PathDecomposition
