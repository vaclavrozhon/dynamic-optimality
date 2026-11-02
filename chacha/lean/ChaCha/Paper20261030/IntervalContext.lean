import ChaCha.Paper20261030.SplitPortSlices
import ChaCha.Paper20261030.ContextPortWords
import ChaCha.Paper20261030.IntervalReplacement

/-!
# The physical middle split agrees with the preferred reference context

When the unchanged context has records on both sides, its last lower
record and first upper record are the two split boundaries. The actual
middle component is equivalent to the represented descendant. Replacing
it physically yields a component equivalent to rewrapping the replacement
in exactly the same preferred context, including every hanging port.
-/

namespace ChaCha.Paper20261030.PathDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations

variable {α : Type*} {β : Nat → Type*} {right : Record (β := β) → Bool}

theorem middle_context (c sub : AuxiliaryComponent α Nat (Tagged β))
    (frames : List (ContextFrame right)) (same : Equivalent c (PreferredContext.wrap sub frames))
    (ordered : c.core.Ordered) (before after : List (Sigma (Tagged β))) (lo hi : Sigma (Tagged β))
    (hb : PreferredContext.before frames = before ++ [lo])
    (ha : PreferredContext.after frames = hi :: after) :
    ∃ (fl : searchResult lo.1 c.core = true)
      (fh : searchResult hi.1 (cutRight c lo.1 fl).core = true),
      Equivalent (middle c lo.1 fl hi.1 fh) sub ∧
        ∀ fresh : AuxiliaryComponent α Nat (Tagged β),
          Equivalent (replaceMiddle c lo.1 fl hi.1 fh fresh) (PreferredContext.wrap fresh frames) := by
  have word : c.core.toListModel = before ++ lo :: (sub.core.toListModel ++ hi :: after) := by
    rw [same.word,PreferredContext.word,hb,ha]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  have ports : c.portWord = PreferredContext.beforePorts frames ++
      (sub.portWord ++ PreferredContext.afterPorts frames) := by
    rw [same.portWord,PreferredContext.portWord,List.append_assoc]
  have pLength : (PreferredContext.beforePorts frames).length = before.length + 1 := by
    rw [PreferredContext.beforePorts_length,hb,List.length_append,List.length_singleton]
  let fl := word_pivot_found c.core ordered before (sub.core.toListModel ++ hi :: after) lo word
  obtain ⟨hl,hlo,hr,hpl,hpr⟩ := split_slices c ordered before (sub.core.toListModel ++ hi :: after) lo
    (PreferredContext.beforePorts frames) (sub.portWord ++ PreferredContext.afterPorts frames)
    word ports pLength fl
  have rightOrdered := cutRight_ordered c ordered lo.1 fl
  let fh := word_pivot_found (cutRight c lo.1 fl).core rightOrdered sub.core.toListModel after hi hr
  have middleLength : sub.portWord.length = sub.core.toListModel.length + 1 := by
    rw [portWord_length,size_eq_length _ sub.balanced]
  obtain ⟨hm,hhi,hh,hpm,hph⟩ := split_slices (cutRight c lo.1 fl) rightOrdered
    sub.core.toListModel after hi sub.portWord (PreferredContext.afterPorts frames)
    hr hpr middleLength fh
  refine ⟨fl,fh,equivalent_of_words hm hpm,?_⟩
  intro fresh
  apply PreferredContext.equivalent_of_context_words
  · rw [replaceMiddle_word,hl,hlo,hhi,hh,hb,ha]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  · simp only [replaceMiddle,join_portWord,hpl,hph,List.append_assoc]

end ChaCha.Paper20261030.PathDecomposition
