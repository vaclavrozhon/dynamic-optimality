import TangoSquared.Paper20261030.LocalPreferenceFlipController
import TangoSquared.Paper20261030.LocalClosedNeighborProgram
import TangoSquared.Paper20261030.DecompositionHeadRepair
import TangoSquared.Paper20261030.ExactSplitWords

/-! The actual head-flip controllers preserve the manuscript's preferred
path decomposition. Ordered separator words identify the read head
payload with its semantic record. Thus the local payload update changes
exactly the reference head and preserves both represented descendants. -/

namespace TangoSquared.Paper20261030.PathDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations SourceLocalProgram

variable {α ρ : Type*}

theorem left_head_controller (right : Record (β := fun _ => ρ) → Bool)
    (record : Record (β := fun _ => ρ)) (l r : Source α (Record (β := fun _ => ρ)))
    (lc rc c : AuxiliaryComponent α Nat (fun _ => ρ×Bool))
    (hl : Represents right l lc) (hr : Represents right r rc)
    (same : Equivalent c (append lc record.2.1 record.2.2 (closed rc)))
    (oldDirection : right record = false) (oldClean : entry record = false) (ordered : c.core.Ordered)
    (update : Nat → ρ → ρ)
    (newDirection : right (record.1,⟨record.2.1,(update record.2.1 record.2.2.1,false)⟩) = true) (outside) :
    ∃ d : AuxiliaryComponent α Nat (fun _ => ρ×Bool),
      Represents right (.fork (record.1,⟨record.2.1,(update record.2.1 record.2.2.1,false)⟩) l r) d ∧
      ∃ reads cost, Run (PreferenceFlipController.program record.2.1 true update) (.opening .start)
        ⟨closed c,outside⟩ .done ⟨closed d,outside⟩ reads cost ∧
        cost ≤ 40110*Nat.clog 2 (c.core.size+1)+2100*Nat.clog 2 (rc.core.size+1)+322 := by
  have endpoint : extreme true c.core = some record.2 := by
    rw [extreme_last,same.word,append_word]
    simp
  let found := extreme_found true c.core ordered endpoint
  have empty := maximum_split_empty c.core c.balanced ordered endpoint
  have old : Represents right (.fork record l r) c := .left oldDirection oldClean hl hr same
  obtain ⟨hc,hp⟩ := old.invariant
  obtain ⟨hrc,hrp⟩ := hr.invariant
  have recovered := max_left_equivalent c lc record.2.1 record.2.2 (closed rc) same found empty
  have representedLeft := hl.equivalent recovered
  have attached : c.ports c.core.size = closed rc := by
    rw [same.ports _ le_rfl,same.size,append_size]
    simp only [append,show ¬ lc.core.size+1 ≤ lc.core.size by omega,if_false]
  have word : c.core.toListModel = lc.core.toListModel ++ record.2 :: [] := by rw [same.word,append_word]
  have pivot := (splitAt_word_decomposition c.core c.balanced ordered lc.core.toListModel [] record.2 word found).2.1
  have payload : (splitAt record.2.1 c.core c.balanced found).value = record.2.2 := eq_of_heq (Sigma.mk.inj pivot).2
  let fresh := (update record.2.1 record.2.2.1,false)
  let d := preferRight c rc record.2.1 found fresh
  have represented : Represents right (.fork (record.1,⟨record.2.1,fresh⟩) l r) d :=
    .right newDirection rfl representedLeft hr (.refl _)
  have execution := PreferenceFlipController.prefer_right c rc hc hrc hp hrp
    (ClosedNeighborController.represented_terminal hr) record.2.1 found empty attached update outside
  simp only [payload] at execution
  exact ⟨d,represented,execution⟩

theorem right_head_controller (right : Record (β := fun _ => ρ) → Bool)
    (record : Record (β := fun _ => ρ)) (l r : Source α (Record (β := fun _ => ρ)))
    (lc rc c : AuxiliaryComponent α Nat (fun _ => ρ×Bool))
    (hl : Represents right l lc) (hr : Represents right r rc)
    (same : Equivalent c (prepend record.2.1 record.2.2 (closed lc) rc))
    (oldDirection : right record = true) (oldClean : entry record = false) (ordered : c.core.Ordered)
    (update : Nat → ρ → ρ)
    (newDirection : right (record.1,⟨record.2.1,(update record.2.1 record.2.2.1,false)⟩) = false) (outside) :
    ∃ d : AuxiliaryComponent α Nat (fun _ => ρ×Bool),
      Represents right (.fork (record.1,⟨record.2.1,(update record.2.1 record.2.2.1,false)⟩) l r) d ∧
      ∃ reads cost, Run (PreferenceFlipController.program record.2.1 false update) (.opening .start)
        ⟨closed c,outside⟩ .done ⟨closed d,outside⟩ reads cost ∧
        cost ≤ 40110*Nat.clog 2 (c.core.size+1)+2100*Nat.clog 2 (lc.core.size+1)+322 := by
  have endpoint : extreme false c.core = some record.2 := by
    rw [extreme_first,same.word,prepend_word]
    rfl
  let found := extreme_found false c.core ordered endpoint
  have empty := minimum_split_empty c.core c.balanced ordered endpoint
  have old : Represents right (.fork record l r) c := .right oldDirection oldClean hl hr same
  obtain ⟨hc,hp⟩ := old.invariant
  obtain ⟨hlc,hlp⟩ := hl.invariant
  have recovered := min_right_equivalent c rc record.2.1 record.2.2 (closed lc) same found empty
  have representedRight := hr.equivalent recovered
  have attached : c.ports 0 = closed lc := by
    rw [same.ports 0 (Nat.zero_le _)]
    simp only [prepend,if_true]
  have word : c.core.toListModel = [] ++ record.2 :: rc.core.toListModel := by rw [same.word,prepend_word]; rfl
  have pivot := (splitAt_word_decomposition c.core c.balanced ordered [] rc.core.toListModel record.2 word found).2.1
  have payload : (splitAt record.2.1 c.core c.balanced found).value = record.2.2 := eq_of_heq (Sigma.mk.inj pivot).2
  let fresh := (update record.2.1 record.2.2.1,false)
  let d := preferLeft lc c record.2.1 found fresh
  have represented : Represents right (.fork (record.1,⟨record.2.1,fresh⟩) l r) d :=
    .left newDirection rfl hl representedRight (.refl _)
  have execution := PreferenceFlipController.prefer_left lc c hlc hc hlp hp
    (ClosedNeighborController.represented_terminal hl) record.2.1 found empty attached update outside
  simp only [payload] at execution
  exact ⟨d,represented,execution⟩

end TangoSquared.Paper20261030.PathDecomposition
