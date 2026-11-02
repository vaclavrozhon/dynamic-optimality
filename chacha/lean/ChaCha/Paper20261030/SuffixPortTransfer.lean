import ChaCha.Paper20261030.SuffixDecomposition
import ChaCha.Paper20261030.ComponentPortWords

/-!
# Restricting a prepared decomposition retains the exact suffix ports

The root preferred path already ends at the sentinel. Restriction deletes
its left-going outlets and keeps every right-going outlet as the same
physical closed component. The resulting port word is the old word
starting at its actual terminal index. This is a representation theorem;
it does not rebuild or charge those retained subtrees.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open PreferredProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem suffixRepresentative_exists {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (terminal : (Secondary.decodeDepth reference p).terminal = d)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    ∃ suffix : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight (suffixSource reference p d valid) suffix ∧
      suffix.portWord = c.portWord.drop (terminalIndex followsRight (source reference p)) := by
  induction reference generalizing c with
  | leaf a =>
    have equal : a = d := by omega
    subst d
    exact ⟨c,represented,by simp [source,terminalIndex]⟩
  | @node a b cut ha hb l r ihl ihr =>
    cases bit : p ⟨a,cut,b⟩
    · have endpoint : (Secondary.decodeDepth l p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,Bool.false_eq_true,if_false] using terminal
      have bounds := (Secondary.decodeDepth_mem l p d).mp
        (by rw [← endpoint]; exact PrefRouter.terminal_mem _)
      obtain ⟨lc,rc,hl,hr,same⟩ := represented.left_view (by exact bit)
      obtain ⟨sl,hsl,ports⟩ := ihl bounds endpoint lc hl
      let out := append sl cut ((⟨a,cut,b⟩,p ⟨a,cut,b⟩),false) (closed rc)
      have outRep : Represents followsRight (suffixSource (.node cut ha hb l r) p d valid) out := by
        simp only [suffixSource,dif_pos bounds.2]
        exact .left bit rfl hsl hr (.refl _)
      refine ⟨out,outRep,?_⟩
      simp only [source,terminalIndex,followsRight,bit,Bool.false_eq_true,if_false]
      rw [same.portWord]
      simp only [out,append_portWord]
      have bound : terminalIndex followsRight (source l p) ≤ lc.portWord.length := by
        rw [portWord_length]
        have := hl.terminalIndex_bound
        omega
      rw [List.drop_append_of_le_length bound]
      rw [ports]
    · have endpoint : (Secondary.decodeDepth r p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,if_true] using terminal
      have bounds := (Secondary.decodeDepth_mem r p d).mp
        (by rw [← endpoint]; exact PrefRouter.terminal_mem _)
      have notLeft : ¬ d ≤ cut := by omega
      obtain ⟨lc,rc,hl,hr,same⟩ := represented.right_view (by exact bit)
      obtain ⟨sr,hsr,ports⟩ := ihr bounds endpoint rc hr
      refine ⟨sr,?_,?_⟩
      · simpa only [suffixSource,dif_neg notLeft] using hsr
      · simp only [source,terminalIndex,followsRight,bit,if_true]
        rw [same.portWord,prepend_portWord]
        simpa only [Nat.add_comm 1,List.drop_succ_cons] using ports

theorem suffixSource_minimum {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool) :
    suffixSource reference p a ⟨le_rfl,Secondary.reference_bounds reference⟩ = source reference p := by
  induction reference with
  | leaf => rfl
  | node cut ha hb l r ihl ihr =>
    simp only [suffixSource,dif_pos ha,source,ihl]

end ChaCha.Paper20261030.SecondaryDecomposition
