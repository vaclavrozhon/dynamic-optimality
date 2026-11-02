import ChaCha.Paper20261030.SplayAuxiliaryDecomposition
import ChaCha.Paper20261030.SplicedSource
import ChaCha.Paper20261030.PreparedPathAgreement

/-!
# Persistent suffix transfer with ordinary splay auxiliaries

These are exact representation statements for the existing suffix and
splice of the reference memories. Every retained port is the same actual
subtree. The root auxiliary can have any shape; physical rotation costs
are supplied separately by the ordinary-splay implementation.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open PreferredProjection ColoredStorage SecondaryDecomposition RawComponent

/-- Physical separator identity, independent of reference preferences. -/
def cutKey (record : Cached) : Nat := record.2.1

namespace Decomposition

theorem Represents.terminalIndex_bound {key : Cached → Nat} {right : Cached → Bool}
    {reference : Source Nat Cached} {c : RawComponent Nat Nat}
    (represented : Represents key right reference c) :
    PathDecomposition.terminalIndex right reference ≤ c.core.size := by
  rw [represented.size]
  exact PathDecomposition.terminalIndex_bound right reference

end Decomposition

open Decomposition

theorem suffixRepresentative_exists {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (terminal : (Secondary.decodeDepth reference p).terminal = d)
    (c : RawComponent Nat Nat)
    (represented : Represents cutKey followsRight (source reference p) c) :
    ∃ suffix : RawComponent Nat Nat,
      Represents cutKey followsRight (suffixSource reference p d valid) suffix ∧
      suffix.portWord = c.portWord.drop (PathDecomposition.terminalIndex followsRight (source reference p)) := by
  induction reference generalizing c with
  | leaf a =>
    have equal : a = d := by omega
    subst d
    exact ⟨c,represented,by simp [source,PathDecomposition.terminalIndex]⟩
  | @node a b cut ha hb l r ihl ihr =>
    cases bit : p ⟨a,cut,b⟩
    · have endpoint : (Secondary.decodeDepth l p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,Bool.false_eq_true,if_false] using terminal
      have bounds := (Secondary.decodeDepth_mem l p d).mp
        (by rw [← endpoint]; exact PrefRouter.terminal_mem _)
      obtain ⟨lc,rc,hl,hr,same⟩ := represented.left_view (by exact bit)
      obtain ⟨sl,hsl,ports⟩ := ihl bounds endpoint lc hl
      let out := append sl cut (closed rc)
      have outRep : Represents cutKey followsRight (suffixSource (.node cut ha hb l r) p d valid) out := by
        simp only [suffixSource,dif_pos bounds.2]
        exact .left bit hsl hr (.refl _)
      refine ⟨out,outRep,?_⟩
      simp only [source,PathDecomposition.terminalIndex,followsRight,bit,Bool.false_eq_true,if_false]
      rw [same.portWord]
      simp only [out,append_portWord]
      have bound : PathDecomposition.terminalIndex followsRight (source l p) ≤ lc.portWord.length := by
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
      · simp only [source,PathDecomposition.terminalIndex,followsRight,bit,if_true]
        rw [same.portWord,prepend_portWord]
        simpa only [Nat.add_comm 1,List.drop_succ_cons] using ports


theorem splicedRepresentative_exists {a b : Nat} (reference : DepthTree a b)
    (p q : DepthSplit → Bool) (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = d)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = d)
    (active incoming : RawComponent Nat Nat)
    (activeRep : Represents cutKey followsRight (source reference p) active)
    (incomingRep : Represents cutKey followsRight (suffixSource reference q d valid) incoming) :
    ∃ out : RawComponent Nat Nat,
      Represents cutKey followsRight (splicedSource reference p q d valid) out ∧
      out.portWord = active.portWord.take (PathDecomposition.terminalIndex followsRight (source reference p)) ++
        incoming.portWord := by
  induction reference generalizing active incoming with
  | leaf a =>
    refine ⟨incoming,incomingRep,?_⟩
    simp only [source,PathDecomposition.terminalIndex,List.take_zero,List.nil_append]
  | @node a b cut ha hb l r ihl ihr =>
    have sameBit := (SeparatorPath.terminal_root_direction ha hb l r p d preparedP).trans
      (SeparatorPath.terminal_root_direction ha hb l r q d preparedQ).symm
    cases bit : p ⟨a,cut,b⟩
    · have qbit : q ⟨a,cut,b⟩ = false := sameBit.symm.trans bit
      have leftP : (Secondary.decodeDepth l p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,Bool.false_eq_true,if_false] using preparedP
      have leftQ : (Secondary.decodeDepth l q).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,qbit,Bool.false_eq_true,if_false] using preparedQ
      have bounds := (Secondary.decodeDepth_mem l p d).mp
        (by rw [← leftP]; exact PrefRouter.terminal_mem _)
      obtain ⟨al,ar,hal,har,activeSame⟩ := activeRep.left_view (by exact bit)
      simp only [suffixSource,dif_pos bounds.2] at incomingRep
      obtain ⟨il,ir,hil,hir,incomingSame⟩ := incomingRep.left_view (by exact qbit)
      obtain ⟨ol,hol,ports⟩ := ihl bounds leftP leftQ al il hal hil
      let out := append ol cut (closed ir)
      have represented : Represents cutKey followsRight (splicedSource (.node cut ha hb l r) p q d valid) out := by
        simp only [splicedSource,dif_pos bounds.2]
        exact .left bit hol hir (.refl _)
      refine ⟨out,represented,?_⟩
      simp only [source,PathDecomposition.terminalIndex,followsRight,bit,Bool.false_eq_true,if_false]
      rw [activeSame.portWord,incomingSame.portWord]
      simp only [out,append_portWord,ports]
      have bound : PathDecomposition.terminalIndex followsRight (source l p) ≤ al.portWord.length := by
        rw [portWord_length]
        have := hal.terminalIndex_bound
        omega
      rw [List.take_append_of_le_length bound,List.append_assoc]
    · have qbit : q ⟨a,cut,b⟩ = true := sameBit.symm.trans bit
      have rightP : (Secondary.decodeDepth r p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,if_true] using preparedP
      have rightQ : (Secondary.decodeDepth r q).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,qbit,if_true] using preparedQ
      have bounds := (Secondary.decodeDepth_mem r p d).mp
        (by rw [← rightP]; exact PrefRouter.terminal_mem _)
      have notLeft : ¬ d ≤ cut := by omega
      obtain ⟨al,ar,hal,har,activeSame⟩ := activeRep.right_view (by exact bit)
      simp only [suffixSource,dif_neg notLeft] at incomingRep
      obtain ⟨orep,horep,ports⟩ := ihr bounds rightP rightQ ar incoming har incomingRep
      let out := prepend cut (closed al) orep
      have represented : Represents cutKey followsRight (splicedSource (.node cut ha hb l r) p q d valid) out := by
        simp only [splicedSource,dif_neg notLeft]
        exact .right bit hal horep (.refl _)
      refine ⟨out,represented,?_⟩
      simp only [source,PathDecomposition.terminalIndex,followsRight,bit,if_true]
      rw [activeSame.portWord]
      simp only [out,prepend_portWord,ports,Nat.add_comm 1,List.take_succ_cons,List.cons_append]


end ChaCha.Paper20261030.SplayAuxiliary
